
#include "defs.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

#include <fstream>
#include <map>
#include <algorithm>

#include <tr1/unordered_set>


external_module_t g_ext;
store_t           g_store;
int               g_verbose_level = 0;
deque<void(*)(int)> g_exit_callbacks;
deque<string>     g_xml_stack;

void algorithm::infer( logical_function_t *p_out_best_h, sparse_vector_t *p_out_fv, lp_inference_cache_t *p_out_cache, lp_inference_cache_t *p_old_cache, inference_configuration_t& c, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t& kb ) {

  p_out_cache->elapsed_prepare = getTimeofDaySec();
  c.timestart                  = getTimeofDaySec();

  if( !c.use_cache ) {
    
    V(1) cerr << "Generating potential hypothesis graph..." << endl;
    if( function::enumeratePotentialElementalHypotheses( &p_out_cache->pg, &p_out_cache->evc, obs, sexp_obs, kb, c ) ) {
      V(1) cerr << "done." << endl;
    
      V(1) cerr << "Converting the graph to LP optimization problem..." << endl;
      if( function::convertToLP( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, p_out_cache->evc, c ) ) {
      
        V(1) cerr << "done." << endl;

        unordered_map<string, int> name2index;

        repeat( j, p_out_cache->lp.variables.size() )
          name2index[ p_out_cache->lp.variables[j].name ] = j;
    
        for( unordered_map<string, double>::iterator iter_cache=c.sol_cache.begin(); c.sol_cache.end()!=iter_cache; ++iter_cache )
          p_out_cache->lp.variables[ name2index[ iter_cache->first ] ].setInitialValue( iter_cache->second );
      } else
        V(1) cerr << "Timeout." << endl;

    } else
      V(1) cerr << "Timeout." << endl;
    
  } else {
    for( uint_t i=0; i<p_out_cache->lp.variables.size(); i++ )
      p_out_cache->lp.variables[i].setInitialValue( p_out_cache->lp.variables[i].optimized );
    
  }
  
  function::adjustLP( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, p_out_cache->evc, c );
  
  p_out_cache->elapsed_prepare = getTimeofDaySec() - p_out_cache->elapsed_prepare;

  if( c.ilp ) cout << p_out_cache->lp.toString() << endl;
  
  if( p_out_cache->elapsed_prepare < c.timelimit ) {
    V(1) cerr << "Start inference with " << (BnB == c.method ? "BnB" : (c.method == CuttingPlaneBnB ? "BnB (with CPI)" : "LocalSearch")) << "..." << endl;

    /* Reset the time. */
    c.timestart = getTimeofDaySec();
    
    switch( c.method ) {
    case CuttingPlaneBnB:
    case BnB: { p_out_cache->lp.sol_type = function::solveLP_BnB( &p_out_cache->lp, &p_out_cache->lprel, c, p_out_cache ); break; }
#ifdef USE_LOCALSOLVER
    case LocalSearch: { p_out_cache->lp.sol_type = function::solveLP_LS( &p_out_cache->lp, c, p_out_cache ); break; }
#endif
    default: break;
    };
  
    if( c.ilp ) cout << p_out_cache->lp.solutionToString() << endl;

  } else p_out_cache->lp.sol_type = NotAvailable;

  function::convertLPToHypothesis( p_out_best_h, p_out_fv, p_out_cache->lp, p_out_cache->lprel, p_out_cache->evc, p_out_cache->pg );
  p_out_cache->loss.setLoss( c.training_instance, *p_out_best_h, p_out_cache->lp.optimized_obj );
  
}

void algorithm::learn( score_function_t *p_out_sfunc, const learn_configuration_t &c, const vector<training_data_t>& t, const knowledge_base_t& kb ) {

  unordered_map<string, int> num_diff;
  unordered_map<int, unordered_map<string, double> > sol_cache;
  
  for( int n=0; n<c.N; n++ ) {

    cerr << "Iteration: " << 1+n << endl;
    function::beginXMLtag( "learn-process", "iteration=\"" + toString(1+n, "%d") +"\"" );

    double total_updates = 0.0, total_loss = 0.0, minimum_loss = 0.0;

    for( uint_t i=0; i<t.size(); i++ ) {

      string log_head = "I=" + toString(n+1, "%d") + ": " + t[i].name + ": ";
      
      V(2)
        cerr << log_head << "  Input:  " << t[i].x.toString() << endl
             << log_head << "  Output: " << t[i].outputToString() << endl;
      else
        cerr << "." << endl;

      function::beginXMLtag( "training", "instance=\"" + t[i].name + "\"" );

      /* I) Predict! */
      function::beginXMLtag( "current-prediction", "" );
      
      /* arg max_{x_i, y^, h^}. */
      inference_configuration_t ci = c.ci;
      logical_function_t        h_current, h_correct;
      sparse_vector_t           v_current, v_correct;
      vector<const literal_t*>  y_literals;
      lp_inference_cache_t      cache( ci );
      double                    s_current, s_correct;

      t[i].y_lf.getAllLiterals( &y_literals );
      ci.training_instance = t[i];
      ci.objfunc           = LossAugmented;
      ci.sol_cache         = sol_cache[i];
        
      infer( &h_current, &v_current, &cache, NULL, ci, t[i].x, t[i].x_sexp, kb );
      s_current     = cache.lp.optimized_obj;
      total_loss   += cache.loss.loss;
      minimum_loss += cache.loss.minimum_loss;

      V(2) 
        cerr << log_head << "H:     " << h_current.toString() << endl
             << log_head << "C(H):  " << s_current << " + " << (cache.loss.maximum_loss - cache.loss.loss) << " == " << ci.p_sfunc->getScore( v_current ) << endl
             << log_head << "Class: " << (s_current < 0 ? "-1" : "+1") << endl
             << log_head << "Loss:  " << cache.loss.maximum_loss << " >= " << cache.loss.loss << " >= " << cache.loss.minimum_loss << endl;

      cache.printStatistics();
      if( ci.proofgraph ) cache.pg.printGraph( cache.lp, cache.lprel, "id=\"i"+ toString(1+n, "%d") +"pred\" type=\"Prediction\">" );
      
      function::endXMLtag( "current-prediction" );

      if( NotAvailable == cache.lp.sol_type ) {
        V(2) cerr << log_head << "Result of inference is not available." << endl;
        cout << "<update loss=\""+ toString( cache.loss.loss, "%f" ) +"\" coefficient=\"-\" />" << endl; function::endXMLtag( "training" );
        continue;
      }

      /* Caching the solution. */
      repeat( j, cache.lp.variables.size() )
        sol_cache[i][ cache.lp.variables[j].name ] = cache.lp.variables[j].optimized;
      
      ci.sol_cache         = sol_cache[i];
        
      if( cache.loss.minimum_loss == cache.loss.loss ) { cout << "<update loss=\"0\" coefficient=\"0\" />" << endl; function::endXMLtag( "training" ); continue; }

      if( Structure == t[i].type_output ) {

        /* I-2) Hiden variable completion! */
        
        /* arg max_{x_i, y_i, h} */
        function::beginXMLtag( "hidden-variable-completion", "" );
      
        lp_inference_cache_t another_cache( ci );
        ci.objfunc             = LabelGiven;
        //ci.method              = BnB;
        //ci.use_cache         = true;
        ci.initial_label_index = t[i].x.branches.size();

        logical_function_t       x_prime = t[i].x;
      
        for( uint_t j=0; j<y_literals.size(); j++ ) {
          if( !g_store.isNegative( y_literals[j]->predicate ) ) { x_prime.branches.push_back( *y_literals[j] ); }
        }
      
        infer( &h_correct, &v_correct, &another_cache, NULL, ci, x_prime, t[i].x_sexp, kb );
        s_correct = another_cache.lp.optimized_obj;

        for( uint_t j=0; j<another_cache.lp.variables.size(); j++ ) {
          if( 0 == another_cache.lp.variables[j].name.find( "fc_u_g_" ) ) s_correct -= another_cache.lp.variables[j].obj_val * another_cache.lp.variables[j].optimized;
        }

        V(2)
          cerr << log_head << "H':     " << h_correct.toString() << endl
               << log_head << "C(H'):  " << s_correct << " == " << ci.p_sfunc->getScore( v_correct ) << endl
               << log_head << "Loss:  " << another_cache.loss.maximum_loss << " >= " << another_cache.loss.loss << " >= " << another_cache.loss.minimum_loss << endl;

        s_current = ci.p_sfunc->getScore( v_current );
        s_correct = ci.p_sfunc->getScore( v_correct );
        
        another_cache.printStatistics();
        if( ci.proofgraph ) another_cache.pg.printGraph( another_cache.lp, another_cache.lprel, "id=\"i"+ toString(1+n, "%d") +"hvc\" type=\"HiddenVariableCompletion\">" );

        function::endXMLtag( "hidden-variable-completion" );

        /* TODO: Not updated if it is not good solution. */
        //if( s_current < s_correct ) {
        if( Optimal != another_cache.lp.sol_type ) {
          V(2) cerr << log_head << "Could not find good completion." << endl;
          cout << "<update loss=\""+ toString( cache.loss.loss, "%f" ) +"\" coefficient=\"-\" />" << endl; function::endXMLtag( "training" );
          continue;
        }
        
      }
      
      /* II) Update the weights! */
      double                numerator = 0.0, denominator = 0.0;
      unordered_set<string> feature_indices;

      switch( t[i].type_output ) {
      case Class:     numerator = -t[i].y_cls * cache.loss.loss; break;
      case Structure: numerator = s_current - s_correct + cache.loss.loss; V(2) cerr << log_head << "numerator = " << s_current << "-" << s_correct << "+" << cache.loss.loss << endl; break;
      }

      function::getVectorIndices( &feature_indices, v_current );
      function::getVectorIndices( &feature_indices, v_correct );

      for( unordered_set<string>::iterator iter_fi = feature_indices.begin(); feature_indices.end() != iter_fi; ++iter_fi ) {
        string j = *iter_fi;
        denominator += pow(v_correct[j] - v_current[j], 2);
      }

      double tau, TauTolerance = c.E * 0.1;

      if( TauTolerance > fabs(numerator) )   numerator = numerator >= 0 ? TauTolerance : -TauTolerance;
      
      if( 0.0 == denominator ) tau = 0.0;
      else tau                     = min( c.C, numerator / denominator ); // numerator / denominator; //2

      //tau = 0.5;
      cerr << log_head << "Update coefficient: " << tau << " = min(" << c.C << ", " << numerator << " / " << denominator << ")" << endl;

      function::beginXMLtag( "feature-vector", "" );
      foreach( unordered_set<string>, iter_fi, feature_indices )
        cout << "<update element=\""<< *iter_fi <<"\" log=\""<< (v_current[*iter_fi] != v_correct[*iter_fi] ? ::toString( 1+num_diff[*iter_fi]++, "*%d " ) : "") <<"\">"
             << v_current[*iter_fi] << " -> " << v_correct[*iter_fi] << "</update>" << endl;
      function::endXMLtag( "feature-vector" );      
      
      if( 0.0 == tau ) { cout << "<update loss=\"0\" coefficient=\""+ toString( cache.loss.loss, "%f" ) +"\" />" << endl; function::endXMLtag( "training" ); continue; }

      function::beginXMLtag( "update", "loss=\""+ toString( cache.loss.loss, "%f" ) + "\" coefficient=\"" + ::toString( tau, "%f" ) + "\"" );
      
      function::beginXMLtag( "loss", "" );
      cout << cache.loss.printVW() << endl;
      function::endXMLtag( "loss" );
      
      total_updates += fabs(tau);

      function::beginXMLtag( "model" );

      cout << "(model ";

      ostringstream log_weight_updates;
      
      for( unordered_set<string>::iterator iter_fi = feature_indices.begin(); feature_indices.end() != iter_fi; ++iter_fi ) {
        string j = *iter_fi;
        if( 0 != v_correct[j] - v_current[j] ) {

          V(3) 
            log_weight_updates << log_head << "Weight update: w_" << j << " <- " << p_out_sfunc->weights[j] + tau * (v_correct[j] - v_current[j]) << " = " << p_out_sfunc->weights[j] << " + " << tau * (v_correct[j] - v_current[j]) << endl;
        
          p_out_sfunc->weights[j] += tau * (v_correct[j] - v_current[j]);

        }

        if( 0 != p_out_sfunc->weights[j] )
          cout << "(weight \""<< j <<"\" "<< p_out_sfunc->weights[j] << ") ";
        
      }

      cout << ")" << endl;

      cerr << log_weight_updates.str() << endl;

      function::endXMLtag( "model" );

      function::endXMLtag( "update" );
      function::endXMLtag( "training" );
      
    }

    cerr << "# -- Total loss: " << total_loss << " (avg. = " << (total_loss / t.size()) << " / min. = " << minimum_loss << ")" << endl;
    cerr << "# -- Total update: " << total_updates << " (avg. = " << (total_updates / t.size()) << ")" << endl;

    function::endXMLtag( "learn-process" );
    
    if( 0.0 == total_updates || minimum_loss == total_loss ) {
      cerr << "# ... Ok, that's enough. "
           << "Henry terminated the training procedure in " << 1+n << "-th iteration." << endl;
      break;
    }
    
    cerr << " > " << c.E << endl << "# " << endl;
    
  }
  
}

bool _moduleProcessInput( vector<training_data_t>   *p_out_t,
                          score_function_t          *p_out_sfunc,
                          knowledge_base_t          *p_out_kb,
                          precompiled_kb_t          *p_out_pckb,
                          learn_configuration_t     *p_out_lc,
                          inference_configuration_t *p_out_ic,
                          command_option_t          &cmd, vector<string> &args ) {

  if( 0 == args.size() ) args.push_back( "-" );

  /* Read the precompiled knowledge base. */
  if( has_key( cmd, 'b' ) && NULL != p_out_kb ) {
    if( !function::readPrecompiledKB( p_out_kb, cmd[ 'b' ] ) ) {
      cerr << "ERROR: Could not read the precomplied knowledge base." << endl;
      return false;
    }
  }

  unordered_map<string, int> confusion_matrix;
  bool                       f_classified = false, f_structured = false, f_kb_modified = false;
    
  for( uint_t a=0; a<args.size(); a++ ) {
  
    /* Start interpreting the input. */
    istream                   *p_is = &cin;
    ifstream                   file;

    if( "-" != args[a] ) {
      file.open( args[a].c_str() );
      p_is = &file;

      if( file.fail() ) {
        cerr << "File not found: " << args[a] << endl;
        break;
      }
      
    }

    for( sexp_reader_t sr(*p_is); !sr.isEnd(); ++sr ) {
    
      if( sr.stack.isFunctor( "include" ) ) {
        vector<string> args_once( 1, sr.stack.children[1]->getString() );
        _moduleProcessInput( p_out_t, p_out_sfunc, p_out_kb, p_out_pckb, p_out_lc, p_out_ic, cmd, args_once );
      }

      if( sr.stack.isFunctor( "model" ) ) {
        for( uint_t i=1; i<sr.stack.children.size(); i++ ) {
          
          if( sr.stack.children[i]->isFunctor( "weight" ) ) {
            /* Set the model weights. */
            p_out_ic->ignore_weight = false;
        
            string index  = sr.stack.children[i]->children[1]->getString();
            double weight = atof( sr.stack.children[i]->children[2]->getString().c_str() );
            V(4) cerr << "Weight loaded: " << index << ":" << weight << endl;
            
            p_out_sfunc->weights[ index ] = weight;

          }
        }
      }
    
      if( sr.stack.isFunctor( "B" ) ) {
        if( has_key( cmd, 'b' ) ) continue;
          
        /* Identify the LF part. */
        int i_lf      = sr.stack.findFunctorArgument( ImplicationString );

        if( NULL != p_out_pckb ) {
          logical_function_t lf( *sr.stack.children[i_lf] );
          (*p_out_pckb)[ lf.branches[1].lit.predicate ][ lf.branches[1].lit.terms.size() ].push_back( sr.stack.toString() );
          f_kb_modified = true;
        }
      }

      if( sr.stack.isFunctor( "O" ) && NULL != p_out_ic ) {
        /* Compile the knowledge base. */
        if( !has_key( cmd, 'b' ) && (f_kb_modified || 0 == p_out_kb->axioms.size() ) ) {
          f_kb_modified = false;
          
          if( !function::compileKB( p_out_kb, *p_out_pckb ) ) {
            cerr << "ERROR: Knowledge compilation failed." << endl; continue;
          }
        }
        
        int
          i_x    = sr.stack.findFunctorArgument( AndString ), i_y    = sr.stack.findFunctorArgument( FnTrainingLabel ),
          i_name = sr.stack.findFunctorArgument( "name" ),    i_cls  = -1, i_structure = -1;

        if( -1 == i_x ) cerr << "Input not found." << endl;

        logical_function_t obs( *sr.stack.children[i_x] );
        training_data_t    td;
        
        if( -1 != i_y ) {
          i_cls = sr.stack.children[ i_y ]->findFunctorArgument( "class" );
          i_structure = sr.stack.children[ i_y ]->findFunctorArgument( "structure" );
          
          if( -1 != i_cls )
            td = training_data_t( obs,
                                atoi( sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString().c_str() ),
                                -1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "" );
            
          else
            td = training_data_t( obs,
                                logical_function_t( *sr.stack.children[ i_y ]->children[ i_structure ]->children[1] ),
                                -1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "" );
        }

        td.x_sexp = sr.stack.toString();
        
        /* For an example-specific training. */
        if( has_key( cmd, 'p' ) ) {
          if( -1 == i_name ) continue;
          if( sr.stack.children[i_name]->children[1]->getString() != cmd[ 'p' ] ) continue;
        }

        /* Learn or infer. */
        if( "learn" == cmd['m'] ) {
          
          /* Usage: (O (^ p1 p2 p3 ...) (output (class|structure (^ label)) ) ) */
          if( -1 == i_cls && -1 == i_structure ) { cerr << "Only supervised learning is supported." << endl; continue; }
        
          if( NULL != p_out_t ) p_out_t->push_back( td );

        } else if( "infer" == cmd['m'] ) {
        
          logical_function_t   best_h;
          lp_inference_cache_t cache( *p_out_ic );
          sparse_vector_t      v_current;
        
          cout << "<result-inference target=\"" << (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "") << "\">" << endl;

          p_out_ic->training_instance = td;
          
          function::enumerateConstatns( &p_out_kb->constants, obs );
          algorithm::infer( &best_h, &v_current, &cache, NULL, *p_out_ic, obs, sr.stack.toString(), *p_out_kb );
        
          /* Basic output. */
          vector<const literal_t*> literals_obs;
          obs.getAllLiterals( &literals_obs );

          cache.printStatistics();
          if( p_out_ic->proofgraph ) cache.pg.printGraph( cache.lp, cache.lprel );
        
          cout << "<observed size=\"" << literals_obs.size() << "\" domain_size=\"" << p_out_kb->constants.size() << "\">" << obs.toString() << "</observed>" << endl
               << "<hypothesis score=\"" << cache.lp.optimized_obj << "\">" << best_h.toString() << "</hypothesis>" << endl
               << "<vector>" << function::toString(v_current) << "</vector>" << endl;

          if( p_out_ic->show_variable_cluster ) {
            cout << "<variable-equivalence>" << endl;

            unordered_map<int, unordered_set<store_item_t> > var_cluster;
            for( unordered_map<store_item_t, int>::iterator iter_vc2v=cache.lprel.vc2v.begin(); cache.lprel.vc2v.end()!=iter_vc2v; ++iter_vc2v ) {
              var_cluster[ (int)cache.lp.variables[ iter_vc2v->second ].optimized ].insert( iter_vc2v->first );
            }
        
            for( unordered_map<int, unordered_set<store_item_t> >::iterator iter_vc=var_cluster.begin(); var_cluster.end()!=iter_vc; ++iter_vc )
              if( 0 != iter_vc->first ) cout << "<cluster id=\"" << iter_vc->first << "\">" << g_store.toString(iter_vc->second) << "</cluster>" << endl;

            cout << "</variable-equivalence>" << endl;
          }

          if( -1 != i_y ) {
            if( -1 != i_cls ) {
              confusion_matrix[ (cache.lp.optimized_obj >= 0 ? "+1" : "-1") + sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() ]++;
              f_classified = true;
              
              cout << "<task-result"
                   << " predicted-class=\""<< (cache.lp.optimized_obj >= 0 ? "+1" : "-1") << "\""
                   << " gold-class=\""<< sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() << "\""
                   << " loss=\""<< cache.loss.loss <<"\" />" << endl;
            } else {
              confusion_matrix[ 0.0 == cache.loss.loss ? "+1" : "-1" ]++;
              f_structured = true;
              
              cout << "<task-result"
                   << " gold-structure=\""<< logical_function_t( *sr.stack.children[ i_y ]->children[ i_structure ]->children[1] ).toString() << "\""
                   << " loss=\""<< cache.loss.loss <<"\" />" << endl;
            }
          }
          
          cout << "</result-inference>" << endl;

        }
        
      }
    
    }

    if( "-" != args[a] ) file.close();
    
  }

  if( f_structured ) {
    cout << "<performance><accuracy>"<< 100.0*confusion_matrix["+1"]/(confusion_matrix["+1"]+confusion_matrix["-1"]) <<"</accuracy>"
         << "<correct>"<< confusion_matrix["+1"] <<"</correct><incorrect>"<< confusion_matrix["-1"] <<"</incorrect></performance>" << endl;
  }
  
  if( f_classified ) {
    cout << "<performance>"
         << "<value system=\"+1\" gold=\"+1\">"<< confusion_matrix["+1+1"] <<"</value>" << endl
         << "<value system=\"+1\" gold=\"-1\">"<< confusion_matrix["+1-1"] <<"</value>" << endl
         << "<value system=\"-1\" gold=\"-1\">"<< confusion_matrix["-1-1"] <<"</value>" << endl
         << "<value system=\"-1\" gold=\"+1\">"<< confusion_matrix["-1+1"] <<"</value>" << endl
         << "</performance>" << endl;
  }

  return true;
  
}

bool _moduleCompileKb( command_option_t &cmd, vector<string> &args ) {

  precompiled_kb_t pckb;
  _moduleProcessInput( NULL, NULL, NULL, &pckb, NULL, NULL, cmd, args );

  if( !function::writePrecompiledKB( pckb, cmd[ 'o' ] ) ) {
    cerr << "ERROR: Precompilation failed." << endl;
  }
  
  return true;
  
}

bool _moduleProcessInferOptions( inference_configuration_t *p_out_con, command_option_t &cmd ) {
  
  if( !has_key( cmd, 'd' ) ) cmd[ 'd' ] = "9999";
  if( !has_key( cmd, 'c' ) ) cmd[ 'c' ] = "9999";
  if( !has_key( cmd, 'T' ) ) cmd[ 'T' ] = "9999";
  if( !has_key( cmd, 't' ) ) cmd[ 't' ] = "1";
  if( !has_key( cmd, 'O' ) ) cmd[ 'O' ] = "";
  if( !has_key( cmd, 'i' ) ) cmd[ 'i' ] = "bnb";

  p_out_con->max_variable_clusters = atoi( cmd[ 'c' ].c_str() );
  p_out_con->depthlimit            = atoi( cmd[ 'd' ].c_str() );
  p_out_con->timelimit             = atof( cmd[ 'T' ].c_str() );
  p_out_con->nbthreads             = atof( cmd[ 't' ].c_str() );
  p_out_con->extension_module      = cmd[ 'e' ];

  if( has_key( cmd, 'e' ) ) g_ext.initialize( p_out_con->extension_module );

  if( "ls" == cmd['i'] )  p_out_con->method       = LocalSearch;
  else if( "rlp" == cmd['i'] )  p_out_con->method = RoundLP;
  else if( "bnb" == cmd['i'] )  p_out_con->method = BnB;
  else if( "cpi" == cmd['i'] )  p_out_con->method = CuttingPlaneBnB;

  if( string::npos != cmd[ 'O' ].find( "proofgraph" ) ) p_out_con->proofgraph            = true;
  if( string::npos != cmd[ 'O' ].find( "ilp" ) )        p_out_con->ilp                   = true;
  if( string::npos != cmd[ 'O' ].find( "varcluster" ) ) p_out_con->show_variable_cluster = true;
  if( string::npos != cmd[ 'O' ].find( "stats" ) )      p_out_con->show_statistics       = true;

  if( atoi( cmd['v'].c_str() ) >= 2 ) p_out_con->is_ilp_verbose = true;

  return true;
  
}

bool _moduleInfer( command_option_t &cmd, vector<string> &args ) {

  score_function_t           sfunc;
  inference_configuration_t  c( sfunc );
  knowledge_base_t           kb;
  precompiled_kb_t           pckb;
  
  /* Setting the parameters. */
  c.ignore_weight = true;
  
  _moduleProcessInferOptions( &c, cmd );
  _moduleProcessInput( NULL, &sfunc, &kb, &pckb, NULL, &c, cmd, args );
  
  return true;
  
}

bool _moduleLearn( command_option_t &cmd, vector<string> &args ) {

  vector<training_data_t>  t;
  score_function_t         sfunc;
  knowledge_base_t         kb;
  precompiled_kb_t         pckb;
  learn_configuration_t    c( sfunc );

  /* Setting the parameters. */
  _moduleProcessInferOptions( &c.ci, cmd );

  if( !has_key( cmd, 'C' ) ) cmd[ 'C' ] = "1.0";
  if( !has_key( cmd, 'N' ) ) cmd[ 'N' ] = "9999";
  if( !has_key( cmd, 'E' ) ) cmd[ 'E' ] = "10e-05";
  
  c.method = OnlinePassiveAggressive;
  c.C      = atof(cmd['C'].c_str());
  c.N      = atoi(cmd['N'].c_str());
  c.E      = atof(cmd['E'].c_str());

  _moduleProcessInput( &t, &sfunc, &kb, &pckb, &c, &c.ci, cmd, args );

  /* Compile the knowledge base. */
  if( !has_key( cmd, 'b' ) && 0 == kb.axioms.size() )
    if( !function::compileKB( &kb, pckb ) ) {
      cerr << "ERROR: Knowledge compilation failed." << endl;
      return false;
    }
  
  algorithm::learn( &sfunc, c, t, kb );

  cout << "<model>" << endl
       << "(model ";
  for( weight_vector_t::iterator iter_fi = sfunc.weights.begin(); sfunc.weights.end() != iter_fi; ++iter_fi ) {
    if( 0.0 != iter_fi->second ) cout << "(weight \"" << iter_fi->first << "\" " << iter_fi->second << ") ";
  }

  cout << ")" << endl
       << "</model>" << endl;
  
  return true;
  
}

int main( int argc, char **pp_args ) {

  srand( time(NULL) );
  
  string exec_options;
  
  for( int i=1; i<argc; i++ ) exec_options += (1 != i ? " " : "") + string( pp_args[i] );
  
  if( 1 == argc ) { cerr << str_usage << endl; return 1; }

  command_option_t cmd;
  vector<string>   args;
  function::getParsedOption( &cmd, &args, "m:v:i:b:C:N:t:T:w:E:O:o:p:d:c:e:", argc, pp_args );

  if( !has_key( cmd, 'm' ) ) { cerr << str_usage << endl; return 1; }
  
  bool ret = false;
  
  cout << "<?xml version=\"1.0\" encoding=\"UTF-8\" ?>" << endl;

  function::beginXMLtag( "henry-output", "parameter=\"" + exec_options + "\"" );

  signal( SIGINT, function::catch_int );
  
  if( has_key( cmd, 'v' ) ) { g_verbose_level = atoi(cmd['v'].c_str()); }
  
  if( "compile_kb" == cmd['m'] ) {
    if( !has_key( cmd, 'o' ) ) { cerr << str_usage << endl; return 1; }
    ret = _moduleCompileKb( cmd, args );
  } else if( "infer" == cmd['m'] ) ret = _moduleInfer( cmd, args );
  else if( "learn" == cmd['m'] ) ret = _moduleLearn( cmd, args );

  g_ext.finalize();
  function::endXMLtag( "henry-output" );
  
  if( !ret ) { cerr << str_usage << endl; return 1; }
  
  return 0;
  
}
