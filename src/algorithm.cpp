
#include "defs.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <fstream>
#include <map>
#include <algorithm>

#include <tr1/unordered_set>

/* Instances. */
ofstream           g_out_file;
ostream           *g_p_out         = &cout;
external_module_t  g_ext;
store_t            g_store;
int                g_verbose_level = 0;
deque<void(*)(int)> g_exit_callbacks;
deque<string>      g_xml_stack;
list<list<PyObject*> > mypyobject_t::trash_cans;



inference_result_t algorithm::infer( logical_function_t *p_out_best_h, sparse_vector_t *p_out_fv, lp_inference_cache_t *p_out_cache, lp_inference_cache_t *p_old_cache, inference_configuration_t& c, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t& kb, bool f_learning, const weight_vector_t &w, ostream *p_out ) {

  inference_result_t ret = GenerationTimeout;
  p_out_cache->elapsed_prepare = getTimeofDaySec();
  c.timestart                  = getTimeofDaySec();

  if( !c.use_cache ) {
    
    V(1) cerr << TS() << "Generating potential hypothesis graph..." << endl;
    p_out_cache->pg.initializeDatabase();
    
    if( function::enumeratePotentialElementalHypotheses( &p_out_cache->pg, &p_out_cache->evc, obs, sexp_obs, kb, c ) ) {
    
      V(1) cerr << TS() << "Converting the graph to LP optimization problem..." << endl;
      if( function::convertToLP( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, p_out_cache->evc, c ) ) {

        unordered_map<string, int> name2index;

        repeat( j, p_out_cache->lp.variables.size() )
          name2index[ p_out_cache->lp.variables[j].name ] = j;
    
        for( unordered_map<string, double>::iterator iter_cache=c.sol_cache.begin(); c.sol_cache.end()!=iter_cache; ++iter_cache )
          p_out_cache->lp.variables[ name2index[ iter_cache->first ] ].setInitialValue( iter_cache->second );
      } else
        V(1) cerr << TS() << "Timeout." << endl;

    } else
      V(1) cerr << TS() << "Timeout." << endl;

    p_out_cache->pg.cleanUpDatabase();
    
  } else {
    for( uint_t i=0; i<p_out_cache->lp.variables.size(); i++ )
      p_out_cache->lp.variables[i].setInitialValue( p_out_cache->lp.variables[i].optimized );
    
  }
  
  function::adjustLP( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, p_out_cache->evc, c );
  
  p_out_cache->elapsed_prepare = getTimeofDaySec() - p_out_cache->elapsed_prepare;

  if( c.ilp ) (*g_p_out) << p_out_cache->lp.toString() << endl;
  
  if( p_out_cache->elapsed_prepare < c.timelimit ) {
    ret = ILPTimeout;
      
    V(1) cerr << TS() << "Start inference with " << (BnB == c.method ? "BnB" : (c.method == CuttingPlaneBnB ? "BnB (with CPI)" : "LocalSearch")) << "..." << endl;
    
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
  
    if( c.ilp ) (*g_p_out) << p_out_cache->lp.solutionToString() << endl;
    
    foreachc( pairwise_vars_t, iter_t1, p_out_cache->lprel.pp2v )
      for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
        if( 0.5 < p_out_cache->lp.variables[ iter_t2->second ].optimized )
          p_out_cache->lp.optimized_obj -= -0.0001;
      }

    if( p_out_cache->lp.sol_type == Optimal || p_out_cache->lp.sol_type == SubOptimal ) ret = Success;
    
  } else p_out_cache->lp.sol_type = NotAvailable;

  sparse_vector_t fv;
  function::convertLPToHypothesis( p_out_best_h, &fv, *p_out_cache );
  p_out_cache->loss.setLoss(c.training_instance, *p_out_best_h, p_out_cache->lprel, p_out_cache->lp.optimized_obj);
  p_out_cache->loss.minimum_loss = p_out_cache->loss.loss;

  if( NULL != p_out_fv ) (*p_out_fv) = fv;

  (*p_out) << "<observed size=\"" << obs.branches.size() << "\" domain_size=\"" << kb.constants.size() << "\">" << endl << obs.toString(c.isColoring()) << endl << "</observed>" << endl
           << "<hypothesis score=\"" << p_out_cache->lp.optimized_obj << "\">" << endl << p_out_best_h->toString(c.isColoring()) << endl << "</hypothesis>" << endl
           << "<vector score=\""<< score_function_t::getScore( w, fv ) <<"\">" << endl << function::toString(*p_out_fv, c.isColoring()) << endl << "</vector>" << endl;

  if( string::npos != c.output_info.find(OutputInfoFactors) ) {
    (*p_out) << "<score-function>" << endl;

    repeat( i, p_out_cache->lp.variables.size() ) {
      if(0 == p_out_cache->lp.variables[i].name.find("ufc_"))
        cout << toString(string::npos != c.output_info.find("colored") ?
                         "<factor name=\"\33[0;33m%s\33[0m\" value=\"\33[0;34m%f\33[0m\">%f</factor>" : "<factor name=\"%s\" value=\"%f\">%f</factor>",
                         p_out_cache->lp.variables[i].name.c_str(), p_out_cache->lp.variables[i].obj_val, p_out_cache->lp.variables[i].optimized) << endl;
    }
    
    (*p_out) << "</score-function>" << endl;
  }

  if(c.isAxiomOutput()) {
    (*p_out) << "<instantiated-axioms>" << endl;

    foreach(unordered_set<string>, i, p_out_cache->pg.instantiated_axioms)
      (*p_out) << "<axiom>" << *i << "</axiom>" << endl;
    
    (*p_out) << "</instantiated-axioms>" << endl;
  }

  if( g_ext.isFunctionDefined( "cbPostprocess" ) ) {
    (*p_out) << "<post-process>" << endl;
    mypyobject_t::buyTrashCan();

    external_module_context_t emc = {&p_out_cache->pg, NULL, &c};
    mypyobject_t pycon(PyCapsule_New( (void*)&emc, NULL, NULL));
    mypyobject_t pyarg(Py_BuildValue("(O)", pycon.p_pyobj));
    mypyobject_t pyret(g_ext.call( "cbPostprocess", pyarg.p_pyobj ));
    
    mypyobject_t::cleanTrashCan();
    (*p_out) << "</post-process>" << endl;
  }
  
  return ret;
}

void algorithm::learn( score_function_t *p_out_sfunc, const learn_configuration_t &c, vector<training_data_t>& t, const knowledge_base_t& kb ) {

  unordered_map<string, int> num_diff;
  unordered_map<string, int> gave_up_in_generation;
  
  repeat( n, c.N ) {

    cerr << TS() << "Iteration: " << 1+n << endl;
    function::beginXMLtag( "learn-process", "iteration=\"" + toString("%d", 1+n) +"\"" );

    double total_updates = 0.0, total_loss = 0.0, total_minimum_loss = 0.0; 
    g_store.cleanupUnknowns();

    /* Shuffle the training set. */
    random_shuffle( t.begin(), t.end() );
    
    /* Initialize the weights with the current weights. */
    int           num_progress = 0;
    int           num_actually_trained = 0;
    pid_t         forked_pid, child_pid;
    vector<pid_t> child_processes;

    repeat( s, c.S ) {

      forked_pid = fork();

      /* PARENT PROECSS JUST CREATES A CHILD PROCESS. */
      if( 0 != forked_pid ) {
        child_processes.push_back(forked_pid);
        continue;
      }

      /* START TRAINING. */
      child_pid = getpid();
      cerr << TS() << "fork(): " << child_pid << " from " << getpid() << endl;
      
      repeat( i, t.size() ) {
        if( s != i % c.S ) continue;
        
        stringstream ss;
        unordered_map<int, unordered_map<string, double> > sol_cache;
        
        num_progress++;
        
        string log_head = toString( "I=%d: S=%d/%d: P=%d/%d@%s (%.1f %%): ",  1+n, 1+s, c.S, 1+i, t.size(), t[i].name.c_str(), 100.0 * ((double)num_progress / t.size()) );
        
        cerr << endl;
        _N( " * Target: " << t[i].name << " / I="<< 1+n <<" / S=" << 1+s );

        if( 1 == gave_up_in_generation[t[i].name] ) {
          cerr << TS() << "Skipped because it failed in search space generation process before." << endl; continue;
        }
        
        _N( " * Current prediction" );
      
        function::beginXMLtag( "training", "instance=\"" + t[i].name + "\"", &ss );

        /* I) Predict! */
        function::beginXMLtag( "current-prediction", "gold-structure=\""+ t[i].y_lf.toString() +"\"", &ss );
      
        /* arg max_{x_i, y^, h^}. */
        inference_configuration_t ci    = c.ci;
        logical_function_t        h_current, h_correct;
        sparse_vector_t           v_current, v_correct;
        unordered_set<string>     feature_indices;      
        vector<const literal_t*>  y_literals;
        lp_inference_cache_t      cache( ci );
        double                    s_current, s_correct;
        double                    x_len = 0, xh_len = 0;

        t[i].y_lf.getAllLiterals( &y_literals );
        ci.training_instance      = t[i];
        ci.objfunc                = LossAugmented;
        ci.sol_cache              = sol_cache[i];
        ci.target_name            = t[i].name;
        
        inference_result_t ret = infer( &h_current, &v_current, &cache, NULL, ci, t[i].x, t[i].x_sexp, kb, true, p_out_sfunc->weights, &ss );

        if( GenerationTimeout == ret ) gave_up_in_generation[t[i].name] = 1;
        
        s_current     = cache.lp.optimized_obj;

        cache.printStatistics( &ss );
        if( ci.proofgraph ) cache.pg.printGraph( cache.lp, cache.lprel, "id=\"i"+ toString("%d", 1+n) +"pred\" type=\"Prediction\"", &ss );
      
        function::endXMLtag( "current-prediction", &ss );

        if( NotAvailable == cache.lp.sol_type ) {
          V(2) cerr << TS() << log_head << "Result of inference is not available." << endl;
          ss << "<update loss=\"0\" coefficient=\"-\" />" << endl;
          function::endXMLtag( "training", &ss );
          (*g_p_out) << ss.str() << endl;
          continue;
        }

        total_loss += cache.loss.loss;
        
        /* Caching the solution. */
        repeat( j, cache.lp.variables.size() )
          sol_cache[i][ cache.lp.variables[j].name ] = cache.lp.variables[j].optimized;
      
        ci.sol_cache         = sol_cache[i];
        
        if( 0.0 == cache.loss.loss ) {
          cerr << TS() << "No loss!" << endl;
          ss << "<update loss=\"0\" coefficient=\"0\" />" << endl;
          function::endXMLtag( "training", &ss );
          num_actually_trained++;
          (*g_p_out) << ss.str() << endl;
          continue; }

        if( Structure == t[i].type_output ) {

          /* I-2) Hiden variable completion! */
          cerr << endl;
          _N( " * Hidden variable completion" );
        
          /* arg max_{x_i, y_i, h} */
          function::beginXMLtag( "hidden-variable-completion", "", &ss );
      
          lp_inference_cache_t another_cache( ci );
          ci.objfunc             = LabelGiven;
          //ci.method            = BnB;
          //ci.use_cache         = true;
          ci.initial_label_index = t[i].x.branches.size();
          ci.target_name         = t[i].name;

          logical_function_t       x_prime = t[i].x;
      
          for( uint_t j=0; j<y_literals.size(); j++ ) {
            if( !g_store.isNegative( y_literals[j]->predicate ) ) { x_prime.branches.push_back( *y_literals[j] ); }
          }
        
          infer( &h_correct, &v_correct, &another_cache, NULL, ci, x_prime, t[i].x_sexp, kb, true, p_out_sfunc->weights, &ss );
          s_correct = another_cache.lp.optimized_obj;

          total_minimum_loss += another_cache.loss.loss;

          if( cache.loss.loss == another_cache.loss.loss ) {
            cerr << TS() << "Minimum loss reached." << endl;
            ss << toString("<update loss=\"%f\" coefficient=\"0\" />", cache.loss.loss) << endl;
            function::endXMLtag( "training", &ss );
            (*g_p_out) << ss.str() << endl;
            num_actually_trained++;
            continue; }

          variable_cluster_t vc_sys, vc_gold;
          foreachc( pairwise_vars_t, iter_t1, cache.lprel.pp2v )
            for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
              if( true || 0.5 < cache.lp.variables[iter_t2->second].optimized ) x_len += 1;
            }

          foreachc( pairwise_vars_t, iter_t1, another_cache.lprel.pp2v )
            for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
              if( true || 0.5 < another_cache.lp.variables[iter_t2->second].optimized ) xh_len += 1;
            }

          /* Create a weighted difference vector. */
          // sparse_vector_t v_weighted_current, v_weighted_correct;
          // function::convertLPToHypothesis( &h_current, &v_weighted_current, cache, true );
          // function::convertLPToHypothesis( &h_correct, &v_weighted_correct, another_cache, true );

          // v_current = v_weighted_current;
          // v_correct = v_weighted_correct;
          
	  // xh_len = x_len;

          s_current = score_function_t::getScore( p_out_sfunc->weights, v_current );
          s_correct = score_function_t::getScore( p_out_sfunc->weights, v_correct );
          xh_len = 0; x_len = 0;
          
          // x_len  = s_current+s_correct;
          // xh_len = s_current+s_correct;
          
          //xh_len += another_cache.pg.nodes.size();
          
          function::getVectorIndices( &feature_indices, v_correct );
          function::getVectorIndices( &feature_indices, v_current );

          for( unordered_set<string>::iterator iter_fi = feature_indices.begin(); feature_indices.end() != iter_fi; ++iter_fi ) {
            if( 1.0 < xh_len ) v_correct[*iter_fi] *= 1.0 / xh_len;
            if( 1.0 < x_len ) v_current[*iter_fi] *= 1.0 / x_len;
          }

          /* Re-calculate ;-) */
          double s_org_current = s_current; s_current = score_function_t::getScore( p_out_sfunc->weights, v_current );
          double s_org_correct = s_correct; s_correct = score_function_t::getScore( p_out_sfunc->weights, v_correct );
          
          another_cache.printStatistics( &ss );
          if( ci.proofgraph ) another_cache.pg.printGraph( another_cache.lp, another_cache.lprel, "id=\"i"+ toString("%d", 1+n) +"hvc\" type=\"HiddenVariableCompletion\"", &ss );

          function::endXMLtag( "hidden-variable-completion", &ss );

          /* TODO: Not updated if it is not good solution. */
          if( NotAvailable == another_cache.lp.sol_type || s_org_current < s_org_correct ) {
            V(2) cerr << TS() << log_head << toString("Could not find a better completion. (HVC: %f > CURR: %f)", s_org_correct, s_org_current) << endl;
            ss << "<update loss=\""+ toString( "%f", cache.loss.loss ) +"\" coefficient=\"-\" />" << endl; function::endXMLtag( "training", &ss );
            (*g_p_out) << ss.str() << endl;            
            continue;
          }
        
        }
      
        /* II) Update the weights! */
        double                numerator = 0.0, denominator = 0.0;

        switch( t[i].type_output ) {
        case Class:     numerator = -t[i].y_cls * cache.loss.loss; break;
        case Structure: numerator = s_current - s_correct + cache.loss.loss;  break;
        }
        
        for( unordered_set<string>::iterator iter_fi = feature_indices.begin(); feature_indices.end() != iter_fi; ++iter_fi ) {
          string j = *iter_fi;
          denominator += pow(v_correct[j] - v_current[j], 2);
        }

        double tau, TauTolerance = c.E * 0.1;

        if(TauTolerance > fabs(numerator))   numerator = numerator >= 0 ? TauTolerance : -TauTolerance;

        ss << toString("<update-coefficient numerator=\"%f\" denominator=\"%f\" />", numerator, denominator) << endl;
        
        if(0.0 == denominator) tau = 0.0;
        else                   tau = min( c.C, numerator / denominator );

        function::beginXMLtag( "feature-vector-diff", "", &ss );

        foreach( unordered_set<string>, iter_fi, feature_indices )
          ss << " <element name=\""<< *iter_fi <<"\" log=\""<< (v_current[*iter_fi] != v_correct[*iter_fi] ? ::toString( "*%d ", 1+num_diff[*iter_fi]++ ) : "") << "\" diff=\"" << v_correct[*iter_fi] - v_current[*iter_fi] << "\">"
             << v_current[*iter_fi] << " -> " << v_correct[*iter_fi] << "</element>" << endl;
        
        function::endXMLtag( "feature-vector-diff", &ss );      
      
        function::beginXMLtag( "update", toString("loss=\"%f\" coefficient=\"%f\" vector-diff=\"%f\">", cache.loss.loss, tau, denominator), &ss );
      
        function::beginXMLtag( "loss", "", &ss );
        ss << cache.loss.printVW() << endl;
        function::endXMLtag( "loss", &ss );

        total_updates += fabs(tau);

        function::beginXMLtag( "weight-vector", "", &ss );
        for( unordered_set<string>::iterator iter_fi = feature_indices.begin(); feature_indices.end() != iter_fi; ++iter_fi ) {
          string j = *iter_fi;
          if(0 == j.find(PrefixFixedWeight)) continue; /* Fixed weight. */
          if(0 != v_correct[j] - v_current[j]) {
            ss << toString("<element name=\"%s\">%f -> %f</element>", j.c_str(), p_out_sfunc->weights[j], p_out_sfunc->weights[j] + tau * (v_correct[j] - v_current[j])) << endl;
            p_out_sfunc->weights[j] += tau * (v_correct[j] - v_current[j]);
          }
        }
        function::endXMLtag( "weight-vector", &ss );

        num_actually_trained++;
        
        /* Check-sum. */
        double s_new_current = 0.0, s_new_correct = 0.0;
        
        for( weight_vector_t::iterator iter_fi = p_out_sfunc->weights.begin(); p_out_sfunc->weights.end() != iter_fi; ++iter_fi ) {
          s_new_current += iter_fi->second * v_current[iter_fi->first];
          s_new_correct += iter_fi->second * v_correct[iter_fi->first];
        }

        ss << toString("<check-sum old-current=\"%f\" new-current=\"%f\" old-correct=\"%f\" new-correct=\"%f\" diff=\"%f\" />", s_current, s_new_current, s_correct, s_new_correct, s_new_correct - s_new_current) << endl;
        
        function::beginXMLtag( "model", "", &ss );

        ss << "(model ";
        for( weight_vector_t::iterator iter_fi = p_out_sfunc->weights.begin(); p_out_sfunc->weights.end() != iter_fi; ++iter_fi ) {
          if( 0.0 != iter_fi->second ) ss << "(weight \"" << iter_fi->first << "\" " << iter_fi->second << ") ";
        }
        ss << ")" << endl;

        function::endXMLtag( "model", &ss );

        function::endXMLtag( "update", &ss );
        function::endXMLtag( "training", &ss );

        (*g_p_out) << ss.str() << endl;
        
      }

      break;
            
    }

    /* CHILD:  WRITE THE RESULTS TO THE FILE, AND JUST BREAK. */
    if( 0 == forked_pid ) {
      cerr << TS() << "fork() = " << child_pid << " will exit." << endl;

      /* WRITE THE TRAINED WEIGHTS. */
      ofstream ofs(toString("./w-fork-%d.tmp", child_pid).c_str(), ofstream::out);

      /* HEADERS. */
      ofs << num_actually_trained << "\t" << total_loss << "\t" << total_updates << endl;

      /* WEIGHT VECTOR. */
      for( weight_vector_t::iterator iter_fi = p_out_sfunc->weights.begin(); p_out_sfunc->weights.end() != iter_fi; ++iter_fi ) {
        if( 0.0 != iter_fi->second ) ofs << iter_fi->first << "\t" << iter_fi->second << endl;
      }

      ofs << "_END_\t0.0" << endl;

      /* GAVE_UP_IN_GENERATION. */
      for( unordered_map<string,int>::iterator iter_gug=gave_up_in_generation.begin(); gave_up_in_generation.end()!=iter_gug; ++iter_gug)
        if( 1 == iter_gug->second ) ofs << iter_gug->first << endl;
      
      ofs.close();
      g_ext.finalize();
      exit(0);
    }

    /* PARENT: WAIT FOR ALL THE PROCESSES TO END, AND MERGE THE RESULTS. */
    vector<pair<weight_vector_t,double> > results;
    pid_t ret;
      
    while((ret = waitpid(-1, NULL, WNOHANG)) >= 0) {
      if( 0 == ret ) continue;
      cerr << TS() << "Welcome home, " << ret << "." << endl;

      ifstream        ifs(toString("./w-fork-%d.tmp", ret).c_str());
      string          name, local_gug;; double value, local_loss, local_updates;
      int             local_num_trained;
      weight_vector_t weights;

      ifs >> local_num_trained >> local_loss >> local_updates;
      num_actually_trained += local_num_trained;
      total_loss           += local_loss;
      total_updates        += local_updates;
        
      while( ifs >> name >> value && "_END_" != name )
        weights[ name ] = value;

      results.push_back( make_pair(weights, (double)local_num_trained) );

      while( ifs >> local_gug )
        gave_up_in_generation[local_gug] = 1;
      
      ifs.close();
      remove(toString("./w-fork-%d.tmp", ret).c_str());
    }

    p_out_sfunc->weights = weight_vector_t();
    
    repeat( i, results.size() )
      for( weight_vector_t::iterator iter_fi = results[i].first.begin(); results[i].first.end() != iter_fi; ++iter_fi ) {
        if(0 == iter_fi->first.find(PrefixFixedWeight)) p_out_sfunc->weights[iter_fi->first] = 1;
        else                                            p_out_sfunc->weights[iter_fi->first] += (results[i].second/num_actually_trained) * iter_fi->second;
      }
    
    /* OUTPUT THE CURRENT MODEL. */
    function::beginXMLtag( "model" );
    (*g_p_out) << "(model ";
    for( weight_vector_t::iterator iter_fi = p_out_sfunc->weights.begin(); p_out_sfunc->weights.end() != iter_fi; ++iter_fi ) {
      if( 0.0 != iter_fi->second ) (*g_p_out) << "(weight \"" << iter_fi->first << "\" " << iter_fi->second << ") ";
    }
    
    (*g_p_out) << ")" << endl;
    function::endXMLtag( "model" );

    cerr << TS() << "# -- Total loss: " << total_loss << " (avg. = " << (total_loss / t.size()) << ")" << endl;
    cerr << TS() << "# -- Total update: " << total_updates << " (avg. = " << (total_updates / t.size()) << ")" << endl;

    cout << toString("<total-update total-loss=\"%f\" minimum-loss=\"%f\" averaged-loss=\"%f\" averaged-update=\"%f\" />", total_loss, total_minimum_loss, total_loss/t.size(), total_updates/t.size()) << endl;
    
    function::endXMLtag( "learn-process" );
    
    if( 0.0 == total_updates || total_minimum_loss == total_loss ) {
      cerr << TS() << "# ... Ok, that's enough. "
           << "Henry terminated the training procedure in " << 1+n << "-th iteration." << endl;
      break;
    }
    
    cerr << " > " << c.E << endl << "# " << endl;
    
  }
  
}

#define _SYNCHK(x, s, e) _A(x, "Syntax error at line " << s.n_line << ":" << e << endl << s.stack.toString());

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
      E( "Could not read the precomplied knowledge base.");
      return false;
    }
  }

  unordered_map<string, int> confusion_matrix;
  bool                       f_classified = false, f_structured = false, f_kb_modified = false, f_p_found = false;
    
  for( uint_t a=0; a<args.size(); a++ ) {
    /* Start interpreting the input. */
    istream                   *p_is = &cin;
    ifstream                   file;

    if( "-" != args[a] ) {
      file.open( args[a].c_str() );
      p_is = &file;

      if( file.fail() ) {
        E( "File not found: " << args[a] );
        break;
      }
      
    }

    sexp_reader_t sr(*p_is);
    
    for( ; !sr.isEnd(); ++sr ) {
    
      if( sr.stack.isFunctor( "include" ) ) {
        _SYNCHK(StringStack == sr.stack.children[1]->type, sr, "what is included should be a string.");
        
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
            V(4) cerr << TS() << "Weight loaded: " << index << ":" << weight << endl;
            
            p_out_sfunc->weights[ index ] = weight;

          }
        }
      }
    
      if( sr.stack.isFunctor( "B" ) ) {
        if( has_key( cmd, 'b' ) ) continue;

        /* Identify the LF part. */
        int i_lf = sr.stack.findFunctorArgument( ImplicationString ),
          i_inc = sr.stack.findFunctorArgument( IncString );
        
        _SYNCHK(-1 != i_lf || -1 != i_inc, sr, "no logical connectors found.");

        if(-1 != i_lf) {
          _SYNCHK(sr.stack.children[i_lf]->children.size() == 3, sr, "function '=>' takes two arguments. ");
        } else if(-1 != i_inc) {
          _SYNCHK(sr.stack.children[i_inc]->children.size() == 3, sr, "function '_|_' takes two arguments. ");
        }
        
        if( NULL != p_out_pckb ) {
          logical_function_t lf( *sr.stack.children[-1 != i_lf ? i_lf : i_inc] );

          if(-1 != i_inc) {
            _SYNCHK(Literal == lf.branches[0].opr && Literal == lf.branches[1].opr, sr, "function '_|_' takes two literals. ");
          }
          
          if( Literal == lf.branches[1].opr ) {
            (*p_out_pckb)[ lf.branches[1].lit.predicate ][ lf.branches[1].lit.terms.size() ].push_back( sr.stack.toString() );
            f_kb_modified = true;
          } else if( AndOperator == lf.branches[1].opr ) {
            (*p_out_pckb)[ lf.branches[1].branches[0].lit.predicate ][ lf.branches[1].branches[0].lit.terms.size() ].push_back( sr.stack.toString() );
            f_kb_modified = true;
          } else {
            _SYNCHK(false, sr, "unsupported logical forms.");
          }
        }
      }

      if( sr.stack.isFunctor( "O" ) && NULL != p_out_ic ) {
        
        /* Compile the knowledge base. */
        if( !has_key( cmd, 'b' ) && (f_kb_modified || 0 == p_out_kb->axioms.size() ) ) {
          f_kb_modified = false;
          
          if( !function::compileKB( p_out_kb, *p_out_pckb ) ) {
            E( "ERROR: Knowledge compilation failed." ); continue;
          }
        }
        
        int
          i_x    = sr.stack.findFunctorArgument( AndString ), i_y    = sr.stack.findFunctorArgument( FnTrainingLabel ),
          i_name = sr.stack.findFunctorArgument( "name" ),    i_cls  = -1, i_structure = -1;
        
        string the_name = toString( "%s::%s", (string::npos != args[a].rfind("/") ? args[a].substr(args[a].rfind("/")+1) : args[a]).c_str(), (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?").c_str() );

        if( -1 == i_x ) { W( "Input not found:" << the_name ); continue; }

        logical_function_t obs( *sr.stack.children[i_x] );
        training_data_t    td;
        
        if( -1 != i_y ) {
          i_cls = sr.stack.children[ i_y ]->findFunctorArgument( "class" );
          i_structure = sr.stack.children[ i_y ]->findFunctorArgument( AndString );
          
          if( -1 != i_cls )
            td = training_data_t( obs,
                                atoi( sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString().c_str() ),
                                the_name );
            
          else if( -1 != i_structure )
            td = training_data_t( obs,
                                logical_function_t( *sr.stack.children[ i_y ]->children[ i_structure ] ),
                                the_name );
          else
            { W( "Label empty: " << the_name ); i_y = -1; i_structure = -1; }
            
        }

        td.x_sexp = sr.stack.toString();
        
        /* For an example-specific training. */
        if( has_key( cmd, 'p' ) ) {
          if( -1 == i_name ) continue;
          if( sr.stack.children[i_name]->children[1]->getString() != cmd[ 'p' ] ) continue;
          f_p_found = true;
        }

        /* Learn or infer. */
        if( "learn" == cmd['m'] ) {
          
          /* Usage: (O (^ p1 p2 p3 ...) (output (class|structure (^ label)) ) ) */
          if( -1 == i_cls && -1 == i_structure ) { W( "Label not found: " << the_name << " ... only supervised learning is supported." ); continue; }
        
          if( NULL != p_out_t ) p_out_t->push_back( td );

        } else if( "infer" == cmd['m'] ) {
          
          cerr << endl;
          _N( " * Target: " << the_name );
          
          logical_function_t   best_h;
          lp_inference_cache_t cache( *p_out_ic );
          sparse_vector_t      v_current;

          (*g_p_out) << "<result-inference target=\"" << (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "") << "\">" << endl;

          p_out_ic->target_name       = the_name;
          p_out_ic->training_instance = td;
          
          function::enumerateConstatns( &p_out_kb->constants, obs );
          algorithm::infer( &best_h, &v_current, &cache, NULL, *p_out_ic, obs, sr.stack.toString(), *p_out_kb, false, p_out_sfunc->weights );
        
          /* Basic output. */
          vector<const literal_t*> literals_obs;
          obs.getAllLiterals( &literals_obs );

          cache.printStatistics();
          if( p_out_ic->proofgraph ) cache.pg.printGraph( cache.lp, cache.lprel );
        
          if( p_out_ic->show_variable_cluster ) {
            (*g_p_out) << "<variable-equivalence>" << endl;

            unordered_map<int, unordered_set<store_item_t> > var_cluster;
            for( unordered_map<store_item_t, int>::iterator iter_vc2v=cache.lprel.vc2v.begin(); cache.lprel.vc2v.end()!=iter_vc2v; ++iter_vc2v ) {
              var_cluster[ (int)cache.lp.variables[ iter_vc2v->second ].optimized ].insert( iter_vc2v->first );
            }
        
            for( unordered_map<int, unordered_set<store_item_t> >::iterator iter_vc=var_cluster.begin(); var_cluster.end()!=iter_vc; ++iter_vc )
              if( 0 != iter_vc->first ) (*g_p_out) << "<cluster id=\"" << iter_vc->first << "\">" << g_store.toString(iter_vc->second) << "</cluster>" << endl;

            (*g_p_out) << "</variable-equivalence>" << endl;
          }

          if( -1 != i_y ) {
            if( -1 != i_cls ) {
              confusion_matrix[ (cache.lp.optimized_obj >= 0 ? "+1" : "-1") + sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() ]++;
              f_classified = true;
              
              (*g_p_out) << "<task-result"
                   << " predicted-class=\""<< (cache.lp.optimized_obj >= 0 ? "+1" : "-1") << "\""
                   << " gold-class=\""<< sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() << "\""
                   << " loss=\""<< cache.loss.loss <<"\" />" << endl;
            } else {
              confusion_matrix[ 0.0 == cache.loss.loss ? "+1" : "-1" ]++;
              f_structured = true;
              
              (*g_p_out) << "<task-result"
                   << " gold-structure=\""<< logical_function_t( *sr.stack.children[ i_y ]->children[ i_structure ] ).toString() << "\""
                   << " loss=\""<< cache.loss.loss <<"\" />" << endl;
            }
          }
          
          (*g_p_out) << "</result-inference>" << endl;

        }
        
      }
    
    }

    if( "-" != args[a] ) file.close();

    _A(sr.getQueue().size() == 2, "Syntax error: too few parentheses.");
  }

  if( f_structured ) {
    (*g_p_out) << "<performance><accuracy>"<< 100.0*confusion_matrix["+1"]/(confusion_matrix["+1"]+confusion_matrix["-1"]) <<"</accuracy>"
         << "<correct>"<< confusion_matrix["+1"] <<"</correct><incorrect>"<< confusion_matrix["-1"] <<"</incorrect></performance>" << endl;
  }
  
  if( f_classified ) {
    (*g_p_out) << "<performance>"
         << "<value system=\"+1\" gold=\"+1\">"<< confusion_matrix["+1+1"] <<"</value>" << endl
         << "<value system=\"+1\" gold=\"-1\">"<< confusion_matrix["+1-1"] <<"</value>" << endl
         << "<value system=\"-1\" gold=\"-1\">"<< confusion_matrix["-1-1"] <<"</value>" << endl
         << "<value system=\"-1\" gold=\"+1\">"<< confusion_matrix["-1+1"] <<"</value>" << endl
         << "</performance>" << endl;
  }

  if( has_key( cmd, 'p' ) && !f_p_found ) E( "Problem not found:" << cmd['p'] );
  
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
  if( !has_key( cmd, 'T' ) ) cmd[ 'T' ] = "9999";
  if( !has_key( cmd, 't' ) ) cmd[ 't' ] = "1";
  if( !has_key( cmd, 'O' ) ) cmd[ 'O' ] = "";
  if( !has_key( cmd, 'i' ) ) cmd[ 'i' ] = "bnb";
  if( !has_key( cmd, 'k' ) ) cmd[ 'k' ] = "1";
  if( !has_key( cmd, 'c' ) ) cmd[ 'c' ] = "wa";

  p_out_con->depthlimit            = atoi( cmd[ 'd' ].c_str() );
  p_out_con->timelimit             = atof( cmd[ 'T' ].c_str() );
  p_out_con->nbthreads             = atof( cmd[ 't' ].c_str() );
  p_out_con->extension_module      = cmd[ 'e' ];
  p_out_con->k_best                = atoi(cmd[ 'k' ].c_str());

  if(has_key(cmd, 'X')) {
    p_out_con->prohibited_literals.insert(atoi(cmd['X'].c_str()));
  }
  
  if( has_key( cmd, 'e' ) ) {
    g_ext.filename = p_out_con->extension_module;
    g_ext.args     = cmd[ 'f' ];
  }
    
  if( "ls" == cmd['i'] )  p_out_con->method       = LocalSearch;
  else if( "rlp" == cmd['i'] )  p_out_con->method = RoundLP;
  else if( "bnb" == cmd['i'] )  p_out_con->method = BnB;
  else if( "cpi" == cmd['i'] )  p_out_con->method = CuttingPlaneBnB;

  if( "wa" == cmd['c'] ) p_out_con->p_sfunc->tp = WeightedAbduction;
  else                   p_out_con->p_sfunc->tp = UserDefined;

  if( string::npos != cmd[ 'O' ].find( "proofgraph" ) ) p_out_con->proofgraph            = true;
  if( string::npos != cmd[ 'O' ].find( "ilp" ) )        p_out_con->ilp                   = true;
  if( string::npos != cmd[ 'O' ].find( "varcluster" ) ) p_out_con->show_variable_cluster = true;
  if( string::npos != cmd[ 'O' ].find( "stats" ) )      p_out_con->show_statistics       = true;

  p_out_con->output_info = cmd[ 'O' ];

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
  if( !has_key( cmd, 'S' ) ) cmd[ 'S' ] = "1";
  if( !has_key( cmd, 'N' ) ) cmd[ 'N' ] = "9999";
  if( !has_key( cmd, 'E' ) ) cmd[ 'E' ] = "10e-05";
  
  c.method = OnlinePassiveAggressive;
  c.C      = atof(cmd['C'].c_str());
  c.N      = atoi(cmd['N'].c_str());
  c.S      = atoi(cmd['S'].c_str());
  c.E      = atof(cmd['E'].c_str());

  _moduleProcessInput( &t, &sfunc, &kb, &pckb, &c, &c.ci, cmd, args );

  /* Compile the knowledge base. */
  if( !has_key( cmd, 'b' ) && 0 == kb.axioms.size() )
    if( !function::compileKB( &kb, pckb ) ) {
      E( "Knowledge compilation failed." );
      return false;
    }

  
  algorithm::learn( &sfunc, c, t, kb );

  (*g_p_out) << "<model>" << endl
       << "(model ";
  for( weight_vector_t::iterator iter_fi = sfunc.weights.begin(); sfunc.weights.end() != iter_fi; ++iter_fi ) {
    if( 0.0 != iter_fi->second ) (*g_p_out) << "(weight \"" << iter_fi->first << "\" " << iter_fi->second << ") ";
  }

  (*g_p_out) << ")" << endl
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
  function::getParsedOption( &cmd, &args, "m:v:i:b:C:N:t:T:w:E:O:o:p:d:c:e:f:k:S:X:", argc, pp_args );

  if( !has_key( cmd, 'm' ) ) { cerr << str_usage << endl; return 1; }
  
  bool ret = false;

  /* GLOBAL OPTION: -o */
  if( has_key( cmd, 'o' ) && "compile_kb" != cmd['m'] ) {
    g_out_file.open( cmd['o'].c_str() );
    g_p_out = &g_out_file;

    if( g_out_file.fail() ) {
      E( "File not found: " << cmd['o'] );
      return false;
    }
  }

  (*g_p_out) << "<?xml version=\"1.0\" encoding=\"UTF-8\" ?>" << endl;

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

  if( has_key( cmd, 'o' ) ) g_out_file.close();
  
  if( !ret ) { cerr << str_usage << endl; return 1; }
  
  return 0;
  
}
