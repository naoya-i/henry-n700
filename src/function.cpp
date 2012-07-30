#include "defs.h"

#include <time.h>
#include <stdlib.h>
#include <math.h>

#include <fstream>
#include <algorithm>
#include <map>

#include "darts.h"

using namespace function;


bool g_f_weighted_abduction = false;

bool function::enumeratePotentialElementalHypotheses( proof_graph_t *p_out_pg, variable_cluster_t *p_out_evc, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t &kb, const inference_configuration_t &c ) {

  vector<int>              nodes_obs;
  vector<const literal_t*> literals;
  obs.getAllLiterals( &literals );

  for( uint_t i=0; i<literals.size(); i++ ) {
    if( c.isTimeout() ) return false;
    
    int n_obs = p_out_pg->addNode( *literals[i], LabelGiven != c.objfunc || i < c.initial_label_index ? ObservableNode : LabelNode );

    p_out_pg->nodes[ n_obs ].parent_node           = -1;
    p_out_pg->nodes[ n_obs ].obs_node              = n_obs;
    p_out_pg->nodes[ n_obs ].instantiated_by.axiom = sexp_obs;
    p_out_pg->nodes[ n_obs ].instantiated_by.where = i;
    nodes_obs.push_back( n_obs );

    V(4) cerr << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << literals[i]->toString() << endl;
    
    if( ObservableNode != p_out_pg->nodes[ n_obs ].type ) continue;
    
    if( !instantiateBackwardChainings( p_out_pg, p_out_evc, n_obs, kb, c ) ) return false;
    
  }

  p_out_pg->addHyperNode( nodes_obs );

  return true;
  
}

bool function::instantiateBackwardChainings( proof_graph_t *p_out_pg, variable_cluster_t *p_out_evc, int n_obs, const knowledge_base_t &kb, const inference_configuration_t &c ) {

  if( p_out_pg->nodes[ n_obs ].depth > (signed)c.depthlimit-1 ) return true;
  
  int unifiable_axioms;
  if( 0 == kb.da.size() ) return true;
  kb.da.exactMatchSearch( p_out_pg->nodes[ n_obs ].lit.toPredicateArity().c_str(), unifiable_axioms );

  if( -1 == unifiable_axioms ) return true;
  if( c.isTimeout() ) return false;
  
  /* For each unifiable axiom, */
  istringstream iss_axiom_set( kb.axioms[ unifiable_axioms ] );
  string        axiom;
  string        log_head = "";

  /* Log: indicate the path to observation! */
  vector<string> path_to_obs;
  int parent_node = n_obs;
  while( -1 != parent_node ) {
    path_to_obs.push_back( p_out_pg->nodes[ parent_node ].lit.toString() );
    parent_node = p_out_pg->nodes[ parent_node ].parent_node;
  }

  log_head = ::join( path_to_obs.rbegin(), path_to_obs.rend(), ": " ) + ": ";

  unordered_set<string> applied_axioms;
  
  while( getline( iss_axiom_set, axiom, '\t' ) ) {

    istringstream iss_axiom( axiom );
    V(5) cerr << log_head << "instantiate: " << axiom << " for " << endl;
    p_out_pg->instantiated_axioms.insert( axiom );

    for( sexp_reader_t sr(iss_axiom); !sr.isEnd(); ++sr ) {

      if( !sr.stack.isFunctor( "B" ) ) continue;
        
      int i_lf = sr.stack.findFunctorArgument( ImplicationString );
      
      /* For each clause that has the literal n_obs in its right-hand side, */
      logical_function_t lf( *sr.stack.children[i_lf] );
      string             axiom_str = lf.toString();

      if( applied_axioms.end() != applied_axioms.find(axiom_str) ) continue;
      applied_axioms.insert( axiom_str );
      
      V(5) cerr << axiom_str << " in " << ::join( p_out_pg->nodes[ n_obs ].axiom_used.begin(), p_out_pg->nodes[ n_obs ].axiom_used.end(), "/" ) << "?" << endl;

      if( p_out_pg->nodes[ n_obs ].axiom_used.end() != p_out_pg->nodes[ n_obs ].axiom_used.find( axiom_str ) ) {
        V(5) cerr << log_head << "Loopy!" << endl;
        continue; /* That's loopy axiom. */
      }
      
      /* Produce substitution. */
      unifier_t theta;
      if( !getMGU( &theta, lf.branches[1].lit, p_out_pg->nodes[ n_obs ].lit ) ) continue;
        
      /* For each literal, */
      vector<literal_t> lhs_literals;

      if( Literal == lf.branches[0].opr )
        lhs_literals.push_back( lf.branches[0].lit );
      else {
        for( uint_t j=0; j<lf.branches[0].branches.size(); j++ )
          lhs_literals.push_back( lf.branches[0].branches[j].lit );
      }

      /* Check if this lhs matches the condition stated by the given label. */
      if( LabelGiven == c.objfunc ) {
        bool f_prohibited = false;
        
        //cerr << c.training_instance.y_lf.toString() << endl;
        repeat( j, c.training_instance.y_lf.branches.size() ) {
          if( NotOperator != c.training_instance.y_lf.branches[j].opr ) continue;

          repeat( k, lhs_literals.size() ) {
            if( c.training_instance.y_lf.branches[j].branches[0].lit.predicate == lhs_literals[k].predicate ) { f_prohibited = true; break; }
          }
        }

        if( f_prohibited ) continue;
      }

      /* Perform backward-chaining. */
      vector<int> backchained_literals;
        
      for( uint_t j=0; j<lhs_literals.size(); j++ ) {

        literal_t &lit = lhs_literals[j];

        /* Issue unknown variables */
        for( uint_t k=0; k<lit.terms.size(); k++ )
          if( !theta.isApplied( lit.terms[k] ) ) theta.add( lit.terms[k], g_store.issueUnknown() );
          
        theta.apply( &lit );

        int         n_backchained;

        /* If the completely same node is found, then recycle it. */
        vector<int> recycles;

        if( p_out_pg->getNode( &recycles, lit ) ) {
          
          n_backchained = recycles[0];
          p_out_pg->nodes[ n_backchained ].axiom_used.insert( p_out_pg->nodes[ n_obs ].axiom_used.begin(), p_out_pg->nodes[ n_obs ].axiom_used.end() );
          p_out_pg->nodes[ n_backchained ].axiom_used.insert( axiom_str );
          p_out_pg->nodes[ n_backchained ].nodes_appeared.insert( n_obs );
          
        } else {
          
          n_backchained = p_out_pg->addNode( lit, HypothesisNode );
        
          /* Set the node parameters. */
          p_out_pg->nodes[ n_backchained ].depth                 = p_out_pg->nodes[ n_obs ].depth + 1;
          p_out_pg->nodes[ n_backchained ].obs_node              = p_out_pg->nodes[ n_obs ].obs_node;
          p_out_pg->nodes[ n_backchained ].parent_node           = n_obs;
          p_out_pg->nodes[ n_backchained ].instantiated_by.axiom = axiom;
          p_out_pg->nodes[ n_backchained ].instantiated_by.where = j;
          p_out_pg->nodes[ n_backchained ].axiom_used.insert( p_out_pg->nodes[ n_obs ].axiom_used.begin(), p_out_pg->nodes[ n_obs ].axiom_used.end() );
          p_out_pg->nodes[ n_backchained ].axiom_used.insert( axiom_str );
          p_out_pg->nodes[ n_backchained ].nodes_appeared.insert( n_obs );
          p_out_pg->nodes[ n_backchained ].lit.wa_number        *= p_out_pg->nodes[ n_obs ].lit.wa_number;

          V(5) cerr << log_head << "new Literal: " << p_out_pg->nodes[ n_backchained ].lit.toString() << endl;
          
          /* Perform further backward-inference on the back-chained literal. */
          if( !g_f_weighted_abduction || (g_f_weighted_abduction && 0.0 < p_out_pg->nodes[ n_backchained ].lit.wa_number) )
            if( !instantiateBackwardChainings( p_out_pg, p_out_evc, n_backchained, kb, c ) ) return false;
            
        }
          
        backchained_literals.push_back( n_backchained );
        
      }

      if( backchained_literals.size() > 0 ) {
        pg_hypernode_t hn = p_out_pg->addHyperNode( backchained_literals );
        p_out_pg->addEdge( n_obs, hn );
      }
        
    }
    
  }

  return true;
  
}

inline int _getCorefVar( store_item_t t1, store_item_t t2, const lp_problem_mapping_t &lprel ) {
  store_item_t t1s = t1, t2s = t2; if( t1s > t2s ) swap( t1s, t2s );
    
  pairwise_vars_t::const_iterator k1 = lprel.pp2v.find(t1s);
  if( lprel.pp2v.end() == k1 ) return -1;

  unordered_map<store_item_t, int>::const_iterator k2 = k1->second.find(t2s);
  return k1->second.end() == k2 ? -1 : k2->second;
}

int _createCorefVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, store_item_t t1, store_item_t t2, bool f_create_new = true) {

  if( t1 > t2 ) swap(t1, t2);
  
  if( f_create_new ) p_out_cache->evc.add( t1, t2 );
  
  /* Skip the pair of logical terms if the following conditions hold:
     1. These two do not involve any unifiability of atoms;
     2. Both are constants;
     3. They do not belong to the same potential equivalent cluster;
     *4. One of them are not observed.
  */
  if( t1 == t2 ) return -1;
  if( g_store.isConstant(t1) && g_store.isConstant(t2) ) return -1;
  
  variable_cluster_t::variable_mapper_t::iterator i_v1 = p_out_cache->evc.map_v2c.find(t1);
  if( p_out_cache->evc.map_v2c.end() == i_v1 ) return -1;
  
  variable_cluster_t::variable_mapper_t::iterator i_v2 = p_out_cache->evc.map_v2c.find(t2);
  if( p_out_cache->evc.map_v2c.end() == i_v2 ) return -1;
  
  if( i_v1->second != i_v2->second ) return -1;
  
  int& ret = t1 < t2 ? p_out_lprel->pp2v[t1][t2] : p_out_lprel->pp2v[t2][t1];
  if( 0 == ret ) { ret = p_out_lp->addVariable( lp_variable_t( "p_"+g_store.claim(t1)+g_store.claim(t2) ) ); p_out_lp->variables[ ret ].obj_val = -0.0001; }
  
  return ret;
}

inline int _createNodeVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, const proof_graph_t &pg, int n ) {
  int& v_h = p_out_lprel->n2v[n];
  if( 0 != v_h ) return v_h;
  
  v_h = p_out_lp->addVariable( lp_variable_t( "h_" + pg.nodes[n].lit.toString() ) );
  
  if( ObservableNode == pg.nodes[n].type || LabelNode == pg.nodes[n].type ) p_out_lp->variables[ v_h ].fixValue( 1.0 );

  return v_h;
}

/* and_{1,2,3} <=> h_i ^ h_c1 ^ h_c2 ^ ... ^ h_c3. */
inline int _createConjVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, const proof_graph_t &pg, int n, int hn ) {
  int& v_hn = p_out_lprel->hn2v[hn];
  if( 0 != v_hn ) return v_hn;

  char buffer[1024]; sprintf( buffer, "and_%d", hn );
  v_hn = p_out_lp->addVariable( lp_variable_t( string( buffer ) ) );

  /* and_{1,2,3} <=> h_i ^ h_c1 ^ h_c2 ^ ... ^ h_c3. */
  lp_constraint_t con( "and", Range, 0, 1 );
  con.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, n ), 1.0 );
  repeat( j, pg.hypernodes[ hn ].size() )
    con.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, pg.hypernodes[ hn ][j] ), 1.0 );
  con.rhs = 1.0 * con.vars.size() - 1;
  con.push_back( v_hn, -1.0 * con.vars.size() );
  p_out_lp->addConstraint( con );

  /* h_c1 ^ h_c2 ^ ... h_cn => h_i */
  lp_constraint_t con_imp( "imp", LessEqual, 0.0 );
  repeat( i, pg.hypernodes[ hn ].size() )
    con_imp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, pg.hypernodes[ hn ][i] ), 1.0 );
  con_imp.rhs = 1.0 * con_imp.vars.size() - 1.0;
  con_imp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, n ), -1.0 * con_imp.vars.size() );
  p_out_lp->addConstraint( con_imp );
  
  return v_hn;
}

/* sc <=> x=y ^ h_i ^ h_j ^ ... ^ h_n */
inline int _createUnifyCooccurringVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const proof_graph_t &pg, store_item_t ti, store_item_t tj, const vector<int> &literals ) {
  int v_sc    = p_out_lp->addVariable( lp_variable_t( "sc_"+ g_store.claim(ti) + "~" + g_store.claim(tj) + "," + "~" ) );
  int v_coref = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj );

  lp_constraint_t con_sc( "sc_sxyhihj"+ g_store.claim(ti) + "~" + g_store.claim(tj) + "," + "~", Range, 0, 1 );
  repeat( i, literals.size() )
    con_sc.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, literals[i] ), 1.0 );
  
  if( -1 != v_coref ) con_sc.push_back( v_coref, 1.0 );
          
  con_sc.rhs = 1.0 * con_sc.vars.size() - 1;
  con_sc.push_back( v_sc, -1.0 * con_sc.vars.size() );

  p_out_lp->addConstraint( con_sc );
  
  return v_sc;
}

bool function::convertToLP( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &pg, const variable_cluster_t &evc, inference_configuration_t& c ) {

  sparse_vector_t v_inf, v_minf; v_inf[ "FIXED" ] = 9999.0; v_minf[ "FIXED" ] = -9999.0;
  unordered_set<store_item_t> logical_terms;
  
  /* Create an in-memory database for potential elemental hypotheses. */
  sqlite3 *p_db; sqlite3_open( ":memory:", &p_db );
  external_module_t::p_db_pehypotheses = p_db;
  
  sqlite3_exec( p_db, "CREATE TABLE pehypothesis(id INTEGER PRIMARY KEY, explains INTEGER, predicate TEXT, arg1 TEXT, arg2 TEXT, arg3 TEXT, arg4 TEXT, arg5 TEXT, arg6 TEXT)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpehid ON pehypothesis(id)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpehexp ON pehypothesis(explains)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpehpred ON pehypothesis(predicate)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg1 ON pehypothesis(arg1)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg2 ON pehypothesis(arg2)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg3 ON pehypothesis(arg3)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg4 ON pehypothesis(arg4)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg5 ON pehypothesis(arg5)", NULL, 0, NULL );
  sqlite3_exec( p_db, "CREATE INDEX idxpeharg6 ON pehypothesis(arg6)", NULL, 0, NULL );
  
  /* Start creating the feature... */
  p_out_lp->addVariable( lp_variable_t( "dummy" ) );

  /* Factor: new assumption factors and explained factors. */
  repeat( i, pg.nodes.size() ) {
    sqlite3_exec( p_db, ("INSERT INTO pehypothesis VALUES ("+ ::toString(i, "%d") + "," + pg.nodes[i].lit.toSQL() +")").c_str(), NULL, 0, NULL );

    repeat( j, pg.nodes[i].lit.terms.size() ) logical_terms.insert( pg.nodes[i].lit.terms[j] );
    
    // /* Factor: prior. */
    if( g_f_weighted_abduction ? ObservableNode == pg.nodes[i].type : LabelNode != pg.nodes[i].type ) {
      factor_t fc_prior( IdenticalFactorTrigger );
      fc_prior.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ) );

      int v_fc_prior = fc_prior.apply( p_out_lp, "fc_prior_" + pg.nodes[i].toString() );
      p_out_lprel->feature_vector[ v_fc_prior ][ "FC_PRIOR_" + pg.nodes[i].lit.toPredicateArity() ] = g_f_weighted_abduction ? -pg.nodes[i].lit.wa_number : -1;
    }
    
    /* Factor: explained. */
    factor_t fc_explained( OrFactorTrigger );
    lp_constraint_t con_expimp( "expimp", LessEqual, 0 );

    pg_edge_set_t::const_iterator iter_eg = pg.edges.find(i);
    
    if( pg.edges.end() != iter_eg ) {
      repeat( j, iter_eg->second.size() ) {
        double wa_conj_costs  = 0.0;
        int    v_conj         = _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_eg->second[j] );
        fc_explained.push_back( v_conj );

        /* Factor: new assumption. */        
        factor_t fc_assume( IdenticalFactorTrigger );
        fc_assume.push_back( v_conj );

        repeat( k, pg.hypernodes[ iter_eg->second[j] ].size() )
          wa_conj_costs += pg.nodes[ pg.hypernodes[ iter_eg->second[j] ][k] ].lit.wa_number;
        
        con_expimp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, pg.hypernodes[ iter_eg->second[j] ][0] ), -1.0 );
        
        int v_fc = fc_assume.apply( p_out_lp, "fc_a_" + ::toString(iter_eg->second[j], "%d") );
        p_out_lprel->feature_vector[ v_fc ]["FC_A_" + pg.getEdgeName( i, iter_eg->second[j] ) ] = g_f_weighted_abduction ? -wa_conj_costs : -1;
      }
    }

    int v_fc_exp = fc_explained.apply( p_out_lp, "fc_e_" + pg.nodes[i].lit.toString() );
    if( -1 != v_fc_exp ) p_out_lprel->feature_vector[ v_fc_exp ]["FC_E_" + pg.nodes[i].lit.toPredicateArity() ] = g_f_weighted_abduction ? pg.nodes[i].lit.wa_number : 1;

    // if( -1 != v_fc_exp ) {
    //   lp_constraint_t con_h( "fcimp", LessEqual, 0 );
    //   con_h.push_back( v_fc_exp, 1.0 );
    //   con_h.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ), -1.0 );
    //   p_out_lp->addConstraint( con_h );

    //   con_expimp.push_back( v_fc_exp, 1.0 );
    //   p_out_lp->addConstraint( con_expimp );
    // }

    /* Factor: Conjunction duty. */
    pg_node_hypernode_map_t::const_iterator iter_n2hn = pg.n2hn.find(i);
    if( pg.n2hn.end() != iter_n2hn ) {

      factor_t fc_conjduty( AndFactorTrigger );

      repeat( j, iter_n2hn->second.size() ) {
        int v_hn = _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_n2hn->second[j] );
        if( 1 == pg.hypernodes[ iter_n2hn->second[j] ].size() ) continue;
      
        fc_conjduty.push_back( v_hn, false );
      }

      if( fc_conjduty.triggers.size() > 0 ) fc_conjduty.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ) );

      fc_conjduty.apply( p_out_lp, "fc_cjd_" + pg.nodes[i].lit.toString(), true );

    }
    
  }

  sqlite3_exec( p_db, "VACUUM", NULL, 0, NULL );

  g_ext.call( "cbScoreFunction", NULL );
  
  PyObject *pymap = PyDict_New();

  foreachc( pg_term_map_t, iter_tm, pg.t2n ) {
    PyObject *pylist = PyList_New( iter_tm->second.size() );
    
    repeat( i, iter_tm->second.size() )
      PyList_SetItem( pylist, i, PyString_FromString( pg.nodes[ iter_tm->second[i] ].toString().c_str() ) );
    
    PyDict_SetItemString( pymap, g_store.claim(iter_tm->first).c_str(), pylist );
  }
  
  /* Factor: variable unification factors */
  vector<store_item_t> ord_logical_terms( logical_terms.begin(), logical_terms.end() );
  unordered_map<int, unordered_set<int> > constants_unifiables;

  repeat( i, ord_logical_terms.size() ) {
    repeatf( j, i, ord_logical_terms.size() ) {
      
      factor_t     fc_unif_evid( OrFactorTrigger );
      store_item_t ti = ord_logical_terms[i], tj = ord_logical_terms[j]; if( ti > tj ) swap(ti, tj);

      lp_constraint_t con_expunf( "expunf", LessEqual, 0 );
      
      /* Collecting the evidence. */
      PyObject *pyret = g_ext.call( "cbGetUnificationEvidence", Py_BuildValue( "ssO", g_store.claim(ti).c_str(), g_store.claim(tj).c_str(), pymap ) );
      
      if( NULL == pyret ) continue;
      
      /* pyret must be [(0.1, "", [1,3,5]), (...), ...] */
      bool f_including_label = false;
      
      repeat( k, PyList_Size(pyret) ) {
        if( c.isTimeout() ) return false;

        /* Enumerate evidential literals. */
        PyObject    *pytuple = PyList_GetItem( pyret, k ), *pylist = PyTuple_GetItem( pytuple, 2 );
        double       score   = PyFloat_AsDouble( PyTuple_GetItem( pytuple, 0 ) );
        vector<int>  evidential_literals;
        string       signature = "";
          
        repeat( l, PyList_Size(pylist) ) {
          evidential_literals.push_back( PyInt_AsLong( PyList_GetItem( pylist, l ) ) );
          signature += pg.nodes[ evidential_literals[l] ].toString() + " ";
        }
        
        int v_sc = _createUnifyCooccurringVar( p_out_lp, p_out_lprel, p_out_cache, pg, ti, tj, evidential_literals );
        
        V(5) cerr << "Evidence: " << g_store.claim(ti) +"~"+ g_store.claim(tj) << ": " << signature << " (score = " << score << ")" << endl;        
        fc_unif_evid.push_back( v_sc );

        repeat( l, evidential_literals.size() )
          con_expunf.push_back( _createNodeVar(p_out_lp, p_out_lprel, pg, evidential_literals[l]), -1.0 );
        
        /* Factor: unification */
        if( 0.0 != score ) {
          if( -9999 != score ) {
            bool f_is_illusion = LabelNode == pg.nodes[evidential_literals[0]].type || LabelNode == pg.nodes[evidential_literals[1]].type;
            f_including_label |= f_is_illusion;

            factor_t fc_unif( IdenticalFactorTrigger );
            fc_unif.push_back( v_sc );

            int v_fc_ue = fc_unif.apply( p_out_lp, (f_is_illusion ? "fc_u_g_" : "fc_ue_") + g_store.claim(ti) +","+ g_store.claim(tj) +","+ signature );
            
            if( f_is_illusion ) p_out_lp->variables[ v_fc_ue ].obj_val = 9999;
            else                p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_EVIDENCE_" + string(PyString_AsString( PyTuple_GetItem( pytuple, 1 ) )) ] = score;

          } else {
            factor_t fc_unif( AndFactorTrigger );
          
            repeat( l, evidential_literals.size() ) 
              fc_unif.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, evidential_literals[l] ) );
          
            if( ti != tj ) fc_unif.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) );
          
            fc_unif.apply( p_out_lp, "fc_ue_" + g_store.claim(ti) +","+ g_store.claim(tj) +","+ signature, true );
          }
        }
          
      }

      Py_DECREF( pyret );

      if( 0 < fc_unif_evid.triggers.size() ) {
        if( g_store.isConstant(ti) && !g_store.isConstant(tj) ) constants_unifiables[tj].insert(ti);
        if( g_store.isConstant(tj) && !g_store.isConstant(ti) ) constants_unifiables[ti].insert(tj);
      }

      if( ti != tj && !g_store.isConstant(ti) && !g_store.isConstant(tj) ) {
        int v_fc_ue = fc_unif_evid.apply( p_out_lp, (f_including_label ? "fc_u_g_" : "fc_ue_") + g_store.claim(ti) +","+ g_store.claim(tj) );
        
        if( -1 != v_fc_ue ) {

          /* e1 v e2 v ... v en => ue ^ coref */
          // repeat( k, fc_unif_evid.triggers.size() ) {
          //   lp_constraint_t con_h( "fcimp", LessEqual, 0 );
          //   con_h.push_back( fc_unif_evid.triggers[k], 2.0  );
          //   con_h.push_back( v_fc_ue, -1.0 );
          //   con_h.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), -1.0 );
          //   p_out_lp->addConstraint( con_h );
          // }
          
          //con_expunf.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), 2.0 );
          con_expunf.push_back( v_fc_ue, 2.0 );
          p_out_lp->addConstraint( con_expunf );

          if( !f_including_label )
            p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD" ] = 1.0;
          else
            p_out_lp->variables[ v_fc_ue ].obj_val = 1.0;
          
          // /* Factor: new assumption. */
          // if( f_including_label ) {
          //   p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) ].obj_val = -1;
          //   p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) ].name = "fc_u_g_";
          // } else {
          //   factor_t fc_prior( IdenticalFactorTrigger );
          //   fc_prior.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) );
          //   int v_fc_prior = fc_prior.apply( p_out_lp, "fc_ua_" + g_store.claim(ti) +","+ g_store.claim(tj) );
          //   p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" ] = -1;
          // }
          
          // lp_constraint_t con_h( "fcimp", LessEqual, 0 );
          // con_h.push_back( v_fc_ue, 1.0 );
          // con_h.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), -1.0 );
          // p_out_lp->addConstraint( con_h );
          
          // const vector<int> *p_nodes_ti, *p_nodes_tj;
          // pg.getNode( &p_nodes_ti, tj ); pg.getNode( &p_nodes_tj, ti );

          // repeat( k, p_nodes_ti->size() ) {
          //   int  ni = (*p_nodes_ti)[k];
          //   cerr << pg.nodes[ni].toString() << g_store.claim( tj ) << pg.nodes[ni].type << endl;
          //   if( ObservableNode == pg.nodes[ ni ].type ) { cerr << "yyyy" << endl; }
          //     repeat( l, p_nodes_tj->size() ) {
          //     int nj = (*p_nodes_tj)[l];
          //     // if( ObservableNode == pg.nodes[ ni ].type ) p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" + pg.nodes[ ni ].lit.toPredicateArity() ]  = -1;
          //     // if( ObservableNode == pg.nodes[ nj ].type ) p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" + pg.nodes[ nj ].lit.toPredicateArity() ]  = -1;
          //     if( ObservableNode == pg.nodes[ ni ].type ) p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD_FOR_" + pg.nodes[ ni ].lit.toPredicateArity() ]  = 1;
          //     if( ObservableNode == pg.nodes[ nj ].type ) p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD_FOR_" + pg.nodes[ nj ].lit.toPredicateArity() ]  = 1;
          //   } }

        }
      }
      
    } }

  sqlite3_close( p_db );
  
  Py_DECREF( pymap );
  
  /* Impose mutual exclusiveness over variable equaility relation. */
  for( unordered_map<store_item_t, unordered_set<int> >::iterator iter_cm=constants_unifiables.begin(); constants_unifiables.end()!=iter_cm; ++iter_cm ) {
    if( 1 == iter_cm->second.size() ) continue;
    
    V(4) cerr << "MX: " << g_store.claim(iter_cm->first) << ":";

    lp_constraint_t con_con( "mxc", LessEqual, 1.0 );
    
    foreach( unordered_set<store_item_t>, iter_t, iter_cm->second ) {
      con_con.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, iter_cm->first, *iter_t ), 1.0 );
      V(4) cerr << g_store.claim(*iter_t) << ", ";
    }

    V(4) cerr << endl;
    
    p_out_lp->addConstraint( con_con );
  }
  
  V(2) cerr << "enumerateP: ... done." << endl;
  
  /* Impose transitivity constraints on variable equality relation. */
  for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
    vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
    
    repeat( i, variables.size() ) {
      repeatf( j, i+1, variables.size() ) {
        if( c.isTimeout() ) return false;
        
        store_item_t t1 = variables[i], t2 = variables[j]; if( t1 > t2 ) swap(t1, t2);
        _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, t1, t2, false );
      } }
  }

  if( BnB == c.method || LocalSearch == c.method ) {
    V(2) cerr << "enumerateP: Creating transitivity constraints..." << endl;

    for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {

      vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
      
      for( uint_t i=0; i<variables.size(); i++ ) {
        for( uint_t j=i+1; j<variables.size(); j++ ) {
          for( uint_t k=j+1; k<variables.size(); k++ ) {
            store_item_t ti = variables[i], tj = variables[j], tk = variables[k];
            int
              v_titj        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj, false ),
              v_tjtk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, tj, tk, false ),
              v_titk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tk, false );

            if( c.isTimeout() ) return false;
            if( -1 == v_titj || -1 == v_tjtk || -1 == v_titk ) continue;
        
            lp_constraint_t con_trans1( "trans", GreaterEqual, -1 );
            con_trans1.push_back( v_titk, 1.0 );
            con_trans1.push_back( v_titj, -1.0 );
            con_trans1.push_back( v_tjtk, -1.0 );
            p_out_lp->addConstraint( con_trans1 );

            lp_constraint_t con_trans2( "trans", GreaterEqual, -1 );
            con_trans2.push_back( v_titk, -1.0 );
            con_trans2.push_back( v_titj, 1.0 );
            con_trans2.push_back( v_tjtk, -1.0 );
            p_out_lp->addConstraint( con_trans2 );

            lp_constraint_t con_trans3( "trans", GreaterEqual, -1 );
            con_trans3.push_back( v_titk, -1.0 );
            con_trans3.push_back( v_titj, -1.0 );
            con_trans3.push_back( v_tjtk, 1.0 );
            p_out_lp->addConstraint( con_trans3 );
        
          } } }
    }
    
    V(2) cerr << "enumerateP: ... done." << endl;
  }

  /* Loss augmented factors. */
  if( false ) {//LossAugmented == c.objfunc ) {
    
    vector<const literal_t*>  y_literals;
    c.training_instance.y_lf.getAllLiterals( &y_literals );

    
    repeat( i, y_literals.size() ) {
      
      const vector<int> *p_nodes;
      if( !pg.getNode( &p_nodes, y_literals[i]->predicate, y_literals[i]->terms.size() ) ) cerr << "Could not find a gold literal." << endl;

      /* Loss for predicate priors. */
      factor_t fc_loss_pri( OrFactorTrigger );
      
      repeat( ipa, p_nodes->size() )
        fc_loss_pri.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, (*p_nodes)[ipa] ) );

      int v_fc_loss_pri = fc_loss_pri.apply( p_out_lp, "fc_loss" + y_literals[i]->toString() );
      if( -1 != v_fc_loss_pri ) p_out_lp->variables[ v_fc_loss_pri ].obj_val = -1.0;                
      
      /* Loss for argument matching. */
      repeat( it, y_literals[i]->terms.size() ) {
        
        repeatf( j, i+1, y_literals.size() ) { 
          repeat( jt, y_literals[j]->terms.size() ) {

            if( y_literals[i]->terms[it] != y_literals[j]->terms[jt] ) continue;

            //cerr << y_literals[i]->toString() << y_literals[j]->toString() << endl;

            const vector<int> *p_nodes_j;
            if( !pg.getNode( &p_nodes_j, y_literals[j]->predicate, y_literals[j]->terms.size() ) ) continue;

            factor_t fc_loss_am( OrFactorTrigger );

            repeat( ipa, p_nodes->size() ) {
              repeat( jpa, p_nodes_j->size() ) {
                if( (*p_nodes)[ipa] == (*p_nodes_j)[jpa] ) continue;

                //cerr << pg.nodes[ (*p_nodes)[ipa] ].lit.toString() << pg.nodes[ (*p_nodes_j)[jpa] ].lit.toString() << g_store.claim(pg.nodes[ (*p_nodes)[ipa] ].lit.terms[it]) << g_store.claim(pg.nodes[ (*p_nodes_j)[jpa] ].lit.terms[jt]) << endl;
                
                if( pg.nodes[ (*p_nodes)[ipa] ].lit.terms[it] == pg.nodes[ (*p_nodes_j)[jpa] ].lit.terms[jt] ) {
                  factor_t fc_coocur( AndFactorTrigger );
                  fc_coocur.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, (*p_nodes)[ipa] ) );
                  fc_coocur.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, (*p_nodes_j)[jpa] ) );
                  fc_loss_am.push_back( fc_coocur.apply( p_out_lp, "fc_co" + pg.nodes[ (*p_nodes)[ipa] ].lit.toString() + pg.nodes[ (*p_nodes_j)[jpa] ].lit.toString() ) );
                } else {
                  int v_coref = _getCorefVar( pg.nodes[ (*p_nodes)[ipa] ].lit.terms[it], pg.nodes[ (*p_nodes_j)[jpa] ].lit.terms[jt], (const lp_problem_mapping_t&)*p_out_lprel );
                  if( -1 == v_coref ) continue;
                  factor_t fc_coocur( AndFactorTrigger );
                  fc_coocur.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, (*p_nodes)[ipa] ) );
                  fc_coocur.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, (*p_nodes_j)[jpa] ) );
                  fc_coocur.push_back( v_coref );
                  fc_loss_am.push_back( fc_coocur.apply( p_out_lp, "fc_co" + pg.nodes[ (*p_nodes)[ipa] ].lit.toString() + pg.nodes[ (*p_nodes_j)[jpa] ].lit.toString() + "^" + g_store.claim(pg.nodes[ (*p_nodes_j)[jpa] ].lit.terms[jt]) + "==" + g_store.claim(pg.nodes[ (*p_nodes)[ipa] ].lit.terms[it]) ) );
                }
                
              } }

            int v_fc_loss_am = fc_loss_am.apply( p_out_lp, "fc_loss" + y_literals[i]->toString() + y_literals[j]->toString() );
            if( -1 != v_fc_loss_am ) p_out_lp->variables[ v_fc_loss_am ].obj_val = -1.0;                
            
          } }
        
      }
      
    }
    
  }
    
  /* Set the feature vector. */
  for( unordered_map<int, sparse_vector_t>::iterator iter_o2v=p_out_lprel->feature_vector.begin(); p_out_lprel->feature_vector.end() != iter_o2v; ++iter_o2v ) {
    for( sparse_vector_t::iterator iter_v=iter_o2v->second.begin(); iter_o2v->second.end()   != iter_v; ++iter_v ) {
      if( "FIXED" == iter_v->first ) p_out_lp->variables[ iter_o2v->first ].obj_val  = iter_v->second;
      else                           p_out_lp->variables[ iter_o2v->first ].obj_val += (c.ignore_weight ? 1.0 : c.p_sfunc->weights[ iter_v->first ]) * iter_v->second;
    }
  }
  
  return true;
  
}

void function::adjustLP( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &pg, const variable_cluster_t &evc, inference_configuration_t& c ) {

  if( LabelGiven == c.objfunc ) {

    for( uint_t i=0; i<p_out_lprel->v_loss.size(); i++ )
      if( !p_out_lp->variables[ p_out_lprel->v_loss[i] ].isFixed() ) p_out_lp->variables[ p_out_lprel->v_loss[i] ].fixValue( 0.0 );
    
  }
  
}

void function::convertLPToHypothesis( logical_function_t *p_out_h, sparse_vector_t *p_out_fv, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const variable_cluster_t &evc, const proof_graph_t &pg ) {

  p_out_h->opr = AndOperator;
  p_out_h->branches.clear();
  
  for( uint_t i=0; i<pg.nodes.size(); i++ ) {
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find(i);
    if( lprel.n2v.end() == iter_v ) continue;
    
    if( 0.5 < lp.variables[ iter_v->second ].optimized )
      p_out_h->branches.push_back( logical_function_t( pg.nodes[i].lit ) );
  }

  /* Create equality literals. */
  variable_cluster_t vc;
  foreachc( pairwise_vars_t, iter_t1, lprel.pp2v )
    for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
      if( 0.5 < lp.variables[ iter_t2->second ].optimized ) vc.add( iter_t1->first, iter_t2->first );
    }

  foreach( variable_cluster_t::cluster_t, iter_vc, vc.clusters )
    if( iter_vc->second.size() > 1) {
      literal_t equality( PredicateSubstitution );
      
      for( unordered_set<store_item_t>::iterator iter_v=iter_vc->second.begin(); iter_vc->second.end()!=iter_v; ++iter_v )
        equality.terms.push_back( *iter_v );
      
      p_out_h->branches.push_back( logical_function_t( equality ) );
    }

  if( NULL != p_out_fv ) {
    repeat( i, lp.variables.size() ) {
      if( 0.5 > lp.variables[i].optimized ) continue;
      if( lprel.feature_vector.end() != lprel.feature_vector.find(i) ) addVector( p_out_fv, lprel.feature_vector.find(i)->second );
    }
  }
  
}

void function::sample( vector<double> *p_out_array, const sampling_method_t m ) {

  switch(m) {
    
  case Random: {
    srand( time(NULL) );
    for( uint_t i=0; i<p_out_array->size(); i++ ) (*p_out_array)[i] = (rand() % 10000) / 10000.0;
    break; }
    
  case Uniform: {
    double val = 1.0 / p_out_array->size();
    for( uint_t i=0; i<p_out_array->size(); i++ ) (*p_out_array)[i] = val;
    break; }
    
  }
    
}

bool function::compileKB( knowledge_base_t *p_out_kb, const precompiled_kb_t &pckb ) {

  unordered_map<string, string> pa2axioms;

  p_out_kb->keys.clear();
  p_out_kb->axioms.clear();
  
  for( precompiled_kb_t::const_iterator iter_p = pckb.begin(); pckb.end() != iter_p; ++iter_p )
    for( unordered_map<int, vector<string> >::const_iterator iter_a = iter_p->second.begin(); iter_p->second.end() != iter_a; ++iter_a ) {
      char buffer[ 1024 ];
      sprintf( buffer, "%s/%d", g_store.claim( iter_p->first ).c_str(), iter_a->first );
      p_out_kb->keys.push_back( string(buffer) );

      for( uint_t i=0; i<iter_a->second.size(); i++ )
        pa2axioms[ string(buffer) ] += (0 != i ? "\t" : "") + iter_a->second[i];
      
    }

  /* Sort it! */
  V(5) cerr << "compileKB: Sorting the hash keys..." << endl;
  
  sort( p_out_kb->keys.begin(), p_out_kb->keys.end() );

  /* Prepare the key-index pairs for DARTS. */
  vector<const char*> da_keys;
  vector<int>         da_vals;
  
  for( uint_t i=0; i<p_out_kb->keys.size(); i++ ) {
    da_keys.push_back( p_out_kb->keys[i].c_str() ); da_vals.push_back( i );
    p_out_kb->axioms.push_back( pa2axioms[ p_out_kb->keys[i] ] );
  }

  p_out_kb->da.clear();
  
  /* Write the hash table. */
  if( 0 != p_out_kb->da.build( da_keys.size(), &da_keys[0], 0, &da_vals[0] ) ) return false;

  return true;
  
}

bool function::writePrecompiledKB( precompiled_kb_t &pckb, const string &filename ) {

  knowledge_base_t kb;
  compileKB( &kb, pckb );

  /* Write all the axioms at once. */
  ofstream ofs( filename.c_str(), ios::binary );
  int      size = kb.axioms.size();
  ofs.write( (char*)&size, sizeof(int) );
  
  for( uint_t i=0; i<kb.axioms.size(); i++ ) {
    size = kb.axioms[i].size();
    ofs.write( (char *)&size, sizeof(int) );
    ofs.write( (char *)kb.axioms[i].c_str(), size );
  }
  
  ofs.close();
  
  /* Write the hash table. */
  if( 0 != kb.da.save( filename.c_str(), "ab" ) ) return false;
  
  return true;
  
}

bool function::readPrecompiledKB( knowledge_base_t *p_out_kb, const string &filename ) {
  
  ifstream ifs_pckb( filename.c_str(), ios::binary );
  if( !ifs_pckb.is_open() ) return false;
  
  /* Read the header. */
  V(5) cerr << "readPrecompiledKB: Loading header..." << endl;
  
  int num_axioms, size_header = 0;
  ifs_pckb.read( (char *)&num_axioms, sizeof(int) );
  size_header += sizeof(int);

  for( int i=0; i<num_axioms; i++ ) {
    int axiom_length;
    ifs_pckb.read( (char *)&axiom_length, sizeof(int) );

    char buffer[ 1024*1000 ];
    ifs_pckb.read( (char *)buffer, axiom_length ); buffer[ axiom_length ] = 0;
    p_out_kb->axioms.push_back( string(buffer) );
    
    size_header += sizeof(int) + axiom_length;
  }

  ifs_pckb.close();

  V(5) cerr << "readPrecompiledKB: Done." << endl;
  
  /* Read the hash table. */
  if( 0 != p_out_kb->da.open( filename.c_str(), "rb", size_header ) ) return false;

  return true;

}

void function::getParsedOption( command_option_t *p_out_opt, vector<string> *p_out_args, const string &acceptable, int argc, char **argv ) {
  
  int              option;
  
  /* Hmm... let me see. */
  while( -1 != (option = getopt( argc, argv, acceptable.c_str() )) ) {
    if( NULL == optarg ) (*p_out_opt)[ option ] = "";
    else                 (*p_out_opt)[ option ] = optarg;
  }

  for( int i=optind; i<argc; i++ )
    p_out_args->push_back( argv[i] );

}

double loss_t::_lossClassification( int y_cls, double current_score ) {

  int y_current = current_score >= 0 ? 1 : -1;

  if( 1 == y_current * y_cls ) {
    this->loss = 0.0;
    return 0.0;
  }

  this->loss = 1.0 - y_cls * current_score;
  return this->loss;
  
}

store_item_t _findRepr( unordered_set<store_item_t> vars ) {
  foreach( unordered_set<store_item_t>, iter_v, vars )
    if( g_store.isConstant( *iter_v ) ) return *iter_v;
  foreach( unordered_set<store_item_t>, iter_v, vars )
    if( !g_store.isUnknown( *iter_v ) ) return *iter_v;
  return *vars.begin();
}

double loss_t::_lossVariableWise( unordered_set<store_item_t> *p_out_rel_vars, const logical_function_t& y_lf, const logical_function_t y_current ) {

  PyObject *pyret = g_ext.call( "cbGetLoss", Py_BuildValue( "ss", y_current.toString().c_str(), y_lf.toString().c_str() ) );
  this->loss = PyInt_AsLong( pyret );
  
  return 0.0;
  
  vector<const literal_t*> literals_target, literals_this;
  unordered_map<store_item_t, string> clusters;
  unordered_map<string, unordered_set<store_item_t> > s2c;

  y_lf.getAllLiterals( &literals_target );
  y_current.getAllLiterals( &literals_this );

  /* Create unification mapping. */
  for( uint_t i=0; i<literals_this.size(); i++ ) {
    if( PredicateSubstitution != g_store.claim(literals_this[i]->predicate) ) continue;
    string signature = "{"+g_store.toString( literals_this[i]->terms )+"}";
    for( uint_t j=0; j<literals_this[i]->terms.size(); j++ ) {
      clusters[ literals_this[i]->terms[j] ] = signature;
      s2c[ signature ].insert( literals_this[i]->terms[j] );
    }
  }

  /* Create mappings from variable to literals. */
  int score = 0, max_score = 0;
  
  for( uint_t i=0; i<literals_target.size(); i++ ) {

    V(5) cerr << "LT: " << literals_target[i]->toString() << endl;

    /* Are you there? */
    max_score++;
    
    for( uint_t j=0; j<literals_this.size(); j++ )
      if( literals_this[j]->toPredicateArity() == literals_target[i]->toPredicateArity() ) { score++; break; }
    
    si2s_t local_bindings;

    for( uint_t j=0; j<literals_target[i]->terms.size(); j++ ) {
      local_bindings[ literals_target[i]->terms[j] ];
      
      for( uint_t k=0; k<literals_this.size(); k++ ) {

        if( literals_this[k]->toPredicateArity() != literals_target[i]->toPredicateArity() ) continue;

        string c = clusters[literals_this[k]->terms[j]];
        if( "" == c ) {
          c = clusters[literals_this[k]->terms[j]] = g_store.claim( literals_this[k]->terms[j] );
          s2c[ g_store.claim( literals_this[k]->terms[j] ) ].insert( literals_this[k]->terms[j] );
        }
        
        local_bindings[ literals_target[i]->terms[j] ].push_back( c );

        V(5) cerr << "LB: " << _SC(literals_target[i]->terms[j]) << "=" << _SC(literals_this[k]->terms[j]) << "(" << c << ")" << endl;
        
      }
    }

    foreach( si2s_t, iter_lb, local_bindings ) {
      sort( iter_lb->second.begin(), iter_lb->second.end() );
      
      if( v2l.end() == v2l.find( iter_lb->first ) ) {
        v2l[ iter_lb->first ] = iter_lb->second;
        V(5) cerr << g_store.claim(iter_lb->first) << ":" << ::toString( v2l[ iter_lb->first ].begin(), v2l[ iter_lb->first ].end() ) << endl;
        continue;
      }
      
      V(5) {
        cerr << g_store.claim(iter_lb->first) << ":" << endl;
        cerr << "Intersection: Before = " << ::toString( v2l[ iter_lb->first ].begin(), v2l[ iter_lb->first ].end() ) << endl;
        cerr << "Intersection: Before = " << ::toString( iter_lb->second.begin(), iter_lb->second.end() ) << endl;
      }
        
      vector<string> common_vars;
        
      if( iter_lb->second.size() > 0 )
        set_intersection( v2l[ iter_lb->first ].begin(), v2l[ iter_lb->first ].end(),
                          iter_lb->second.begin(), iter_lb->second.end(), inserter(common_vars, common_vars.begin()) );
        
      v2l[ iter_lb->first ] = common_vars;
        
      V(5) cerr << "Intersection: After = " << ::toString( v2l[ iter_lb->first ].begin(), v2l[ iter_lb->first ].end() ) << endl;
      
    }
  }
  
  foreach( si2s_t, iter_v2l, v2l ) {
    max_score++;
    V(5) cerr << "V2L: " << g_store.claim( iter_v2l->first ) << "=" << ::toString( iter_v2l->second.begin(), iter_v2l->second.end() ) << endl;
    if( 0 != iter_v2l->second.size() ) score++;
    if( NULL != p_out_rel_vars ) {
      for( uint_t i=0; i<iter_v2l->second.size(); i++ )
        p_out_rel_vars->insert( s2c[iter_v2l->second[i]].begin(), s2c[iter_v2l->second[i]].end() );
    }
  }

  /* Output alignment information. */
  unordered_map<string, unordered_set<string> > literals;

  repeat( i, literals_this.size() ) {
    if( PredicateSubstitution == g_store.claim(literals_this[i]->predicate) ) continue;
    literal_t duplicated_this = *literals_this[i];
    repeat( j, duplicated_this.terms.size() ) {
      if( clusters.end() == clusters.find( duplicated_this.terms[j] ) ) continue;
      duplicated_this.terms[j] = _findRepr( s2c[ clusters[duplicated_this.terms[j]] ] );
    }
    literals[ duplicated_this.toPredicateArity() ].insert( duplicated_this.toString() );
  }

  repeat( i, literals_target.size() )
    this->im_not_here[ literals_target[i]->toString() ].insert( literals[ literals_target[i]->toPredicateArity() ].begin(), literals[ literals_target[i]->toPredicateArity() ].end() );

  this->loss         = max_score - score;
  this->maximum_loss = max_score;
  
  return max_score - score > 0;
  
}

void proof_graph_t::printGraph( const linear_programming_problem_t &lpp, const lp_problem_mapping_t &lprel, const string& property ) const {

  (*g_p_out) << "<proofgraph" << ("" != property ? (" " + property) : "") << ">" << endl;
  
  for( uint_t i=0; i<nodes.size(); i++ ) {
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find(i);
    if( lprel.n2v.end() == iter_v ) continue;
    
    (*g_p_out) << "<literal id=\""<< i <<"\" type=\""<< nodes[i].type <<"\" active=\""<< (lpp.variables[ iter_v->second ].optimized < 0.5 ? "no" : "yes") <<"\">"
         << nodes[i].toString() << "</literal>" << endl;

    const vector<int> *p_unifiables;
    getNode( &p_unifiables, nodes[i].lit.predicate, nodes[i].lit.terms.size() );

    repeat( j, p_unifiables->size() ) {
      uint_t nj = (*p_unifiables)[j];

      if( i == nj ) continue;
      
      unordered_map<int, int>::const_iterator iter_vj = lprel.n2v.find(nj);
      if( lprel.n2v.end() == iter_vj ) continue;

      unifier_t uni;
      if( !getMGU( &uni, nodes[i].lit, nodes[nj].lit ) ) continue;

      bool f_fails = false;
      
      repeat( k, uni.substitutions.size() ) {
        store_item_t t1 = uni.substitutions[k].terms[0], t2 = uni.substitutions[k].terms[1]; if( t1 > t2 ) swap(t1, t2);
        int v_sxy = _getCorefVar(t1, t2, lprel);

        if( t1 == t2 ) continue;
        if( -1 == v_sxy ) { f_fails = true; break; }
        if( lpp.variables[ v_sxy ].optimized < 0.5 ) { f_fails = true; break; }
      }

      f_fails |= lpp.variables[ iter_v->second ].optimized < 0.5;
      f_fails |= lpp.variables[ iter_vj->second ].optimized < 0.5;

      (*g_p_out) << "<unification l1=\""<< i <<"\" l2=\""<< nj << "\" unifier=\""<< uni.toString() << "\" active=\""<< (lpp.variables[ iter_vj->second ].optimized > 0.5 && !f_fails ? "yes" : "no") << "\" />" << endl;
    }
    
  }
  
  for( pg_edge_set_t::const_iterator iter_eg = edges.begin(); edges.end() != iter_eg; ++iter_eg ) {
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find( iter_eg->first );
    if( lprel.n2v.end() == iter_v ) continue;

    for( uint_t i=0; i<iter_eg->second.size(); i++ ) {

      uint_t n_active = 0;
      
      for( uint_t j=0; j<hypernodes[ iter_eg->second[i] ].size(); j++ ) {
        unordered_map<int, int>::const_iterator iter_vt = lprel.n2v.find( hypernodes[ iter_eg->second[i] ][j] );
        if( lprel.n2v.end() == iter_vt ) continue;
        if( 0.5 < lpp.variables[ iter_vt->second ].optimized ) n_active++;
      }

      (*g_p_out) << "<explanation active=\""<< (0.5 < lpp.variables[ iter_v->second ].optimized && hypernodes[ iter_eg->second[i] ].size() == n_active ? "yes" : "no") <<"\" axiom=\"\">";
      
      for( uint_t j=0; j<hypernodes[ iter_eg->second[i] ].size(); j++ ) {
        (*g_p_out) << hypernodes[ iter_eg->second[i] ][j];
        if( j < hypernodes[ iter_eg->second[i] ].size()-1 ) (*g_p_out) << " ^ ";
      }

      (*g_p_out) << " => " << iter_eg->first << "</explanation>" << endl;
      
    }
        
  }

  (*g_p_out) << "</proofgraph>" << endl;
  
}

/* Thanks for https://gist.github.com/240957. */
sexp_reader_t &sexp_reader_t::operator++() {

  bool f_comment = false;
  char last_c    = 0;
  
  while( m_stream.good() ) {

    char c = m_stream.get();
    
    if( '\\' != last_c && ';' == c ) { f_comment = true; continue; }
    if( f_comment ) {
      if( '\n' == c ) f_comment = false;
      continue;
    }
    
    switch( m_stack.back()->type ) {
    
    case ListStack: {
      if( '(' == c ) { m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); }
      else if( ')' == c ) {
        m_stack[ m_stack.size()-2 ]->children.push_back( m_stack.back() ); m_stack.pop_back();
        if( TupleStack == m_stack.back()->children[0]->type && "quote" == m_stack.back()->children[0]->children[0]->str ) {
          m_stack[ m_stack.size()-2 ]->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
        stack = *m_stack.back()->children.back();
        return *this;
      } else if( '"' == c ) m_stack.push_back( new_stack( sexp_stack_t(StringStack) ) );
      else   if( '\'' == c ) m_stack.push_back( new_stack( sexp_stack_t(TupleStack, "quote", m_stack_list) ) );
      else if( isSexpSep(c) ) break;
      else m_stack.push_back( new_stack( sexp_stack_t(TupleStack, string(1, c), m_stack_list) ) );
      break; }
      
    case StringStack: {
      if( '"' == c ) {
        m_stack[ m_stack.size()-2 ]->children.push_back( m_stack.back() ); m_stack.pop_back();
        if( m_stack.back()->children[0]->type == TupleStack && m_stack.back()->children[0]->children[0]->str == "quote" ) {
          m_stack[ m_stack.size()-2 ]->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
      } else if( '\\' == c ) m_stack.back()->str += m_stream.get();
      else if( ';' != c ) m_stack.back()->str += c;
      break; }

    case TupleStack: {
      if( isSexpSep(c) ) {
        sexp_stack_t *p_atom = m_stack.back(); m_stack.pop_back();
        m_stack.back()->children.push_back(p_atom);
        if( TupleStack == m_stack.back()->children[0]->type && "quote" == m_stack.back()->children[0]->children[0]->str ) {
          m_stack[ m_stack.size()-2 ]->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
        m_stream.unget();
      } else if( '\\' == c ) m_stack.back()->children[0]->str += m_stream.get();
      else m_stack.back()->children[0]->str += c;
      break; }
    }

    last_c = c;
    
  }

  return *this;
  
}

