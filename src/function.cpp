#include "defs.h"

#include <time.h>
#include <stdlib.h>
#include <math.h>

#include <fstream>
#include <algorithm>
#include <map>

#include "darts.h"

using namespace function;

 
inline string _createSQLquery( unordered_map<int, string> *p_out_vars, logical_function_t &cnf_lf, bool f_all_placeholder=false ) {
  
  vector<string>     query_sel, query_from, query_where, query_where_pred;
  unordered_map<store_item_t, unordered_set<string> > argeq, predeq;
          
  repeat( j, cnf_lf.branches.size() ) {
    query_sel.push_back( ::toString("p%d.*", 1+j) );

    string searchstr = g_store.claim(cnf_lf.branches[j].lit.predicate);
    if( string::npos != searchstr.find("%") ) searchstr.replace( searchstr.find("%"), 2, "%" );
    if( string::npos != searchstr.find("*") ) searchstr.replace( searchstr.find("*"), 1, "%" );
    if( "%" != searchstr ) {
      if( string::npos != searchstr.find("-") && string::npos != searchstr.find("%") )
        query_where_pred.push_back( ::toString("p%d.suffix='%s'", 1+j, searchstr.substr( searchstr.find("-")+1 ).c_str() ) );
      else
        query_where_pred.push_back( ::toString("p%d.predicate", 1+j) + (string::npos == searchstr.find("%") ? "='" : " LIKE '")+ (searchstr) +"'" );
    }
    
    if( string::npos == g_store.claim(cnf_lf.branches[j].lit.predicate).find("*") )
      predeq[ cnf_lf.branches[j].lit.predicate ].insert( ::toString("p%d.predicate", 1+j) );
    
    query_from.push_back( ::toString("pehypothesis as p%d", 1+j) );

    if( NULL != p_out_vars ) {
      repeat( k, MaxArguments )
        if( k < cnf_lf.branches[j].lit.terms.size() )
          (*p_out_vars)[ j*MaxArguments+k ] = g_store.claim( cnf_lf.branches[j].lit.terms[k] );
    }
    
    if( g_store.isEqual( cnf_lf.branches[j].lit.predicate, "=" ) || g_store.isEqual( cnf_lf.branches[j].lit.predicate, "!=" ) ) continue;
    
    repeat( k, cnf_lf.branches[j].lit.terms.size() ) {
      if( g_store.isEqual( cnf_lf.branches[j].lit.terms[k], "*" ) ) break;
      if( g_store.isEqual( cnf_lf.branches[j].lit.terms[k], "_" ) ) continue;
      string searchstr = g_store.claim(cnf_lf.branches[j].lit.terms[k]);
      if( string::npos != searchstr.find("%") ) searchstr.replace( searchstr.find("%"), 2, "%" );
      if( !f_all_placeholder && "%" != searchstr ) query_where.push_back( ::toString("p%d",1+j) + "." + ::toString("arg%d",1+k) + (string::npos == g_store.claim(cnf_lf.branches[j].lit.terms[k]).find("%") ? "='" : " LIKE '")+ (searchstr) +"'" );
      argeq[ cnf_lf.branches[j].lit.terms[k] ].insert( ::toString("p%d",1+j) + "." + ::toString("arg%d",1+k) );
    }
    
    repeat( k, MaxArguments ) {
      if( k < cnf_lf.branches[j].lit.terms.size() )
        query_where.push_back( ::toString("p%d",1+j) + "." + ::toString("arg%d", 1+k) + "!=''" );
      else if( !g_store.isEqual( cnf_lf.branches[j].lit.terms[ cnf_lf.branches[j].lit.terms.size()-1 ], "*" ) )
        query_where.push_back( ::toString("p%d",1+j) + "." + ::toString("arg%d", 1+k) + "=''" );
    }

  }

for( unordered_map<store_item_t, unordered_set<string> >::iterator iter_am=argeq.begin(); argeq.end()!=iter_am; ++iter_am ) {
    vector<string> args( iter_am->second.begin(), iter_am->second.end() ); if( 1 == args.size() ) continue;
    repeat( k, args.size()-1 ) query_where.push_back( args[k] + "=" + args[k+1] );
  }

  for( unordered_map<store_item_t, unordered_set<string> >::iterator iter_am=predeq.begin(); predeq.end()!=iter_am; ++iter_am ) {
    vector<string> args( iter_am->second.begin(), iter_am->second.end() ); if( 1 == args.size() ) continue;
    repeat( k, args.size()-1 ) query_where.push_back( args[k] + "=" + args[k+1] );
  }

  query_where.insert( query_where.begin(), query_where_pred.begin(), query_where_pred.end() );

  return "SELECT "+ join(query_sel.begin(), query_sel.end(), ", ") +" FROM "+ join(query_from.begin(), query_from.end(), ", ") + (0 < query_where.size() ? " WHERE "+ join(query_where.begin(), query_where.end(), " AND ") : "");
  
}

inline string _createSQLquery( unordered_map<int, string> *p_out_vars, const sexp_stack_t &srstack ) {
  logical_function_t cnf_lf(srstack);
  return _createSQLquery( p_out_vars, cnf_lf );
}

bool function::enumeratePotentialElementalHypotheses( proof_graph_t *p_out_pg, variable_cluster_t *p_out_evc, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t &kb, const inference_configuration_t &c ) {

  double                   total_observation_cost = 0;
  variable_cluster_t       vc;
  vector<int>              nodes_obs;
  vector<const literal_t*> literals;
  obs.getAllLiterals( &literals );
  
  repeat( i, literals.size() ) {
    if( g_store.isEqual( literals[i]->predicate, "=" ) ) {
      //if( LossAugmented == c.objfunc || (LabelGiven == c.objfunc && i < c.initial_label_index) ) continue;
      
      repeat( j, literals[i]->terms.size() )
        repeatf( k, j+1, literals[i]->terms.size() ) vc.add( literals[i]->terms[j], literals[i]->terms[k] );
      
      continue;
    }
    
    int n_obs = p_out_pg->addNode( *literals[i], LabelGiven != c.objfunc || i < c.initial_label_index ? ObservableNode : LabelNode );

    p_out_pg->nodes[ n_obs ].obs_node              = n_obs;
    p_out_pg->nodes[ n_obs ].instantiated_by.axiom = ""; //sexp_obs;
    p_out_pg->nodes[ n_obs ].instantiated_by.where = i;
    nodes_obs.push_back( n_obs );

    if(!g_store.isEqual( literals[i]->predicate, "!=" ))
      total_observation_cost += p_out_pg->nodes[n_obs].lit.wa_number;
    
    V(4) cerr << TS() << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << literals[i]->toString() << endl;
  }

  /* Make it relative cost. */
  repeat( i, nodes_obs.size() ) {
    p_out_pg->nodes[nodes_obs[i]].lit.wa_number /= total_observation_cost;
    V(4) cerr << TS() << " Revised input: Type=" << p_out_pg->nodes[nodes_obs[i]].type << ", " << p_out_pg->nodes[nodes_obs[i]].lit.toString() << ", " << p_out_pg->nodes[nodes_obs[i]].lit.wa_number << endl;
  }
  
  if( g_ext.isFunctionDefined( "cbPreprocess" ) ) {
    mypyobject_t::buyTrashCan();

    external_module_context_t emc = {p_out_pg, NULL, &c};
    mypyobject_t pycon( PyCapsule_New( (void*)&emc, NULL, NULL) );
    mypyobject_t pyarg( Py_BuildValue("(OO)", pycon.p_pyobj, external_module_t::asListOfTuples(*p_out_pg) ) );
    mypyobject_t pyret( g_ext.call( "cbPreprocess", pyarg.p_pyobj ) );

    if( NULL != pyret.p_pyobj ) {
      /* [("p", ["x1", "x2", ...]), (), ...] */
      repeat(i, PyList_Size(pyret.p_pyobj)) {
        literal_t      lit(PyString_AsString(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 0)));
        
        repeat( j, PyList_Size(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 1)) ) {
          lit.terms.push_back( g_store.cashier(PyString_AsString(PyList_GetItem(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 1), j)) ) );
        }

        unordered_set<int> parents; int n_parent = -1;
        
        repeat( j, PyList_Size(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 2)) ) {
          n_parent = PyInt_AsLong(PyList_GetItem(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 2), j));
          parents.insert(n_parent);
        }

        int n_obs = p_out_pg->addNode( lit, parents.size() > 0 ? HypothesisNode : ObservableNode, n_parent );
        p_out_pg->nodes[ n_obs ].nodes_appeared        = parents;
        p_out_pg->nodes[ n_obs ].obs_node              = n_parent == -1 ? n_obs : n_parent;
        p_out_pg->nodes[ n_obs ].instantiated_by.axiom = ""; //sexp_obs;
        p_out_pg->nodes[ n_obs ].instantiated_by.where = i;
        p_out_pg->nodes[ n_obs ].lit.wa_number         = PyFloat_AsDouble(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 3));

        if(0 == parents.size())
          nodes_obs.push_back( n_obs );

        vector<int> cnj; cnj.push_back(n_obs);
        pg_hypernode_t hn = p_out_pg->addHyperNode(cnj);
        
        repeat( j, PyList_Size(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 2)) )
          p_out_pg->addEdge(PyInt_AsLong(PyList_GetItem(PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 2), j)), hn, "");
        
        if(ObservableNode == p_out_pg->nodes[n_obs].type) total_observation_cost += p_out_pg->nodes[n_obs].lit.wa_number;
        
        V(4) cerr << TS() << " Extra input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << lit.toString() << endl;
        
      }
    }

    mypyobject_t::cleanTrashCan();
  }

  /* Reasoning on observations. */
  // repeat( i, nodes_obs.size() ) {
  //   if( c.isTimeout() ) return false;
  //   if( ObservableNode != p_out_pg->nodes[ nodes_obs[i] ].type ) continue;
  //   if( "" != p_out_pg->nodes[ nodes_obs[i] ].lit.extra && 0 == p_out_pg->nodes[ nodes_obs[i] ].lit.wa_number ) continue;
  //   if( !instantiateBackwardChainings( p_out_pg, p_out_evc, nodes_obs[i], kb, c ) ) return false;
  // }

  /* Reasoning on abduced propositions. */
  int n_start = 0;
  
  repeat( d, c.depthlimit ) {    
    repeatf( i, 0, p_out_pg->nodes.size() ) {
      if( c.isTimeout() ) return false;
      if( LabelNode == p_out_pg->nodes[i].type ) continue;
      if( "" != p_out_pg->nodes[i].lit.extra && 0 == p_out_pg->nodes[i].lit.wa_number ) continue;
      if( !instantiateBackwardChainings( p_out_pg, p_out_evc, i, kb, c ) ) return false;
    }

    if(n_start == p_out_pg->nodes.size()) { cerr << TS() << "d=" << d << ": no axioms was applied." << endl; break; }
    
    n_start = p_out_pg->nodes.size();
  }
  
  p_out_pg->addHyperNode( nodes_obs );

  /* Add the equality. */  
  foreach( variable_cluster_t::cluster_t, iter_vc, vc.clusters ) {
    if( 2 > iter_vc->second.size() ) continue;
  
    literal_t equality( PredicateSubstitution );
      
    for( unordered_set<store_item_t>::iterator iter_v=iter_vc->second.begin(); iter_vc->second.end()!=iter_v; ++iter_v )
      equality.terms.push_back( *iter_v );
      
    int n_obs = p_out_pg->addNode( equality, LabelGiven == c.objfunc ? LabelNode : ObservableNode );

    p_out_pg->nodes[ n_obs ].obs_node              = n_obs;
    p_out_pg->nodes[ n_obs ].instantiated_by.axiom = ""; //sexp_obs;
    nodes_obs.push_back( n_obs );

    V(4) cerr << TS() << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << equality.toString() << endl;
  }
  
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
  string        log_head = ":-D";

  unordered_set<string> applied_axioms;
  
  while( getline( iss_axiom_set, axiom, '\t' ) ) {

    istringstream iss_axiom( axiom );
    V(5) cerr << TS() << log_head << "instantiate: " << axiom << " for " << endl;
    p_out_pg->instantiated_axioms.insert( axiom );

    for( sexp_reader_t sr(iss_axiom); !sr.isEnd(); ++sr ) {

      if( !sr.stack.isFunctor( "B" ) ) continue;
        
      int i_lf = sr.stack.findFunctorArgument( ImplicationString ), i_name = sr.stack.findFunctorArgument( "name" );
      
      /* For each clause that has the literal n_obs in its right-hand side, */
      logical_function_t lf( *sr.stack.children[i_lf] );
      string             axiom_str = lf.toString();

      if( applied_axioms.end() != applied_axioms.find(axiom_str) ) continue;
      applied_axioms.insert( axiom_str );
      
      V(5) cerr << TS() << axiom_str << " in " << ::join( p_out_pg->nodes[ n_obs ].axiom_used.begin(), p_out_pg->nodes[ n_obs ].axiom_used.end(), "/" ) << "?" << endl;

      if( p_out_pg->nodes[ n_obs ].axiom_used.end() != p_out_pg->nodes[ n_obs ].axiom_used.find( axiom_str ) ) {
        V(5) cerr << TS() << log_head << "Loopy!" << endl;
        continue; /* That's loopy axiom. */
      }

      /* If there are multiple literals in RHS, ...  */
      vector<pair<vector<literal_t>,vector<int> > > rhs_collections;
      
      if( Literal != lf.branches[1].opr ) { if( lf.branches[1].branches.size() > 1 ) {
          /* Multiple RHS literals. */
          string             query    = _createSQLquery( NULL, lf.branches[1], true ); 
          sqlite3_stmt      *p_stmt   = NULL;
          char              *p_val    = NULL;
          uint_t             num_cols = 0;
          unifier_t          theta;
          vector<int>        rhs_candidates;
          vector<literal_t>  rhs_literals;

          if( SQLITE_OK != sqlite3_prepare_v2(p_out_pg->p_db, query.c_str(), -1, &p_stmt, 0) ) { E( "Invalid query: " << query.c_str() ); continue; }
          if( 0 == (num_cols = sqlite3_column_count(p_stmt)) ) sqlite3_finalize(p_stmt);
          else {
            while( SQLITE_ROW == sqlite3_step(p_stmt) ) {              
              repeat( k, lf.branches[1].branches.size() ) {
                if( NULL != (p_val = (char *)sqlite3_column_text(p_stmt, (MaxBasicProp+MaxArguments)*k)) ) {
                  if( !getMGU( &theta, lf.branches[1].branches[k].lit, p_out_pg->nodes[ atoi(p_val) ].lit ) ) goto BED;
                  rhs_candidates.push_back( atoi(p_val) );
                  rhs_literals.push_back(lf.branches[1].branches[k].lit);
                }
              }
              
              {
                unordered_set<int> aobss(rhs_candidates.begin(), rhs_candidates.end());
                if(aobss.size() != rhs_candidates.size()) goto BED;
              }
              
              rhs_collections.push_back(make_pair(rhs_literals, rhs_candidates));
              
            BED:
              theta = unifier_t(); rhs_candidates.clear(); rhs_literals.clear();
              continue;
            }

          }

        } else {
          /* Single RHS literal. */
          vector<int> rhs_single; vector<literal_t> rhs_lf;
          rhs_single.push_back(n_obs); rhs_lf.push_back(lf.branches[1].branches[0].lit);
          rhs_collections.push_back(make_pair(rhs_lf,rhs_single));
        }
        
      } else {
        /* Single RHS literal. */
        vector<int> rhs_single; vector<literal_t> rhs_lf;
        rhs_single.push_back(n_obs); rhs_lf.push_back(lf.branches[1].lit);
        rhs_collections.push_back(make_pair(rhs_lf,rhs_single));
      }

      /* Already applied? */
      if( p_out_pg->p_x_axiom[n_obs][axiom_str] > 0 ) continue;

      if(rhs_collections.size() > 0)
        p_out_pg->p_x_axiom[n_obs][axiom_str] = 1;
      
      repeat(i, rhs_collections.size()) {
        unifier_t theta;
        bool      f_inc = false;

        /* Produce substitution. */
        repeat(j, rhs_collections[i].first.size()) {
          V(5) cerr << TS() << rhs_collections[i].first[j].toString() << "~" << p_out_pg->nodes[rhs_collections[i].second[j]].toString() << endl;
          if( !getMGU( &theta, rhs_collections[i].first[j], p_out_pg->nodes[rhs_collections[i].second[j]].lit ) ) { f_inc = true; }
        }

        if(f_inc) continue;

        V(5) cerr << TS() << theta.toString() << endl;
        
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
        
          //cerr << TS() << c.training_instance.y_lf.toString() << endl;
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

          if( false ) {
            // if( p_out_pg->getNode( &recycles, lit ) ) {
          
            n_backchained = recycles[0];
            p_out_pg->nodes[n_backchained].axiom_used.insert( p_out_pg->nodes[n_obs].axiom_used.begin(), p_out_pg->nodes[n_obs].axiom_used.end() );
            p_out_pg->nodes[n_backchained].axiom_used.insert( axiom_str );
            p_out_pg->nodes[n_backchained].nodes_appeared.insert( n_obs );
            p_out_pg->nodes[n_backchained].nodes_appeared.insert(rhs_collections[i].second.begin(), rhs_collections[i].second.end());
            p_out_pg->nodes[n_backchained].parent_node.insert( n_obs );
          
          } else {

            n_backchained = p_out_pg->addNode( lit, HypothesisNode, n_obs );
        
            /* Set the node parameters. */
            double rhs_cost = 0.0; 
          
            repeat(k, rhs_collections[i].second.size())
              rhs_cost += p_out_pg->nodes[rhs_collections[i].second[k]].lit.wa_number;

            V(5) cerr << TS() << log_head << p_out_pg->nodes[n_backchained].lit.wa_number << "*" << rhs_cost << endl;
            
            p_out_pg->nodes[n_backchained].depth                  = p_out_pg->nodes[n_obs].depth + 1;
            p_out_pg->nodes[n_backchained].obs_node               = p_out_pg->nodes[n_obs].obs_node;
            p_out_pg->nodes[n_backchained].parent_node.insert( n_obs );
            p_out_pg->nodes[n_backchained].instantiated_by.axiom  = -1 != i_name ? (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?") : "";
            p_out_pg->nodes[n_backchained].instantiated_by.where  = j;
            p_out_pg->nodes[n_backchained].axiom_used.insert( p_out_pg->nodes[n_obs].axiom_used.begin(), p_out_pg->nodes[n_obs].axiom_used.end() );
            p_out_pg->nodes[n_backchained].axiom_used.insert( axiom_str );
            p_out_pg->nodes[n_backchained].nodes_appeared         = p_out_pg->nodes[n_obs].nodes_appeared;
            p_out_pg->nodes[n_backchained].nodes_appeared.insert(rhs_collections[i].second.begin(), rhs_collections[i].second.end());
            p_out_pg->nodes[n_backchained].lit.wa_number         *= rhs_cost;
            p_out_pg->nodes[n_backchained].lit.instantiated_by    = p_out_pg->nodes[n_backchained].instantiated_by.axiom;
            p_out_pg->nodes[n_backchained].rhs.insert(n_obs);
            p_out_pg->nodes[n_backchained].rhs.insert(rhs_collections[i].second.begin(), rhs_collections[i].second.end());          

            V(5) cerr << TS() << log_head << "new Literal: " << p_out_pg->nodes[n_backchained].lit.toString() << endl;
          
          }
          
          backchained_literals.push_back( n_backchained );
        
        }

        if( backchained_literals.size() > 0 ) {
          pg_hypernode_t hn = p_out_pg->addHyperNode( backchained_literals );
          repeat( j, rhs_collections[i].second.size() )
            p_out_pg->addEdge( rhs_collections[i].second[j], hn, -1 != i_name ? (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?") : "" );
        }
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

int _createCorefVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, unordered_map<int, unordered_set<int> > *p_out_cu, store_item_t t1, store_item_t t2, bool f_create_new = true) {

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

  if( NULL != p_out_cu ) {
    if( g_store.isConstant(t1) && !g_store.isConstant(t2) ) (*p_out_cu)[t2].insert(t1);
    if( g_store.isConstant(t2) && !g_store.isConstant(t1) ) (*p_out_cu)[t1].insert(t2);
  }
  
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
  else if(2 <= pg.nodes[n].rhs.size()) {
    /* Multiple RHS? */
    lp_constraint_t con_mrhs("mrhs", GreaterEqual, 0);
      
    foreachc(unordered_set<int>, r, pg.nodes[n].rhs)
      con_mrhs.push_back(_createNodeVar(p_out_lp, p_out_lprel, pg, *r), 1.0);

    con_mrhs.push_back(v_h, -1.0 * con_mrhs.vars.size());

    p_out_lp->addConstraint(con_mrhs);
  }
  
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

/* u <=> h_i ^ h_j ^ (forall (x_i=y_i)) */
inline int _createUniVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, unordered_map<int, unordered_set<int> > *p_out_cu, const proof_graph_t &pg, int ni, int nj, const unifier_t &uni ) {
  if( ni > nj ) swap(ni, nj);

  int& v_u = p_out_lprel->nn2uv[ni][nj];
  if( 0 != v_u ) return v_u;

  v_u = p_out_lp->addVariable( lp_variable_t( "u_" ) );
  
  /* u <=> h_i ^ h_j ^ (forall (x_i=y_i)) */
  lp_constraint_t con_u( "", Range, 0, 1 );
  con_u.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, ni ), 1.0 );
  con_u.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, nj ), 1.0 );

  for( uint_t k=0; k<uni.substitutions.size(); k++ ) {
    if( uni.substitutions[k].terms[0] == uni.substitutions[k].terms[1] ) continue;

    /* State the pair (t1,t2) has a possibility to be unified. */
    store_item_t t1 = uni.substitutions[k].terms[0], t2 = uni.substitutions[k].terms[1];
    p_out_cache->evc.add( t1, t2 );
    con_u.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, p_out_cu, t1, t2 ), 1.0 );
  }

  con_u.rhs = 1.0 * con_u.vars.size() - 1;
  con_u.push_back( v_u, -1.0 * con_u.vars.size() );

  p_out_lp->addConstraint( con_u );

  return v_u;
}

/* sc <=> x=y ^ h_i ^ h_j ^ ... ^ h_n */
inline int _createUnifyCooccurringVar( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, unordered_map<int, unordered_set<int> > *p_out_cu, const proof_graph_t &pg, store_item_t ti, store_item_t tj, const vector<int> &literals ) {
  int v_sc    = p_out_lp->addVariable( lp_variable_t( "sc_"+ g_store.claim(ti) + "~" + g_store.claim(tj) + "," + "~" ) );
  int v_coref = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, p_out_cu, ti, tj );

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

  /* Start creating factors... */
  p_out_lp->addVariable( lp_variable_t( "dummy" ) );
  
  sparse_vector_t    v_inf, v_minf; v_inf[ "FIXED" ] = 9999.0; v_minf[ "FIXED" ] = -9999.0;
  unordered_map<int, unordered_set<int> > constants_unifiables;
  variable_cluster_t vc_gold;
  unordered_set<int> vars_unification;

  V(1) cerr << TS() << "Processing score function templates..." << endl;
  
  if( g_ext.isFunctionDefined( "cbScoreFunction" )  ) {
    mypyobject_t::buyTrashCan();

    external_module_context_t emc = {&pg, p_out_lprel, &c};
    mypyobject_t pycon( PyCapsule_New( (void*)&emc, NULL, NULL) );
    mypyobject_t pyarg( Py_BuildValue("(O)", pycon.p_pyobj) );
    mypyobject_t pyret( g_ext.call( "cbScoreFunction", pyarg.p_pyobj ) );
      
    V(1) cerr << TS() << "Constructing the score function..." << endl;

    if( NULL != pyret.p_pyobj ) {
        
      /* [ (["FC_1", "FC_2", ...], "FEATURE_ELEMENT", 1.0), ... ] */
      unordered_map<string, int> fc_map;
        
      repeat( i, PyList_Size(pyret.p_pyobj) ) {

        PyObject        *p_pyfactors     = PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 0), *p_pyfen = PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 1), *p_pyfev = PyTuple_GetItem(PyList_GetItem(pyret.p_pyobj, i), 2);
        string           feature_element_name(PyString_AsString(p_pyfen));
        sparse_vector_t  ve;
        vector<string>   signature;
        factor_t         fc(0 == feature_element_name.find("^") ? AndFactorTrigger : OrFactorTrigger);
        bool             is_vua_included = false;

        repeat( j, PyList_Size(p_pyfactors) ) {
          factor_t       fc_cnf(0 == feature_element_name.find("^") ? OrFactorTrigger : AndFactorTrigger);
          vector<string> local_signature;
          
          repeat(k, PyList_Size(PyList_GetItem(p_pyfactors, j))) {
            char *p_factor_name = PyString_AsString(PyList_GetItem(PyList_GetItem(p_pyfactors, j), k));
            
            if( NULL == p_factor_name ) { W( "Factor name is not a string." ); continue; }

            string         fc_name    = p_factor_name;
            bool           f_negation = false;

            if('!' == fc_name[0]) { f_negation = true; fc_name = fc_name.substr(1); }
            
            switch( fc_name[0] ) {
            case 'p': {
              int  p_id; sscanf( fc_name.substr(1).c_str(), "%d", &p_id );
              local_signature.push_back((f_negation?"!":"") + pg.nodes[p_id].toString());
              fc_cnf.push_back( _createNodeVar(p_out_lp, p_out_lprel, pg, p_id), !f_negation );
              break; }
            case 'c': {
              char var1[32], var2[32]; sscanf( fc_name.substr(1).c_str(), "%s %s", var1, var2 );
              int v_coref = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, _VC(var1), _VC(var2) );
              if( -1 != v_coref ) { fc_cnf.push_back( v_coref, !f_negation ); local_signature.push_back(::toString(f_negation ? "%s!=%s" : "%s=%s", var1, var2)); is_vua_included = true; }
              break; }
            default:
              W( "Unknown factor: " << fc_name );
            }
          }

          /* MAKE SURE THAT WE DON'T HAVE OVERLAP. */
          vector<int>                          sorted_triggers = fc_cnf.triggers; sort(sorted_triggers.begin(), sorted_triggers.end());
          string                               signature_fc    = "fc_"+::join(local_signature.begin(), local_signature.end(), "/");
          unordered_map<string, int>::iterator iter_fcm        = fc_map.find(signature_fc);
          int                                  v_fc            = -1;
          
          if(fc_map.end() == iter_fcm) { v_fc = fc_cnf.apply(p_out_lp, signature_fc, false, false); fc_map[signature_fc] = v_fc; }
          else v_fc        = iter_fcm->second;

          signature.push_back(signature_fc);
          fc.push_back(v_fc);
        }

        if(0 == feature_element_name.find("^")) feature_element_name = feature_element_name.substr(1);
        
        /* MAKE SURE THAT WE DON'T HAVE OVERLAP. */
        vector<int>                          sorted_triggers = fc.triggers; sort(sorted_triggers.begin(), sorted_triggers.end());
        string                               signature_fc    = "ufc_"+::join(signature.begin(), signature.end(), "/");
        unordered_map<string, int>::iterator iter_fcm        = fc_map.find(signature_fc);
        int                                  v_fc            = -1;
        bool                                 f_prohibiting   = -9999 == PyFloat_AsDouble(p_pyfev);
          
        if( fc_map.end() == iter_fcm ) { v_fc = fc.apply(p_out_lp, signature_fc, f_prohibiting, false); fc_map[signature_fc] = v_fc; }
        else v_fc         = iter_fcm->second;

        if(is_vua_included && 0 != feature_element_name.find(PrefixFixedWeight)) vars_unification.insert(v_fc);
        
        if( f_prohibiting || -1 != v_fc ) {
          V(5) cerr << TS() << "New factor: " << ::join(signature.begin(), signature.end(), "/") << ":" << PyString_AsString(p_pyfen) << ":" << PyFloat_AsDouble(p_pyfev) << ":" << is_vua_included << endl;
          if(-1 != v_fc) p_out_lp->variables[ v_fc ].name += "/" + string(PyString_AsString(p_pyfen));
        }
        if( !f_prohibiting && -1 != v_fc ) { p_out_lprel->feature_vector[ v_fc ][ PyString_AsString(p_pyfen) ] += PyFloat_AsDouble(p_pyfev); }

      }

    }
      
    mypyobject_t::cleanTrashCan();
    
  }

  /* Basic component. */
  repeat( i, pg.nodes.size() ) {

    if(LabelNode == pg.nodes[i].type) _createNodeVar(p_out_lp, p_out_lprel, pg, i);
    
    /* Specal treatment for (in)equality. */
    if( g_store.isEqual( pg.nodes[i].lit.predicate, PredicateSubstitution ) && ObservableNode == pg.nodes[i].type ) {
      repeat( j, pg.nodes[i].lit.terms.size() ) {
        repeatf( k, j+1, pg.nodes[i].lit.terms.size() ) {
          p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, pg.nodes[i].lit.terms[j], pg.nodes[i].lit.terms[k] ) ].fixValue( 1.0 );
          vc_gold.add( pg.nodes[i].lit.terms[j], pg.nodes[i].lit.terms[k] );
        } }
    }

    if( g_store.isEqual( pg.nodes[i].lit.predicate, "!=" ) && ObservableNode == pg.nodes[i].type ) {
      repeat( j, pg.nodes[i].lit.terms.size() ) {
        repeatf( k, j+1, pg.nodes[i].lit.terms.size() ) {
          p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, pg.nodes[i].lit.terms[j], pg.nodes[i].lit.terms[k] ) ].fixValue( 0.0 );
          V(5) cerr << TS() << "Non-merge: " << _SC(pg.nodes[i].lit.terms[j]) << "," << _SC(pg.nodes[i].lit.terms[k]) << endl;
        } }
    }
    
    /* Factor: Implication. */
    pg_edge_set_t::const_iterator iter_eg = pg.edges.find(i);
    
    if( pg.edges.end() != iter_eg ) {
      repeat( j, iter_eg->second.size() ) {
        _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_eg->second[j] );
      } }
    
    /* Factor: Conjunction. */
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
  
  
//           repeat( i, pg.nodes.size() ) {

//             /* Factor: prior. */
//             if( ObservableNode == pg.nodes[i].type ) {
//               factor_t fc_prior( IdenticalFactorTrigger );
//               fc_prior.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ) );
              
//               int v_fc_prior = fc_prior.apply( p_out_lp, "fc_prior_" + pg.nodes[i].toString() );
//               p_out_lprel->feature_vector[ v_fc_prior ][ "FC_PRIOR_" + pg.nodes[i].lit.toPredicateArity() ] = WeightedAbduction == c.p_sfunc->tp ? -pg.nodes[i].lit.wa_number : -1;
//             }
            
//             /* Factor: explained. */
//             factor_t fc_explained( OrFactorTrigger );
//             lp_constraint_t con_expimp( "expimp", LessEqual, 0 );

//             pg_edge_set_t::const_iterator iter_eg = pg.edges.find(i);
    
//             if( pg.edges.end() != iter_eg ) {
//               repeat( j, iter_eg->second.size() ) {
//                 double wa_conj_costs  = 0.0;
//                 int    v_conj         = _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_eg->second[j] );
//                 fc_explained.push_back( v_conj );

//                 /* Factor: new assumption. */        
//                 factor_t fc_assume( IdenticalFactorTrigger );
//                 fc_assume.push_back( v_conj );

//                 repeat( k, pg.hypernodes[ iter_eg->second[j] ].size() )
//                   wa_conj_costs += pg.nodes[ pg.hypernodes[ iter_eg->second[j] ][k] ].lit.wa_number;
        
//                 //con_expimp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, pg.hypernodes[ iter_eg->second[j] ][0] ), -1.0 );
//                 con_expimp.push_back( v_conj, -1.0 );
        
//                 int v_fc = fc_assume.apply( p_out_lp, "fc_a_" + ::toString(iter_eg->second[j], "%d") );
//                 p_out_lprel->feature_vector[ v_fc ]["FC_A_" + pg.getEdgeName( i, iter_eg->second[j] ) ] = WeightedAbduction == c.p_sfunc->tp ? -wa_conj_costs : -1;
//               }
//             }

//             /* Find unifiable pairs. */
//             const vector<int> *p_unifiables;
//             pg.getNode( &p_unifiables, pg.nodes[i].lit.predicate, pg.nodes[i].lit.terms.size() );

//             repeat( j, p_unifiables->size() ) {
//               uint_t nj = (*p_unifiables)[j];

//               if( LabelNode == pg.nodes[nj].type ) continue;
//               if( i == nj ) continue;
//               if( c.isTimeout() ) return false;

//               unifier_t uni;
//               if( !getMGU( &uni, pg.nodes[i].lit, pg.nodes[nj].lit ) ) continue;

//               if( WeightedAbduction == c.p_sfunc->tp ) {
//                 if( (pg.nodes[i].lit.wa_number == pg.nodes[nj].lit.wa_number && i > nj) || pg.nodes[i].lit.wa_number > pg.nodes[nj].lit.wa_number ) continue;
//                 if( pg.nodes[i].nodes_appeared.end() != pg.nodes[i].nodes_appeared.find(nj) ||
//                     pg.nodes[nj].nodes_appeared.end() != pg.nodes[nj].nodes_appeared.find(i) ) continue;
//               }

//               int v_uni = _createUniVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, pg, i, nj, uni );
//               fc_explained.push_back( v_uni );

//               if( LabelNode == pg.nodes[i].type ) {
//                 factor_t fc_reward( IdenticalFactorTrigger );
//                 fc_reward.push_back( v_uni );
//                 int v_fcr = fc_reward.apply( p_out_lp, "fc_u_g_" );
//                 p_out_lp->variables[ v_fcr ].obj_val = 9999.0;
//               }
              
//               con_expimp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, nj), -1.0 );
//             }

//             int v_fc_exp = -1;

//             if( LabelNode == pg.nodes[i].type ) {
//               v_fc_exp = fc_explained.apply( p_out_lp, "fc_u_g_" + pg.nodes[i].lit.toString() );
//               if( -1 != v_fc_exp ) p_out_lp->variables[ v_fc_exp ].obj_val = 9999.0;
//             } else {
//               v_fc_exp = fc_explained.apply( p_out_lp, "fc_e_" + pg.nodes[i].lit.toString() );
//               if( -1 != v_fc_exp ) p_out_lprel->feature_vector[ v_fc_exp ]["FC_E_" + pg.nodes[i].lit.toPredicateArity() ] = pg.nodes[i].lit.wa_number;
//             }

//             if( -1 != v_fc_exp ) {
//               lp_constraint_t con_h( "", LessEqual, 0 );
//               con_h.push_back( v_fc_exp, 1.0 );
//               con_h.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ), -1.0 );
//               p_out_lp->addConstraint( con_h );

//               con_expimp.push_back( v_fc_exp, 1.0 );
//               p_out_lp->addConstraint( con_expimp );
//             }
                
//           }
          
//           continue;
//         }
        
  
  if( LabelGiven == c.objfunc ) {
    repeat( i, pg.labelnodes.size() ) {
      int n = pg.labelnodes[i];

      if(g_store.isEqual( pg.nodes[n].lit.predicate, "=" )) {
        repeat( j, pg.nodes[n].lit.terms.size() ) {
          repeatf( k, j+1, pg.nodes[n].lit.terms.size() ) {
            int v_coref = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, pg.nodes[n].lit.terms[j], pg.nodes[n].lit.terms[k], false );

            /* Shouldn't make the variable, because it means that the
               solution is not in the search space.  */
            if( -1 == v_coref ) {
              cerr << TS() << "Not in the candidate hypothesis space: " << _SC(pg.nodes[n].lit.terms[j]) << "=" << _SC(pg.nodes[n].lit.terms[k]) << endl;
              continue;
            }
            
            vc_gold.add( pg.nodes[n].lit.terms[j], pg.nodes[n].lit.terms[k] );
          } }
      }
    }
  }

  /* Impose transitivity constraints on variable equality relation. */
  int num_pair = 0;
  
  for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
    vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );

    repeat( i, variables.size() ) {
      lp_constraint_t con_bestlink( "bl", LessEqual, 1 );
      
      repeatf( j, i+1, variables.size() ) {
        if( c.isTimeout() ) return false;
        
        num_pair++;
        
        store_item_t t1 = variables[i], t2 = variables[j]; if( t1 > t2 ) swap(t1, t2);
        int v_coref = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, t1, t2, false );

        if(-1 == v_coref) continue;
        
        con_bestlink.push_back( v_coref, 1.0 );
        
        if(LabelGiven == c.objfunc && 0 < vc_gold.variables.count(t1) && 0 < vc_gold.variables.count(t2)) {
          if( !vc_gold.isInSameCluster(t1,t2) ) { 
            p_out_lp->variables[ v_coref ].fixValue(0.0); 
          } else if( vc_gold.isInSameCluster(t1,t2) ) {
            p_out_lp->variables[ v_coref ].fixValue(1.0); 
          }
        }

        // if( LossAugmented == c.objfunc && vc_gold.map_v2c.count(t1) > 0 && vc_gold.map_v2c.count(t2) > 0 ) {
        //   if( vc_gold.isInSameCluster(t1,t2) ) {
        //     factor_t fc_loss( AndFactorTrigger );
        //     fc_loss.push_back( v_coref, false );
        //     p_out_lp->variables[ fc_loss.apply( p_out_lp, "fc_loss_" + _SC(t1) + _SC(t2) ) ].obj_val = 1.0;
        //     V(5) cerr << TS() << "Gold unification: " << _SC(t1) + "=" + _SC(t2) << endl;
        //   } else {
        //     factor_t fc_loss( AndFactorTrigger );
        //     fc_loss.push_back( v_coref );
        //     p_out_lp->variables[ fc_loss.apply( p_out_lp, "fc_loss_" + _SC(t1) + _SC(t2) ) ].obj_val = 1.0;
        //     V(5) cerr << TS() << "Gold unification: " << _SC(t1) + "!=" + _SC(t2) << endl;
        //   }
        // }
        
      }

      //	  if(LabelGiven != c.objfunc) p_out_lp->addConstraint( con_bestlink );
    }
  }

  /* Make the factors that include variable unification assumptions relative value. */
  foreach(unordered_set<int>, iter_vua, vars_unification) {
    foreach(sparse_vector_t, iter_v, p_out_lprel->feature_vector[*iter_vua]) {
      if(0 == iter_v->first.find(PrefixFixedWeight)) continue;
      iter_v->second /= num_pair;
    } }

  //num_pair=1;
  repeat(i, p_out_lp->variables.size()) {
    if( 0 == p_out_lp->variables[i].name.find( "fc_loss_") ) p_out_lp->variables[i].obj_val /= num_pair;
  }

  /* Set the feature vector. */
  for( unordered_map<int, sparse_vector_t>::iterator iter_o2v=p_out_lprel->feature_vector.begin(); p_out_lprel->feature_vector.end() != iter_o2v; ++iter_o2v ) {
    for( sparse_vector_t::iterator iter_v=iter_o2v->second.begin(); iter_o2v->second.end()   != iter_v; ++iter_v ) {
      if(0 == iter_v->first.find(PrefixFixedWeight)) {
        p_out_lp->variables[ iter_o2v->first ].obj_val += iter_v->second;
        
        if(!c.ignore_weight) { /* Make sure the weight has a value 1. */
          if(c.f_use_temporal_weights) c.weights[iter_v->first] = 1.0;
          else                         c.p_sfunc->weights[iter_v->first] = 1.0;
        }
      } else
        p_out_lp->variables[ iter_o2v->first ].obj_val += (c.ignore_weight ? 1.0 : (c.f_use_temporal_weights ? c.weights[ iter_v->first ] : c.p_sfunc->weights[ iter_v->first ])) * iter_v->second;
      
      p_out_lprel->input_vector[ iter_v->first ]+= iter_v->second;
    }
  }

  if( BnB == c.method || LocalSearch == c.method ) {
    V(2) cerr << TS() << "enumerateP: Creating transitivity constraints..." << endl;

    for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
      
      vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
      
      for( uint_t i=0; i<variables.size(); i++ ) {
        for( uint_t j=i+1; j<variables.size(); j++ ) {
          for( uint_t k=j+1; k<variables.size(); k++ ) {
            store_item_t ti = variables[i], tj = variables[j], tk = variables[k];
            int
              v_titj        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, ti, tj, false ),
              v_tjtk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, tj, tk, false ),
              v_titk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, &constants_unifiables, ti, tk, false );

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
    
  }

  /* Impose mutual exclusiveness over variable equaility relation. */
  for( unordered_map<store_item_t, unordered_set<int> >::iterator iter_cm=constants_unifiables.begin(); constants_unifiables.end()!=iter_cm; ++iter_cm ) {
    if( 1 == iter_cm->second.size() ) continue;
    
    V(4) cerr << TS() << "MX: " << g_store.claim(iter_cm->first) << ":";

    lp_constraint_t con_con( "mxc", LessEqual, 1.0 );
    
    foreach( unordered_set<store_item_t>, iter_t, iter_cm->second ) {
      con_con.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, iter_cm->first, *iter_t ), 1.0 );
      V(4) cerr << TS() << g_store.claim(*iter_t) << ", ";
    }

    V(4) cerr << endl;
    
    p_out_lp->addConstraint( con_con );
  }
  
  return true;




























  
  
  /* Factor: new assumption factors and explained factors. */
  // repeat( i, pg.nodes.size() ) {
  //   sqlite3_exec( p_db, ("INSERT INTO pehypothesis VALUES ("+ ::toString(i, "%d") + "," + pg.nodes[i].lit.toSQL() +")").c_str(), NULL, 0, NULL );

  //   //repeat( j, pg.nodes[i].lit.terms.size() ) logical_terms.insert( pg.nodes[i].lit.terms[j] );
    
  //   // /* Factor: prior. */
  //   if( g_f_weighted_abduction ? ObservableNode == pg.nodes[i].type : LabelNode != pg.nodes[i].type ) {
  //     factor_t fc_prior( IdenticalFactorTrigger );
  //     fc_prior.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ) );

  //     int v_fc_prior = fc_prior.apply( p_out_lp, "fc_prior_" + pg.nodes[i].toString() );
  //     p_out_lprel->feature_vector[ v_fc_prior ][ "FC_PRIOR_" + pg.nodes[i].lit.toPredicateArity() ] = g_f_weighted_abduction ? -pg.nodes[i].lit.wa_number : -1;
  //   }
    
  //   /* Factor: explained. */
  //   factor_t fc_explained( OrFactorTrigger );
  //   lp_constraint_t con_expimp( "expimp", LessEqual, 0 );

  //   pg_edge_set_t::const_iterator iter_eg = pg.edges.find(i);
    
  //   if( pg.edges.end() != iter_eg ) {
  //     repeat( j, iter_eg->second.size() ) {
  //       double wa_conj_costs  = 0.0;
  //       int    v_conj         = _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_eg->second[j] );
  //       fc_explained.push_back( v_conj );

  //       /* Factor: new assumption. */        
  //       factor_t fc_assume( IdenticalFactorTrigger );
  //       fc_assume.push_back( v_conj );

  //       repeat( k, pg.hypernodes[ iter_eg->second[j] ].size() )
  //         wa_conj_costs += pg.nodes[ pg.hypernodes[ iter_eg->second[j] ][k] ].lit.wa_number;
        
  //       con_expimp.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, pg.hypernodes[ iter_eg->second[j] ][0] ), -1.0 );
        
  //       int v_fc = fc_assume.apply( p_out_lp, "fc_a_" + ::toString(iter_eg->second[j], "%d") );
  //       p_out_lprel->feature_vector[ v_fc ]["FC_A_" + pg.getEdgeName( i, iter_eg->second[j] ) ] = g_f_weighted_abduction ? -wa_conj_costs : -1;
  //     }
  //   }

  //   int v_fc_exp = fc_explained.apply( p_out_lp, "fc_e_" + pg.nodes[i].lit.toString() );
  //   if( -1 != v_fc_exp ) p_out_lprel->feature_vector[ v_fc_exp ]["FC_E_" + pg.nodes[i].lit.toPredicateArity() ] = g_f_weighted_abduction ? pg.nodes[i].lit.wa_number : 1;

  //   // if( -1 != v_fc_exp ) {
  //   //   lp_constraint_t con_h( "fcimp", LessEqual, 0 );
  //   //   con_h.push_back( v_fc_exp, 1.0 );
  //   //   con_h.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ), -1.0 );
  //   //   p_out_lp->addConstraint( con_h );

  //   //   con_expimp.push_back( v_fc_exp, 1.0 );
  //   //   p_out_lp->addConstraint( con_expimp );
  //   // }

  //   /* Factor: Conjunction duty. */
  //   pg_node_hypernode_map_t::const_iterator iter_n2hn = pg.n2hn.find(i);
  //   if( pg.n2hn.end() != iter_n2hn ) {

  //     factor_t fc_conjduty( AndFactorTrigger );

  //     repeat( j, iter_n2hn->second.size() ) {
  //       int v_hn = _createConjVar( p_out_lp, p_out_lprel, pg, i, iter_n2hn->second[j] );
  //       if( 1 == pg.hypernodes[ iter_n2hn->second[j] ].size() ) continue;
      
  //       fc_conjduty.push_back( v_hn, false );
  //     }

  //     if( fc_conjduty.triggers.size() > 0 ) fc_conjduty.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, i ) );

  //     fc_conjduty.apply( p_out_lp, "fc_cjd_" + pg.nodes[i].lit.toString(), true );

  //   }
    
  // }

  PyObject *pymap = PyDict_New();

  foreachc( pg_term_map_t, iter_tm, pg.t2n ) {
    PyObject *pylist = PyList_New( iter_tm->second.size() );
    
    repeat( i, iter_tm->second.size() )
      PyList_SetItem( pylist, i, PyString_FromString( pg.nodes[ iter_tm->second[i] ].toString().c_str() ) );
    
    PyDict_SetItemString( pymap, g_store.claim(iter_tm->first).c_str(), pylist );
  }
  
  /* Factor: variable unification factors */
  //unordered_map<int, unordered_set<int> > constants_unifiables;

  // repeat( i, ord_logical_terms.size() ) {
  //   repeatf( j, i, ord_logical_terms.size() ) {
      
  //     factor_t     fc_unif_evid( OrFactorTrigger );
  //     store_item_t ti = ord_logical_terms[i], tj = ord_logical_terms[j]; if( ti > tj ) swap(ti, tj);

  //     lp_constraint_t con_expunf( "expunf", LessEqual, 0 );
      
  //     /* Collecting the evidence. */
  //     PyObject *pyret = NULL; //g_ext.call( "cbGetUnificationEvidence", Py_BuildValue( "ssO", g_store.claim(ti).c_str(), g_store.claim(tj).c_str(), pymap ) );
      
  //     if( NULL == pyret ) continue;
      
  //     /* pyret must be [(0.1, "", [1,3,5]), (...), ...] */
  //     bool f_including_label = false;
      
  //     repeat( k, PyList_Size(pyret) ) {
  //       if( c.isTimeout() ) return false;

  //       /* Enumerate evidential literals. */
  //       PyObject    *pytuple = PyList_GetItem( pyret, k ), *pylist = PyTuple_GetItem( pytuple, 2 );
  //       double       score   = PyFloat_AsDouble( PyTuple_GetItem( pytuple, 0 ) );
  //       vector<int>  evidential_literals;
  //       string       signature = "";
          
  //       repeat( l, PyList_Size(pylist) ) {
  //         evidential_literals.push_back( PyInt_AsLong( PyList_GetItem( pylist, l ) ) );
  //         signature += pg.nodes[ evidential_literals[l] ].toString() + " ";
  //       }
        
  //       int v_sc = -1; //_createUnifyCooccurringVar( p_out_lp, p_out_lprel, p_out_cache, pg, ti, tj, evidential_literals );
        
  //       V(5) cerr << "Evidence: " << g_store.claim(ti) +"~"+ g_store.claim(tj) << ": " << signature << " (score = " << score << ")" << endl;        
  //       fc_unif_evid.push_back( v_sc );

  //       repeat( l, evidential_literals.size() )
  //         con_expunf.push_back( _createNodeVar(p_out_lp, p_out_lprel, pg, evidential_literals[l]), -1.0 );
        
  //       /* Factor: unification */
  //       if( 0.0 != score ) {
  //         if( -9999 != score ) {
  //           bool f_is_illusion = LabelNode == pg.nodes[evidential_literals[0]].type || LabelNode == pg.nodes[evidential_literals[1]].type;
  //           f_including_label |= f_is_illusion;

  //           factor_t fc_unif( IdenticalFactorTrigger );
  //           fc_unif.push_back( v_sc );

  //           int v_fc_ue = fc_unif.apply( p_out_lp, (f_is_illusion ? "fc_u_g_" : "fc_ue_") + g_store.claim(ti) +","+ g_store.claim(tj) +","+ signature );
            
  //           if( f_is_illusion ) p_out_lp->variables[ v_fc_ue ].obj_val = 9999;
  //           else                p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_EVIDENCE_" + string(PyString_AsString( PyTuple_GetItem( pytuple, 1 ) )) ] = score;

  //         } else {
  //           factor_t fc_unif( AndFactorTrigger );
          
  //           repeat( l, evidential_literals.size() ) 
  //             fc_unif.push_back( _createNodeVar( p_out_lp, p_out_lprel, pg, evidential_literals[l] ) );
          
  //           if( ti != tj ) fc_unif.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, ti, tj ) );
          
  //           fc_unif.apply( p_out_lp, "fc_ue_" + g_store.claim(ti) +","+ g_store.claim(tj) +","+ signature, true );
  //         }
  //       }
          
  //     }

  //     Py_DECREF( pyret );

  //     if( 0 < fc_unif_evid.triggers.size() ) {
  //       if( g_store.isConstant(ti) && !g_store.isConstant(tj) ) constants_unifiables[tj].insert(ti);
  //       if( g_store.isConstant(tj) && !g_store.isConstant(ti) ) constants_unifiables[ti].insert(tj);
  //     }

  //     if( ti != tj && !g_store.isConstant(ti) && !g_store.isConstant(tj) ) {
  //       int v_fc_ue = fc_unif_evid.apply( p_out_lp, (f_including_label ? "fc_u_g_" : "fc_ue_") + g_store.claim(ti) +","+ g_store.claim(tj) );
        
  //       if( -1 != v_fc_ue ) {

  //         /* e1 v e2 v ... v en => ue ^ coref */
  //         // repeat( k, fc_unif_evid.triggers.size() ) {
  //         //   lp_constraint_t con_h( "fcimp", LessEqual, 0 );
  //         //   con_h.push_back( fc_unif_evid.triggers[k], 2.0  );
  //         //   con_h.push_back( v_fc_ue, -1.0 );
  //         //   con_h.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), -1.0 );
  //         //   p_out_lp->addConstraint( con_h );
  //         // }
          
  //         //con_expunf.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), 2.0 );
  //         con_expunf.push_back( v_fc_ue, 2.0 );
  //         p_out_lp->addConstraint( con_expunf );

  //         if( !f_including_label )
  //           p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD" ] = 1.0;
  //         else
  //           p_out_lp->variables[ v_fc_ue ].obj_val = 1.0;
          
  //         // /* Factor: new assumption. */
  //         // if( f_including_label ) {
  //         //   p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) ].obj_val = -1;
  //         //   p_out_lp->variables[ _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) ].name = "fc_u_g_";
  //         // } else {
  //         //   factor_t fc_prior( IdenticalFactorTrigger );
  //         //   fc_prior.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, ti, tj ) );
  //         //   int v_fc_prior = fc_prior.apply( p_out_lp, "fc_ua_" + g_store.claim(ti) +","+ g_store.claim(tj) );
  //         //   p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" ] = -1;
  //         // }
          
  //         // lp_constraint_t con_h( "fcimp", LessEqual, 0 );
  //         // con_h.push_back( v_fc_ue, 1.0 );
  //         // con_h.push_back( _createCorefVar(p_out_lp, p_out_lprel, p_out_cache, ti, tj), -1.0 );
  //         // p_out_lp->addConstraint( con_h );
          
  //         // const vector<int> *p_nodes_ti, *p_nodes_tj;
  //         // pg.getNode( &p_nodes_ti, tj ); pg.getNode( &p_nodes_tj, ti );

  //         // repeat( k, p_nodes_ti->size() ) {
  //         //   int  ni = (*p_nodes_ti)[k];
  //         //   cerr << pg.nodes[ni].toString() << g_store.claim( tj ) << pg.nodes[ni].type << endl;
  //         //   if( ObservableNode == pg.nodes[ ni ].type ) { cerr << "yyyy" << endl; }
  //         //     repeat( l, p_nodes_tj->size() ) {
  //         //     int nj = (*p_nodes_tj)[l];
  //         //     // if( ObservableNode == pg.nodes[ ni ].type ) p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" + pg.nodes[ ni ].lit.toPredicateArity() ]  = -1;
  //         //     // if( ObservableNode == pg.nodes[ nj ].type ) p_out_lprel->feature_vector[ v_fc_prior ][ "FC_UNIFY_PRIOR" + pg.nodes[ nj ].lit.toPredicateArity() ]  = -1;
  //         //     if( ObservableNode == pg.nodes[ ni ].type ) p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD_FOR_" + pg.nodes[ ni ].lit.toPredicateArity() ]  = 1;
  //         //     if( ObservableNode == pg.nodes[ nj ].type ) p_out_lprel->feature_vector[ v_fc_ue ][ "FC_UNIFY_FOUND_EVD_FOR_" + pg.nodes[ nj ].lit.toPredicateArity() ]  = 1;
  //         //   } }

  //       }
  //     }
      
  //   } }

  // sqlite3_close( p_db );
  
  Py_DECREF( pymap );
  
  /* Impose mutual exclusiveness over variable equaility relation. */
  for( unordered_map<store_item_t, unordered_set<int> >::iterator iter_cm=constants_unifiables.begin(); constants_unifiables.end()!=iter_cm; ++iter_cm ) {
    if( 1 == iter_cm->second.size() ) continue;
    
    V(4) cerr << "MX: " << g_store.claim(iter_cm->first) << ":";

    lp_constraint_t con_con( "mxc", LessEqual, 1.0 );
    
    foreach( unordered_set<store_item_t>, iter_t, iter_cm->second ) {
      con_con.push_back( _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, iter_cm->first, *iter_t ), 1.0 );
      V(4) cerr << g_store.claim(*iter_t) << ", ";
    }

    V(4) cerr << endl;
    
    p_out_lp->addConstraint( con_con );
  }
  
  /* Impose transitivity constraints on variable equality relation. */
  for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
    vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
    
    repeat( i, variables.size() ) {
      repeatf( j, i+1, variables.size() ) {
        if( c.isTimeout() ) return false;
        
        store_item_t t1 = variables[i], t2 = variables[j]; if( t1 > t2 ) swap(t1, t2);
        _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, t1, t2, false );
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
              v_titj        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, ti, tj, false ),
              v_tjtk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, tj, tk, false ),
              v_titk        = _createCorefVar( p_out_lp, p_out_lprel, p_out_cache, NULL, ti, tk, false );

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
      else                           p_out_lp->variables[ iter_o2v->first ].obj_val += (c.ignore_weight ? 1.0 : (c.p_sfunc->weights[ iter_v->first ]) * iter_v->second);
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

void function::convertLPToHypothesis( logical_function_t *p_out_h, sparse_vector_t *p_out_fv, const lp_inference_cache_t &cache, bool f_vector_weighting ) {

  p_out_h->opr = AndOperator;
  p_out_h->branches.clear();
  
  for( uint_t i=0; i<cache.pg.nodes.size(); i++ ) {
    unordered_map<int, int>::const_iterator iter_v = cache.lprel.n2v.find(i);
    if( cache.lprel.n2v.end() == iter_v ) continue;

    if( ObservableNode == cache.pg.nodes[i].type && g_store.isEqual( cache.pg.nodes[i].lit.predicate, PredicateSubstitution ) ) continue;
    if( LabelNode == cache.pg.nodes[i].type ) continue;
                                          
    if( 0.5 < cache.lp.variables[ iter_v->second ].optimized )
      p_out_h->branches.push_back( logical_function_t( cache.pg.nodes[i].lit ) );
  }

  /* Create equality literals. */
  variable_cluster_t vc;
  foreachc( pairwise_vars_t, iter_t1, cache.lprel.pp2v )
    for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
      if( 0.5 < cache.lp.variables[ iter_t2->second ].optimized )
        vc.add( iter_t1->first, iter_t2->first );
    }

  foreach( variable_cluster_t::cluster_t, iter_vc, vc.clusters )
    if( iter_vc->second.size() > 1) {
      literal_t equality( PredicateSubstitution );
      
      for( unordered_set<store_item_t>::iterator iter_v=iter_vc->second.begin(); iter_vc->second.end()!=iter_v; ++iter_v )
        equality.terms.push_back( *iter_v );
      
      p_out_h->branches.push_back( logical_function_t( equality ) );
    }
  
  if( NULL != p_out_fv ) {
    repeat( i, cache.lp.variables.size() ) {
      if( 0.5 < cache.lp.variables[i].optimized ) {
        if( cache.lprel.feature_vector.end() != cache.lprel.feature_vector.find(i) ) {
          foreachc( sparse_vector_t, iter_fv, cache.lprel.feature_vector.find(i)->second ) {
            double f_coefficient = 1.0;
            if(f_vector_weighting && cache.loss.weighting.find(i) != cache.loss.weighting.end())
              f_coefficient = cache.loss.weighting.find(i)->second;

            size_t ps = iter_fv->first.find(PrefixInvisibleElement);
            if(0 == ps || 1 == ps) continue;
            
            (*p_out_fv)[ iter_fv->first ] += f_coefficient * iter_fv->second;
          }
        }
      }
      // if( cache.lprel.feature_vector.end() != cache.lprel.feature_vector.find(i) ) {
      //   foreachc( sparse_vector_t, iter_fv, cache.lprel.feature_vector.find(i)->second )
      //     if( 0 != iter_fv->first.find( "NOT" ) ) (*p_out_fv)[ iter_fv->first ] += (f_vector_weighting ? mget(cache.loss.weighting, (int&)i, 1.0) : 1.0) * iter_fv->second;
      // }

      // if( f_vector_weighting ) {
      //   for( unordered_map<int, double>::const_iterator iter=cache.loss.weighting.begin(); iter!=cache.loss.weighting.(); iter++ )
      //     cerr << iter->first << ":" << iter->second << endl;
      // }
      
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
  V(5) cerr << TS() << "compileKB: Sorting the hash keys..." << endl;
  
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
  V(1) cerr << TS() << "readPrecompiledKB: Loading header..." << endl;
  
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

store_item_t _findRepr( unordered_set<store_item_t> vars ) {
  foreach( unordered_set<store_item_t>, iter_v, vars )
    if( g_store.isConstant( *iter_v ) ) return *iter_v;
  foreach( unordered_set<store_item_t>, iter_v, vars )
    if( !g_store.isUnknown( *iter_v ) ) return *iter_v;
  return *vars.begin();
}

void proof_graph_t::printGraph( const linear_programming_problem_t &lpp, const lp_problem_mapping_t &lprel, const string& property, ostream* p_out ) const {

  (*p_out) << "<proofgraph" << ("" != property ? (" " + property) : "") << ">" << endl;
  
  for( uint_t i=0; i<nodes.size(); i++ ) {
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find(i);
    if( lprel.n2v.end() == iter_v ) continue;
    
    (*p_out) << "<literal id=\""<< i <<"\" type=\""<< nodes[i].type <<"\" active=\""<< (lpp.variables[ iter_v->second ].optimized < 0.5 ? "no" : "yes") <<"\">"
         << nodes[i].toString() << "</literal>" << endl;

    const vector<int> *p_unifiables;
    getNode( &p_unifiables, nodes[i].lit.predicate, nodes[i].lit.terms.size() );

    repeat( j, p_unifiables->size() ) {
      uint_t nj = (*p_unifiables)[j];

      if(g_store.isEqual(nodes[i].lit.predicate, "!=")) continue;
      if( i == nj ) continue;
      
      unordered_map<int, int>::const_iterator iter_vj = lprel.n2v.find(nj);
      if( lprel.n2v.end() == iter_vj ) continue;

      vector<string> subs;
      unifier_t uni;
      if( !getMGU( &uni, nodes[i].lit, nodes[nj].lit ) ) continue;

      bool f_fails     = false;
      int  num_unified = 0;
      
      repeat( k, uni.substitutions.size() ) {
        store_item_t t1 = uni.substitutions[k].terms[0], t2 = uni.substitutions[k].terms[1]; if( t1 > t2 ) swap(t1, t2);
        int v_sxy = _getCorefVar(t1, t2, lprel);

        if( t1 == t2 ) continue;
        if( -1 == v_sxy ) { f_fails = true; continue; }
        if( lpp.variables[ v_sxy ].optimized < 0.5 ) { f_fails = true; } else { num_unified++; subs.push_back( toString("%s=%s", g_store.claim(t1).c_str(), g_store.claim(t2).c_str()) ); }
      }

      f_fails |= lpp.variables[ iter_v->second ].optimized < 0.5;
      f_fails |= lpp.variables[ iter_vj->second ].optimized < 0.5;

      (*p_out) << "<unification l1=\""<< i <<"\" l2=\""<< nj << "\" unifier=\""<< ::join(subs.begin(), subs.end(), ", ") << "\" active=\""<< ((lpp.variables[ iter_v->second ].optimized > 0.5 && lpp.variables[ iter_vj->second ].optimized > 0.5) && (num_unified >= 1 || !f_fails) ? "yes" : "no") << "\" />" << endl;
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

      (*p_out) << "<explanation name=\""<< edges_name.find(iter_eg->second[i])->second <<"\" active=\""<< (0.5 < lpp.variables[ iter_v->second ].optimized && hypernodes[ iter_eg->second[i] ].size() == n_active ? "yes" : "no") <<"\" axiom=\"\">";
      
      for( uint_t j=0; j<hypernodes[ iter_eg->second[i] ].size(); j++ ) {
        (*p_out) << hypernodes[ iter_eg->second[i] ][j];
        if( j < hypernodes[ iter_eg->second[i] ].size()-1 ) (*p_out) << " ^ ";
      }

      (*p_out) << " => " << iter_eg->first << "</explanation>" << endl;
      
    }
        
  }

  (*p_out) << "</proofgraph>" << endl;
  
}

/* Thanks for https://gist.github.com/240957. */
sexp_reader_t &sexp_reader_t::operator++() {

  bool f_comment = false;
  char last_c    = 0;
  
  while( m_stream.good() ) {

    char c = m_stream.get();

    if( '\n' == c ) n_line++;
    
    if( '\\' != last_c && ';' == c ) { f_comment = true; continue; }
    if( f_comment ) {
      if( '\n' == c ) f_comment = false;
      continue;
    }

    switch( m_stack.back()->type ) {
    
    case ListStack: {
      if( '(' == c ) { m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); }
      else if( ')' == c ) {
        _A( m_stack.size() >= 2, "Syntax error at " << n_line << ": too many parentheses." << endl << m_stack.back()->toString() );
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

