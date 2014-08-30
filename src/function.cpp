#include "defs.h"

#include <time.h>
#include <stdlib.h>
#include <math.h>

#include <fstream>
#include <algorithm>
#include <map>

using namespace function;

bool _query(void (*p_callback)(const vector<int>&, void*),
            void *p_context, const proof_graph_t &pg, int n_current_pg_size, const inference_configuration_t &c, const score_function_t::function_unit_t &unit,
            vector<int> *p_stack=NULL, uint_t current_stack=0, bool f_mirror=false, bool f_ignoreCond=false) {

  if(c.isTimeout()) return false;
  
  /* FOR EACH CONJUNCTION, */
  if(NULL == p_stack) {
    if(OrOperator == unit.lf.opr) {
      repeat(i, unit.lf.branches.size()) {}
    } else if(AndOperator == unit.lf.opr) {
      vector<int> s;
      if(!_query(p_callback, p_context, pg, n_current_pg_size, c, unit, &s, 0, f_mirror, f_ignoreCond))
        return false;
    }

    return true;
  }


  vector<string> conditions;
  vector<int> &stack = *p_stack;
  unordered_set<int> set_stack(stack.begin(), stack.end());

  if(current_stack == unit.lf.branches.size()) {
    if(c.isTimeout()) return false;

    /* CALL. */
    (*p_callback)(stack, p_context);
    return true;
  }    
  
  repeat(cc, current_stack) {
    repeat(i, unit.lf.branches[cc].lit.terms.size()) {
      if(unit.lf.branches[cc].lit.terms[i] == "_") continue;
        
      repeat(j, unit.lf.branches[current_stack].lit.terms.size()) {
        if(unit.lf.branches[current_stack].lit.terms[j] == "_") continue;
        
        if(unit.lf.branches[cc].lit.terms[i] == unit.lf.branches[current_stack].lit.terms[j]) {
          const string &s = unit.lf.branches[current_stack].lit.toPredicateArity();
          conditions.push_back(::toString("%s:%d:%s", ('?' == s[0] ? s.substr(1) : s).c_str(), j, pg.nodes[stack[cc]].lit.terms[i].c_str()));
        }
      } }
  }

  if(f_ignoreCond)
    conditions.clear();
  
  if(0 == conditions.size()) {
    
    /* NO CONDITIONS. JUST ENUMERATE ALL LITERALS. */
    const vector<int> *p_nodes;
    const string &s = unit.lf.branches[current_stack].lit.predicate.toString();
    
    if(pg.getNode(&p_nodes, '?' == s[0] ? s.substr(1) : s, unit.lf.branches[current_stack].lit.terms.size())) {
      repeat(i, p_nodes->size()) {
        if((*p_nodes)[i] >= n_current_pg_size) continue; /* HEY, MAN. */
        if(0 < set_stack.count((*p_nodes)[i])) continue; /* DO NOT GO INTO DEEPER IF IT'S ALREADY INVOLVED. */

        /* CHECK IF THESE ARE UNIFIABLE OR NOT. */
        bool f_unifiable = true;
        repeat(j, pg.nodes[(*p_nodes)[i]].lit.terms.size()) {
          if(unit.lf.branches[current_stack].lit.terms[j] != pg.nodes[(*p_nodes)[i]].lit.terms[j] &&
             unit.lf.branches[current_stack].lit.terms[j].isConstant() && pg.nodes[(*p_nodes)[i]].lit.terms[j].isConstant())
            { f_unifiable=false; break; }
        }

        if(!f_unifiable) continue;
        
        vector<int> next_stack(stack);
        next_stack.push_back((*p_nodes)[i]);
        if(!_query(p_callback, p_context, pg, n_current_pg_size, c, unit, &next_stack, current_stack+1, f_mirror, f_ignoreCond)) return false;
      }
    }
    
  } else {
    


    /* ENUMERATE ALL LITERALS THAT SATISFY THE CONDITIONS. */
    hash<string>       hashier;
    unordered_set<int> satisfied_nodes;
    
    repeat(i, conditions.size()) {
      proof_graph_t::eqhash_t::const_iterator j = pg.eqhash.find(hashier(conditions[i]));

      /* IF THERE ARE NO LITERALS THAT SATISFY THE CONDITIONS, ABORT THE WHOLE PROCESS. */
      if(pg.eqhash.end() == j) { satisfied_nodes.clear(); break; }
      
      const vector<int> &nodes = j->second;
      unordered_set<int> new_satisfied_nodes;
      
      repeat(k, nodes.size()) {
        if(nodes[k] >= n_current_pg_size) continue; /* HEY, MAN. */

        if(0 == i) new_satisfied_nodes.insert(nodes[k]);
        else if(0 < satisfied_nodes.count(nodes[k]))
          new_satisfied_nodes.insert(nodes[k]);
      }

      satisfied_nodes = new_satisfied_nodes;
    }

    foreach(unordered_set<int>, i, satisfied_nodes) {
      if(0 < set_stack.count(*i)) continue; /* DO NOT GO INTO DEEPER IF IT'S ALREADY INVOLVED. */
      
      vector<int> next_stack(stack);
      next_stack.push_back(*i);
      if(!_query(p_callback, p_context, pg, n_current_pg_size, c, unit, &next_stack, current_stack+1, f_mirror, f_ignoreCond)) return false;
    }
  }

  if(!f_mirror && (unit.lf.branches[current_stack].lit.predicate == "=" || unit.lf.branches[current_stack].lit.predicate == "!=")) {
    score_function_t::function_unit_t swapped_unit(unit.name, unit.lf, unit.weight);
    swap(swapped_unit.lf.branches[current_stack].lit.terms[0], swapped_unit.lf.branches[current_stack].lit.terms[1]);
    if(!_query(p_callback, p_context, pg, n_current_pg_size, c, swapped_unit, &stack, current_stack, true, f_ignoreCond)) return false;
  }
  
  return true;
}

bool function::enumeratePotentialElementalHypotheses(proof_graph_t *p_out_pg, const logical_function_t &obs, const knowledge_base_t &kb, const inference_configuration_t &c) {

  if(!p_out_pg->f_obs_processed) {
    
    /* ADD OBSERVED LITERALS INTO THE GRAPH. */
    vector<int>              nodes_obs;
    vector<const literal_t*> literals_obs;
    double                   total_observation_cost = 0;
    
    obs.getAllLiterals( &literals_obs );

    /* COMPOSE OBSERVED VARIABLE CLUSTER. */
    repeat( i, literals_obs.size() ) {
      pg_node_type_t type_node = LabelGiven != c.objfunc || i < c.initial_label_index ? ObservableNode : LabelNode;
      if((LabelNode == type_node || ObservableNode == type_node) && literals_obs[i]->predicate == "=") {
        repeat( j, literals_obs[i]->terms.size() ) {
          repeatf( k, j+1, literals_obs[i]->terms.size() ) {
            p_out_pg->vc_observed.add(literals_obs[i]->terms[j], literals_obs[i]->terms[k]);
          } }
      }
    }
    
    repeat( i, literals_obs.size() ) {
      pg_node_type_t type_node = LabelGiven != c.objfunc || i < c.initial_label_index ? ObservableNode : LabelNode;
      
      if(literals_obs[i]->predicate == "=" || literals_obs[i]->predicate == "!=") {
        if(LabelNode == type_node) continue;
        
        repeat( j, literals_obs[i]->terms.size() ) {
          repeatf( k, j+1, literals_obs[i]->terms.size() ) {
            if((literals_obs[i]->predicate == "=" && !p_out_pg->vc_observed.isInSameCluster(literals_obs[i]->terms[j], literals_obs[i]->terms[k])) ||
               (literals_obs[i]->predicate == "!=" && p_out_pg->vc_observed.isInSameCluster(literals_obs[i]->terms[j], literals_obs[i]->terms[k]))) {
                 W("Inconsistent: " << literals_obs[i]->toString());
                 continue;
               }

            store_item_t t1 = literals_obs[i]->terms[j], t2 = literals_obs[i]->terms[k];
            if(t1 > t2) swap(t1, t2);
            
            int n_obs = p_out_pg->addNode(literal_t(store_item_t(literals_obs[i]->predicate), t1, t2), type_node);
            nodes_obs.push_back( n_obs );
            V(4) cerr << TS() << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << literals_obs[i]->toString() << endl;
          } }
      
        continue;
      }
    
      int n_obs = p_out_pg->addNode(*literals_obs[i], type_node);

      if("" == p_out_pg->nodes[ n_obs ].lit.extra)
        p_out_pg->nodes[ n_obs ].lit.wa_number = 1.0;
        
      p_out_pg->nodes[ n_obs ].instantiated_by.axiom = ""; //sexp_obs;
      p_out_pg->nodes[ n_obs ].instantiated_by.where = i;
      p_out_pg->nodes[ n_obs ].lit.id                = n_obs;
      nodes_obs.push_back( n_obs );

      total_observation_cost += p_out_pg->nodes[n_obs].lit.wa_number;
    
      V(4) cerr << TS() << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << literals_obs[i]->toString() << endl;
    }

    /* Make it relative cost. */
    repeat( i, nodes_obs.size() ) {
      //p_out_pg->nodes[nodes_obs[i]].lit.wa_number /= total_observation_cost;
      V(4) cerr << TS() << " Revised input: Type=" << p_out_pg->nodes[nodes_obs[i]].type << ", " << p_out_pg->nodes[nodes_obs[i]].lit.toString() << ", " << p_out_pg->nodes[nodes_obs[i]].lit.wa_number << endl;

      repeat(j, p_out_pg->nodes[nodes_obs[i]].lit.terms.size())
        p_out_pg->observed_variables.insert(p_out_pg->nodes[nodes_obs[i]].lit.terms[j]);
    }

    p_out_pg->addHyperNode(nodes_obs);
    p_out_pg->f_obs_processed = true;    
  }
  
  /* START REASONING. */
  uint_t n_start = c.n_start;
  int    d       = 0;
  
  /* IDENTIFY SET OF AXIOMS THAT LEADS TO UNIFICATION. */
  unordered_set<int> prominent_axioms;

  cerr << TS() << "Identifying set of prominent axioms..." << endl;

  if(-1 != kb.context_pruning_cdb)
    cerr << TS() << "According to the context..." << endl;

  if(!c.no_pruning) {
    vector<const literal_t*>   literals_obs;
    unordered_map<string, int> inferred_counts;
    unordered_map<string, unordered_set<int> > path_to;

    obs.getAllLiterals( &literals_obs );

//#pragma omp parallel for
    repeat(i, literals_obs.size()) {
      V(2) cerr << TS() << "Start iterative deeping for " << literals_obs[i]->toString() << "..." << endl;

      unordered_map<string, unordered_set<int> > axiom_set;

#pragma omp critical
      kb.getAbductiveHypotheses(&axiom_set, literals_obs[i]->toPredicateArity());

      /* CONTEXT-BASED PRUNING. */
      /* WE OMIT THE PRUNING FOR GENERAL PREDICATESS LIKE "REL", "NN" ETC. */
      //if(literals_obs[i]->predicate != getWord(literals_obs[i]->predicate)) {
        kb.pruneAxioms(&axiom_set, literals_obs);
      //}

      /* START ITERATIVE DEEPING. */
      for(int depth=0; depth<(int)(c.depthlimit-1); depth++) {
        V(2) cerr << TS() << "d = " << (1+depth) << "." << endl;

        unordered_map<string, unordered_set<int> > my_axiom_set = axiom_set;
        unordered_set<string> already_explored;
        int num_total = 0, num_pruned = 0, num_processed = 0;
        double t = getTimeofDaySec();

        for(unordered_map<string, unordered_set<int> >::const_iterator j=my_axiom_set.begin(); my_axiom_set.end()!=j; ++j) {
          if(getTimeofDaySec() - t >= 1.0) {
            cerr << TS() << num_processed << "/" << my_axiom_set.size() << endl;
            t = getTimeofDaySec();
          }

          num_processed++;
          
          if(0 < already_explored.count(j->first)) continue;
          already_explored.insert(j->first);

          /* GET THE DEEPER HYPOTHESES. */
          unordered_map<string, unordered_set<int> > fresh_axiom_set;

#pragma omp critical
          kb.getAbductiveHypotheses(&fresh_axiom_set, j->first);

          int axiom_size = fresh_axiom_set.size();
          num_total += axiom_size;

          //if(j->first != getWord(j->first)) {
            kb.pruneAxioms(&fresh_axiom_set, literals_obs);
          //}

          num_pruned += axiom_size - fresh_axiom_set.size();

          for(unordered_map<string, unordered_set<int> >::iterator k=fresh_axiom_set.begin(); fresh_axiom_set.end()!=k; ++k) {
            axiom_set[k->first].insert(j->second.begin(), j->second.end());
            axiom_set[k->first].insert(k->second.begin(), k->second.end());
          }
        }

        V(2) cerr << TS() << "Very good." << endl;

        if(-1 != kb.context_pruning_cdb) {
          V(2) cerr << TS() << num_pruned << " axioms out of "<< num_total <<" were pruned." << endl;
        }
      }

#pragma omp critical
      {
        inferred_counts[literals_obs[i]->toPredicateArity()]++;

        for(unordered_map<string, unordered_set<int> >::iterator j=axiom_set.begin(); axiom_set.end()!=j; ++j) {
          inferred_counts[j->first]++;
          path_to[j->first].insert(j->second.begin(), j->second.end());
        }
      }
    }

    for(unordered_map<string, int>::iterator i=inferred_counts.begin(); inferred_counts.end()!=i; ++i) {
      V(5) cerr << TS() << i->first << ":" << i->second << ":" << join(path_to[i->first].begin(), path_to[i->first].end(), "%d", ",") << endl;
      if(i->second <= 1) continue;

      prominent_axioms.insert(path_to[i->first].begin(), path_to[i->first].end());
    }

//    /* COUNT THE OCCURENCE OF LITERALS. */
//    for(unordered_map<string, unordered_set<int> >::iterator j=axiom_set.begin(); axiom_set.end()!=j; ++j) {
//      if(++inferred_counts[j->first] >= 2)
//        prominent_axioms.insert(j->second.begin(), j->second.end());
//    }
//
    cerr << TS() << prominent_axioms.size() << " prominent axioms were identified." << endl;
  } else
    cerr << TS() << "Nope." << endl;

  while(true) {
    uint_t current_node_size = p_out_pg->nodes.size(),
      num_used_axiom_tokens = p_out_pg->used_axiom_tokens.size(), num_used_axiom_types = p_out_pg->used_axiom_types.size();
    int num_filtered_out = 0, n_local_start = current_node_size;
    double stime = getTimeofDaySec();

    repeatf(i, n_start, current_node_size) {
      if(getTimeofDaySec() - stime >= 1.0) { cerr << TS() << "ePEH: " << (i-n_start) << "/" << (current_node_size-n_start) << endl; stime = getTimeofDaySec(); }

      if(c.isTimeout()) continue; // return false;
      if(p_out_pg->nodes[i].f_removed) continue;
      if(!instantiateBackwardChainings(p_out_pg, current_node_size, i, kb, prominent_axioms, c, &num_filtered_out)) continue; //return false;

      V(4) cerr << TS() << p_out_pg->nodes[i].toString() << ": " << (p_out_pg->nodes.size() - n_local_start) << " literals were produced." << endl;
      n_local_start = p_out_pg->nodes.size();
    }

    if(c.isTimeout()) return false;

    if(n_start == p_out_pg->nodes.size()) { cerr << TS() << "d=" << (1+d) << ": no axioms were applied." << endl; break; }
    
    cerr << TS() << "d=" << (1+d) << ": "<< (p_out_pg->used_axiom_tokens.size() - num_used_axiom_tokens) <<" axioms were applied" <<
      " (new "<< (p_out_pg->used_axiom_types.size() - num_used_axiom_types) <<" types of axioms were instantiated, " <<
      num_filtered_out << " axioms were filtered out)." << endl;
    cerr << TS() << "d=" << (1+d) << ": "<< (p_out_pg->nodes.size() - current_node_size) <<" literals were generated." << endl;

    n_start = current_node_size;
    d++;
  };

  p_out_pg->n_start = n_start;
  p_out_pg->produceUnificationAssumptions(kb, c);

  /* PROCESS EQUALITIES IN LABEL NODES. */
  if(!p_out_pg->f_lbl_processed) {
    p_out_pg->f_lbl_processed = true;
    
    /* ADD OBSERVED LITERALS INTO THE GRAPH. */
    vector<int>              nodes_obs;
    vector<const literal_t*> literals_obs;
    
    obs.getAllLiterals( &literals_obs );
  
    repeat( i, literals_obs.size() ) {
      pg_node_type_t type_node = LabelGiven != c.objfunc || i < c.initial_label_index ? ObservableNode : LabelNode;
      
      if(!(LabelNode == type_node && (literals_obs[i]->predicate == "=" || literals_obs[i]->predicate == "!="))) continue;
      
      repeat( j, literals_obs[i]->terms.size() ) {
        repeatf( k, j+1, literals_obs[i]->terms.size() ) {
          if((literals_obs[i]->predicate == "=" && !p_out_pg->vc_observed.isInSameCluster(literals_obs[i]->terms[j], literals_obs[i]->terms[k])) ||
             (literals_obs[i]->predicate == "!=" && p_out_pg->vc_observed.isInSameCluster(literals_obs[i]->terms[j], literals_obs[i]->terms[k]))) {
            W("Inconsistent: " << literals_obs[i]->toString());
            continue;
          }
            
          /* ADD IT IF IT ALREADY EXISTS. */
          store_item_t t1 = literals_obs[i]->terms[j], t2 = literals_obs[i]->terms[k];
          if(t1 > t2) swap(t1, t2);
            
          int n_obs = literals_obs[i]->predicate == "=" ?
            p_out_pg->getSubNode(t1, t2) :
            p_out_pg->getNegSubNode(t1, t2);
            
          if(-1 == n_obs) {
            W("Not in search space: " << literals_obs[i]->terms[j] << literals_obs[i]->predicate << literals_obs[i]->terms[k]);

            if(literals_obs[i]->predicate == "=" && !c.use_only_user_score)
              p_out_pg->f_label_not_found = true;
            
            if(literals_obs[i]->predicate == "!=")
              n_obs = p_out_pg->addNode(literal_t(store_item_t(literals_obs[i]->predicate), t1, t2), type_node);
          } else {
            /* IF EQUALITY IS DERIVED FROM ONLY OBSERVATIONS, ASSUME THAT WE DON'T HAVE THE LABEL IN SEARCH SPACE. */
            if(literals_obs[i]->predicate == "=" && !c.use_only_user_score) {
              const vector<int> *p_hypernodes;
              bool               f_found_except_mention = false;
            
              if(p_out_pg->getAssociatedHyperNode(&p_hypernodes, n_obs)) {
                repeat(x, p_hypernodes->size()) {
                  //cerr << "HELLO! " << p_out_pg->hypernodeToString((*p_hypernodes)[x]) << endl;
                  if(string::npos == p_out_pg->hypernodeToString((*p_hypernodes)[x]).find("mention")) { f_found_except_mention = true; break; }
                }
              }

              if(!f_found_except_mention) p_out_pg->f_label_not_found = true;
            }
            
            p_out_pg->nodes[n_obs].type = type_node;
            V(4) cerr << TS() << " Input: Type=" << p_out_pg->nodes[ n_obs ].type << ", " << literals_obs[i]->toString() << endl;
          }
        } }
      
      continue;
    }

  }
  
  return true;
}

bool function::instantiateBackwardChainings(proof_graph_t *p_out_pg, int n_current_pg_size, int n_obs, const knowledge_base_t &kb, const unordered_set<int> &prominent_axioms, const inference_configuration_t &c, int *p_num_filtered_out) {
  if(p_out_pg->nodes[n_obs].lit.predicate.isEqual("nsubj")) return true;
  
  //if( p_out_pg->nodes[ n_obs ].lit.wa_number >= 9999.0) return true;
  if( p_out_pg->nodes[ n_obs ].depth > (signed)c.depthlimit-1 ) return true;
//  if( p_out_pg->nodes[ n_obs ].num_instantiated > 100) return true;
  
  vector<knowledge_base_t::axiom_t> axioms;
  string         key_pa = p_out_pg->nodes[n_obs].lit.toPredicateArity();

//  if(0 < p_out_pg->backchained_on.count(key_pa)) return true;
//
//  p_out_pg->backchained_on.insert(key_pa);

  string o_key_pa = key_pa;

  if(kb.isSearchWithConstant(key_pa)) {
    repeat(i, p_out_pg->nodes[n_obs].lit.terms.size()) {
      if("event/4" == o_key_pa && 2-1 != i) continue;

      if(p_out_pg->nodes[n_obs].lit.terms[i].isConstant())
        key_pa += "/" + p_out_pg->nodes[n_obs].lit.terms[i].toString();
    }

    V(5) cerr << TS() << "SEARCH WITH CONSTANT PREDICATE: " << key_pa << endl;
  }

  V(5) cerr << TS() << "Target: " << p_out_pg->nodes[n_obs].toString() << endl;

  if(!kb.search(&axioms, key_pa, prominent_axioms, p_num_filtered_out, !c.no_pruning)) return true;
  if(c.isTimeout()) return false;

  V(5) cerr << TS() << "Axioms: " << axioms.size() << endl;
  
  /* For each unifiable axiom, */
  string        log_head = ":-D";
  int num_instantiated = 0;

  unordered_set<string> applied_axioms;
  unordered_map<string, vector<pair<vector<literal_t>,vector<int> > > > cache_rhs_collections;
  
  double stime = getTimeofDaySec();

  //cerr << "B:" << p_out_pg->nodes[n_obs].toString() << ":" << axioms.size() << endl;

  //repeat(a, min((size_t)100, axioms.size())) {
  repeat(a, axioms.size()) {
    //istringstream iss_axiom(axioms[a]);
    V(5) cerr << TS() << log_head << "/d=" << p_out_pg->nodes[ n_obs ].depth+1 << "/instantiate: " << axioms[a].axiom << " for " << endl;

    p_out_pg->used_axiom_types.insert(axioms[a].axiom);

    /* Check if the other RHS is in our P. */
    if("" != axioms[a].rhs_ot) {
//      cerr << axioms[a].rhs_ot.substr(0, axioms[a].rhs_ot.find("/")) << "/" <<
//          axioms[a].rhs_ot.substr(axioms[a].rhs_ot.find("/")+1) << endl;

      if(!p_out_pg->getNode(
          NULL,
          store_item_t(axioms[a].rhs_ot.substr(0, axioms[a].rhs_ot.find("/"))),
          atoi(axioms[a].rhs_ot.substr(axioms[a].rhs_ot.find("/")+1).c_str())) ) continue;
    }

    if(getTimeofDaySec() - stime >= 1.0) { V(4) cerr << TS() << "iBC: " << p_out_pg->nodes[n_obs].toString() << ": " << a << "/" << axioms.size() << endl; stime = getTimeofDaySec(); }
    
    sexp_reader_t sr;

    //for(sexp_reader_t sr(iss_axiom); !sr.isEnd(); ++sr) {
    for(sr.setStream(axioms[a].axiom); !sr.isEnd(); ++sr) {
      if(!sr.stack.isFunctor(FnBackgroundKnowledge)) continue;
      if(c.isTimeout()) continue; //return false;

      int i_lf = sr.stack.findFunctorArgument(ImplicationString), i_name = sr.stack.findFunctorArgument("name"),
        i_disj = sr.stack.findFunctorArgument(FnAxiomDisjoint);
      bool f_ghost = string::npos != sr.stack.toString().find("I-AM-GHOST");

      if(-1 == i_lf) {
        int i_inc = sr.stack.findFunctorArgument(IncString); if(-1 == i_inc) continue;
        p_out_pg->detectInconsistentNodes(n_obs, logical_function_t(*sr.stack.children[i_inc]));
        continue;
      }

      if("" != p_out_pg->nodes[n_obs].lit.extra && 0 == p_out_pg->nodes[n_obs].lit.wa_number) continue;

      if(LabelNode == p_out_pg->nodes[n_obs].type) continue;
      
      string name_axiom;
      if(-1 != i_name) {
        name_axiom = sr.stack.children[i_name]->children[1]->getString();
        
        if(string::npos != name_axiom.find("*")) {
          /* How many times is this axioms applied so far? */
          uint_t num_limit = atoi(name_axiom.substr(name_axiom.find("*")+1).c_str());
          if(num_limit <= p_out_pg->nodes[n_obs].axiom_name_used.count(name_axiom)) continue;
        } }

      /* For each clause that has the literal n_obs in its right-hand side, */
      logical_function_t lf( *sr.stack.children[i_lf] );
      string             axiom_str  = name_axiom+"/"+lf.toString();
      string             axiom_disj = -1 == i_disj ? "" : sr.stack.children[i_disj]->children[1]->getString();
      
      /* Already applied? */
      if( p_out_pg->p_x_axiom[n_obs][axiom_str] > 0 ) continue;

      if( applied_axioms.end() != applied_axioms.find(axiom_str) ) continue;

      applied_axioms.insert( axiom_str );
      
      V(5) cerr << TS() << axiom_str << " in " << ::join( p_out_pg->nodes[ n_obs ].axiom_used.begin(), p_out_pg->nodes[ n_obs ].axiom_used.end(), "/" ) << "?" << endl;

      if( p_out_pg->nodes[ n_obs ].axiom_used.end() != p_out_pg->nodes[ n_obs ].axiom_used.find( axiom_str ) ) {
        V(5) cerr << TS() << log_head << "Loopy!" << endl;
        continue; /* That's loopy axiom. */
      }

      /* FIND A SET OF LITERALS THAT MATCHES TO THE RIGHT HAND SIDE LITERALS. */
      vector<pair<vector<literal_t>,vector<int> > > rhs_collections;

      //cerr << lf.branches[1].toString() << endl;

      if(0 < cache_rhs_collections.count(lf.branches[1].toString())) {
        rhs_collections = cache_rhs_collections[lf.branches[1].toString()];
      } else {

        /* If there are multiple literals in RHS, ...  */
        if( Literal != lf.branches[1].opr ) { if( lf.branches[1].branches.size() > 1 ) {
            /* Multiple RHS literals. */
            struct { static void callback(const vector<int> &stack, void *p_context) {
              ((vector<vector<int> >*)p_context)->push_back(stack);
            } } cb;
              
            /* ACQUIRE OTHER POSSIBLE COMBINATIONS OF LITERALS. */
            vector<vector<int> > combinations;
            score_function_t::function_unit_t unit("", lf.branches[1], 0.0);
            _query(cb.callback, (void*)&combinations, *p_out_pg, n_current_pg_size, c, unit, NULL, 0, false, !c.no_apc4rhs);

            unifier_t          theta;
            vector<int>        rhs_candidates;
            vector<literal_t>  rhs_literals;

            repeat(j, combinations.size()) {
              repeat(k, combinations[j].size()) {
                if(c.isTimeout()) continue; //return false;

                if(!getMGU(&theta, lf.branches[1].branches[k].lit, p_out_pg->nodes[combinations[j][k]].lit))
                  goto BED;

                rhs_candidates.push_back(combinations[j][k]);
                rhs_literals.push_back(lf.branches[1].branches[k].lit);
              }

              {
                unordered_set<int> aobss(rhs_candidates.begin(), rhs_candidates.end());
                if(aobss.size() != rhs_candidates.size()) goto BED;
              }
//
//              repeat(jj, rhs_literals.size()) {
//                cerr << rhs_collections.size() << ":" << jj << rhs_literals[jj].toString() << endl;
//              }

              rhs_collections.push_back(make_pair(rhs_literals, rhs_candidates));

            BED:
              theta = unifier_t(); rhs_candidates.clear(); rhs_literals.clear();
              continue;
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

        cache_rhs_collections[lf.branches[1].toString()] = rhs_collections;
      }

      if(0 == rhs_collections.size())
        V(5) cerr << TS() << "No matching RHS found." << endl;

      num_instantiated++;

      repeat(i, rhs_collections.size()) {
        if(c.isTimeout()) continue; // return false;
        unifier_t      theta;
        bool           f_inc = false;
        vector<string> rhs_instances;
        unordered_map<string, unordered_set<string> > mapsVarConv;
        unordered_set<int> rhs_binding_literals;

        /* Produce substitution. */
        bool f_me_in = false;
        /* For each literal, */
        vector<literal_t> lhs_literals;

        repeat(j, rhs_collections[i].first.size()) {
          if(n_obs == rhs_collections[i].second[j]) f_me_in = true;

          V(5) cerr << TS() << rhs_collections[i].first[j].toString() << "~" << p_out_pg->nodes[rhs_collections[i].second[j]].toString() << endl;
          if( !getMGU( &theta, rhs_collections[i].first[j], p_out_pg->nodes[rhs_collections[i].second[j]].lit ) ) { f_inc = true; }
          rhs_instances.push_back(p_out_pg->nodes[rhs_collections[i].second[j]].toString());
          //cerr << i << ":" << j << p_out_pg->nodes[rhs_collections[i].second[j]].toString() << endl;

          for(int k=0; k<rhs_collections[i].first[j].terms.size(); k++)
            mapsVarConv[rhs_collections[i].first[j].terms[k].toString()].insert(p_out_pg->nodes[rhs_collections[i].second[j]].lit.terms[k].toString());
        }

        // TODO: abc
        //XXX
        if(!f_me_in) { V(5) cerr << TS() << "Wuff! (me)" << endl; continue; }
        if(f_inc) { V(5) cerr << TS() << "Wuff (inc)!" << endl; continue; }

        V(5) cerr << TS() << theta.toString() << endl;

        p_out_pg->used_axiom_tokens.insert(axiom_str + theta.toString());
        
        if( Literal == lf.branches[0].opr )
          lhs_literals.push_back( lf.branches[0].lit );
        else {
          for( uint_t j=0; j<lf.branches[0].branches.size(); j++ )
            lhs_literals.push_back( lf.branches[0].branches[j].lit );
        }

        /* BINDING FOR RHS. */
        repeat(j, theta.substitutions.size()) {
          if(theta.substitutions[j].terms[0].isConstant() && !theta.substitutions[j].terms[1].isConstant()) {
            rhs_binding_literals.insert(lhs_literals.size());
            lhs_literals.push_back(theta.substitutions[j]);
          }
        }

        /* FOR EQUALITY. */
        bool fNotApplicable = false;
        
        for(unordered_map<string, unordered_set<string> >::const_iterator j=mapsVarConv.begin(); mapsVarConv.end()!=j; ++j) {
          for(unordered_set<string>::const_iterator k=j->second.begin(); j->second.end()!=k; ++k) {
            for(unordered_set<string>::const_iterator l=j->second.begin(); j->second.end()!=l; ++l) {
              if(*k >= *l) continue;
              if(store_item_t(*k).isConstant() && store_item_t(*l).isConstant()) {
                fNotApplicable = true;
                continue;
              }
              
              rhs_binding_literals.insert(lhs_literals.size());
              lhs_literals.push_back(literal_t("=", *k, *l));
            }
          }
        }

        if(fNotApplicable)
          continue;

        /* Check if this lhs matches the condition stated by the given label. */
        bool f_prohibited = false;
        if( LabelGiven == c.objfunc ) {
          repeat( j, c.training_instance.y_lf.branches.size() ) {
            if( NotOperator != c.training_instance.y_lf.branches[j].opr ) continue;

            repeat( k, lhs_literals.size() ) {
              if( c.training_instance.y_lf.branches[j].branches[0].lit.predicate == lhs_literals[k].predicate ) { f_prohibited = true; break; }
           }
          }

          if( f_prohibited ) V(5) cerr << "Prohibited: " << axiom_str << endl;
        }

        /* Conditionin by inequality. */
        vector<pair<store_item_t, store_item_t> > cond_neqs;
        repeat(j, lf.branches[1].branches.size()) {
          if(lf.branches[1].branches[j].lit.predicate == "!=") {
            if(theta.map(lf.branches[1].branches[j].lit.terms[0]) == "") theta.add(lf.branches[1].branches[j].lit.terms[0], store_item_t::issueUnknown());
            if(theta.map(lf.branches[1].branches[j].lit.terms[1]) == "") theta.add(lf.branches[1].branches[j].lit.terms[1], store_item_t::issueUnknown());

            cond_neqs.push_back(make_pair(theta.map(lf.branches[1].branches[j].lit.terms[0]), theta.map(lf.branches[1].branches[j].lit.terms[1])));
          }
        }

        /* Perform backward-chaining. */
        vector<int> backchained_literals;
        unordered_set<int> associated_hypernodes;
        double rhs_cost = 0.0;

        repeat(j, rhs_collections[i].second.size()) {
          rhs_cost += p_out_pg->nodes[rhs_collections[i].second[j]].lit.wa_number;
          p_out_pg->p_x_axiom[rhs_collections[i].second[j]][axiom_str] = 1;
        }

        for( uint_t j=0; j<lhs_literals.size(); j++ ) {
          literal_t &lit = lhs_literals[j];

          /* ISSUE UNKNOWN VARIABLES. EXCEPT LITERALS THAT ARE PRODUCED FROM RHS BINDING. */
          if(0 == rhs_binding_literals.count(j)) {
            for( uint_t k=0; k<lit.terms.size(); k++ ) {
              static size_t s_cag = 0;
              if('!' == lit.terms[k].toString()[0]) { theta.add(lit.terms[k], store_item_t(::toString("CAG_%d", s_cag++))); }
              if(!lit.terms[k].isConstant() && !theta.isApplied(lit.terms[k])) theta.add(lit.terms[k], store_item_t::issueUnknown());
            }

            theta.apply( &lit );
          }
          
          int    n_backchained = p_out_pg->addNode( lit, HypothesisNode, n_obs );
        
          /* Set the node parameters. */
          V(5) cerr << TS() << log_head << p_out_pg->nodes[n_backchained].lit.wa_number << "*" << rhs_cost << endl;

          p_out_pg->nodes[n_backchained].num_instantiated         = axioms.size();
          p_out_pg->nodes[n_backchained].depth                    = p_out_pg->nodes[n_obs].depth + (f_ghost ? 0 : 1);
          p_out_pg->nodes[n_backchained].instantiated_by.axiom    = -1 != i_name ? (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?") : "";
          p_out_pg->nodes[n_backchained].instantiated_by.where    = j;
          p_out_pg->nodes[n_backchained].axiom_used.insert( p_out_pg->nodes[n_obs].axiom_used.begin(), p_out_pg->nodes[n_obs].axiom_used.end() );
          p_out_pg->nodes[n_backchained].axiom_used.insert( axiom_str );
          p_out_pg->nodes[n_backchained].axiom_name_used          = p_out_pg->nodes[n_obs].axiom_name_used;
          p_out_pg->nodes[n_backchained].axiom_name_used.insert(-1 != i_name ? (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?") : "");
          p_out_pg->nodes[n_backchained].nodes_appeared           = p_out_pg->nodes[n_obs].nodes_appeared;
          p_out_pg->nodes[n_backchained].nodes_appeared.insert(rhs_collections[i].second.begin(), rhs_collections[i].second.end());
          p_out_pg->nodes[n_backchained].lit.id                   = n_backchained;
          p_out_pg->nodes[n_backchained].lit.backchained_on       = n_obs;
          p_out_pg->nodes[n_backchained].lit.theta                = theta.toString();
          p_out_pg->nodes[n_backchained].lit.wa_number           *= rhs_cost;
          p_out_pg->nodes[n_backchained].lit.instantiated_by      = p_out_pg->nodes[n_backchained].instantiated_by.axiom;
          p_out_pg->nodes[n_backchained].lit.instantiated_by_all  = p_out_pg->nodes[n_obs].lit.instantiated_by_all + "#" + p_out_pg->nodes[n_backchained].instantiated_by.axiom;
          p_out_pg->nodes[n_backchained].rhs.insert(n_obs);
          p_out_pg->nodes[n_backchained].rhs.insert(rhs_collections[i].second.begin(), rhs_collections[i].second.end());
          p_out_pg->nodes[n_backchained].cond_neqs.insert(p_out_pg->nodes[n_backchained].cond_neqs.end(), cond_neqs.begin(), cond_neqs.end());
          p_out_pg->nodes[n_backchained].f_prohibited             = f_prohibited;
          p_out_pg->nodes[n_backchained].axiom_disj               = axiom_disj == "" ? p_out_pg->nodes[n_obs].axiom_disj : (p_out_pg->nodes[n_obs].toString() + axiom_disj);

          V(5) cerr << TS() << log_head << "new Literal: " <<
            p_out_pg->nodes[n_backchained].lit.toString() << endl;
          
          backchained_literals.push_back( n_backchained );

          if(0 < c.prohibited_literals.count(n_backchained))
            p_out_pg->nodes[n_backchained].f_prohibited = true;
        }

        if( backchained_literals.size() > 0 ) {
          /* Examine already have the same hypernode. */
          pg_hypernode_t hn;

          hn = p_out_pg->addHyperNode( backchained_literals );
          
          repeat( j, rhs_collections[i].second.size() )
            p_out_pg->addEdge(rhs_collections[i].second[j], hn, -1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?", rhs_collections[i].second.size(), axiom_str);

          if("" != axiom_disj || c.explanation_disjoint) {
            static hash<string> hashier;

            p_out_pg->axiom_disjoint_set[hashier(::join(rhs_instances.begin(), rhs_instances.end()))].insert(hn);
            V(6) cerr << TS() << "disjoint: " << ::join(rhs_instances.begin(), rhs_instances.end()) << ::toString("%s:%s:%s", axioms[i].axiom.c_str(), theta.toString().c_str(), axiom_disj.c_str()) << endl;
          }
        }

      }

    }

  }

  V(4) cerr << TS() << p_out_pg->nodes[n_obs].toString() << ": " << num_instantiated << " axioms were instantiated out of " << axioms.size() << endl;

  return true;
}

void proof_graph_t::detectInconsistentNodes(int n_obs, const logical_function_t &lf) {
  string axiom_str = lf.toString();
  
  /* Already applied? */
  //if(p_x_axiom[n_obs][axiom_str] > 0 ) return;
  
  /* Find the inconsistent pair! */
  const vector<int> *p_paired_nodes;
  int   n_lf_obs, n_lf_paired;

  V(6) cerr << TS() << "INC:" << lf.toString() << endl;
  
  if(nodes[n_obs].lit.predicate == lf.branches[1].lit.predicate) {
    n_lf_obs = 1; n_lf_paired = 0;
    if(!getNode(&p_paired_nodes, lf.branches[0].lit.predicate, lf.branches[0].lit.terms.size())) return;
  } else {
    n_lf_obs = 0; n_lf_paired = 1;
    if(!getNode(&p_paired_nodes, lf.branches[1].lit.predicate, lf.branches[1].lit.terms.size())) return;
  }

  /* CONSTANT MISMATCH */
  for(uint i=0; i<nodes[n_obs].lit.terms.size(); i++) {
    if(lf.branches[n_lf_obs].lit.terms[i].isConstant() && nodes[n_obs].lit.terms[i].isConstant() &&
       lf.branches[n_lf_obs].lit.terms[i] != nodes[n_obs].lit.terms[i]) return;
  }

  repeat(i, p_paired_nodes->size()) {
    V(5) cerr << TS() << "Possibly inconsistent: " << nodes[(*p_paired_nodes)[i]].toString() << ", " << nodes[n_obs].toString() << endl;
    
    /* CONSTANT MISMATCH */
    bool fConstantMismatch = false;
    
    for(uint j=0; j<nodes[(*p_paired_nodes)[i]].lit.terms.size(); j++) {
      if(lf.branches[n_lf_paired].lit.terms[j].isConstant() && nodes[(*p_paired_nodes)[i]].lit.terms[j].isConstant() &&
         lf.branches[n_lf_paired].lit.terms[j] != nodes[(*p_paired_nodes)[i]].lit.terms[j]) {fConstantMismatch = true; break;}
    }

    if(fConstantMismatch) continue;
    
    V(5) cerr << TS() << "Inconsistent: " << nodes[(*p_paired_nodes)[i]].toString() << ", " << nodes[n_obs].toString() << endl;
          
    unifier_t theta;

    for(uint j=0; j<nodes[n_obs].lit.terms.size(); j++) {
      if(lf.branches[n_lf_obs].lit.terms[j].isConstant() && !nodes[n_obs].lit.terms[j].isConstant())
        theta.add(lf.branches[n_lf_obs].lit.terms[j], nodes[n_obs].lit.terms[j]);
    }

    for(uint j=0; j<nodes[(*p_paired_nodes)[i]].lit.terms.size(); j++) {
      if(lf.branches[n_lf_paired].lit.terms[j].isConstant() && !nodes[(*p_paired_nodes)[i]].lit.terms[j].isConstant())
        theta.add(lf.branches[n_lf_paired].lit.terms[j], nodes[(*p_paired_nodes)[i]].lit.terms[j]);
    }
    
    repeat(t1, lf.branches[0].lit.terms.size()) {
      repeat(t2, lf.branches[1].lit.terms.size()) {
        if(lf.branches[0].lit.terms[t1] == lf.branches[1].lit.terms[t2]) {
          theta.add(nodes[(*p_paired_nodes)[i]].lit.terms[t1], nodes[n_obs].lit.terms[t2]);
        }
      } }

    p_x_axiom[n_obs][axiom_str] = 1;
    p_x_axiom[(*p_paired_nodes)[i]][axiom_str] = 1;
    mutual_exclusive_nodes.push_back(make_pair(make_pair((*p_paired_nodes)[i], n_obs), theta));
  }
  
  // repeat(i, p_nodes->size()) {          
  //   unifier_t theta;
  //   bool      f_fail = false;
  //   pg_node_t
  //     &n1 = nodes[n_obs].lit.predicate == lf.branches[0].lit.predicate ? nodes[n_obs] : nodes[(*p_nodes)[i]],
  //     &n2 = nodes[n_obs].lit.predicate == lf.branches[0].lit.predicate ? nodes[(*p_nodes)[i]] : nodes[n_obs];

    
  //   repeat(t1, lf.branches[0].lit.terms.size()) {
  //     repeat(t2, lf.branches[1].lit.terms.size()) {
  //       if(lf.branches[0].lit.terms[t1] == lf.branches[1].lit.terms[t2]) {
  //         theta.add(n1.lit.terms[t1], n2.lit.terms[t2]);

  //         if(n1.lit.terms[t1].isConstant() && n2.lit.terms[t2].isConstant() &&
  //             n1.lit.terms[t1] != n2.lit.terms[t2]) {
  //           f_fail = true; break;
  //         }
  //       }

  //       if(lf.branches[0].lit.terms[t1].isConstant() && lf.branches[0].lit.terms[t1] != n1.lit.terms[t1] && lf.branches[0].lit.terms[t1] != n2.lit.terms[t2]) {
  //         f_fail = true; break;
  //       }

  //       if(lf.branches[1].lit.terms[t2].isConstant() && lf.branches[1].lit.terms[t2] != n1.lit.terms[t1] && lf.branches[1].lit.terms[t2] != n2.lit.terms[t2]) {
  //         f_fail = true; break;
  //       }
  //     } }

  //   if(f_fail) continue;

  //   V(5) cerr << TS() << "Inconsistent: " << n1.toString() << ", " << n2.toString() << theta.toString() << endl;
    
  //   p_x_axiom[n_obs][axiom_str] = 1;
  //   p_x_axiom[(*p_nodes)[i]][axiom_str] = 1;
  //   mutual_exclusive_nodes.push_back(make_pair(make_pair((*p_nodes)[i], n_obs), theta));
  // }
}

bool proof_graph_t::produceUnificationAssumptions(const knowledge_base_t &kb, const inference_configuration_t &c) {

  vector<pair<int, int> > unifiables;
    
  /* ENUMERATE UNIFIABLE LITERALS. */
  V(2) cerr << TS() << "Enumerating unifiable literals..." << endl;

  pg_node_map_t my_p2n = p2n;

  foreach(pg_node_map_t, iter_p2n, my_p2n) {
    if(iter_p2n->first == "=" || iter_p2n->first == "!=") continue;
    
    for(unordered_map<int, vector<int> >::iterator iter_pa2n=iter_p2n->second.begin(); iter_p2n->second.end()!=iter_pa2n; ++iter_pa2n) {
      if(!kb.isUnifiable(iter_p2n->first, iter_pa2n->first)) continue;
      if(1 == iter_pa2n->second.size()) continue;
      
      if(iter_pa2n->second.size() >= 10) {
        V(4) cerr << TS() << "Unifiable: " << ::toString("%s/%d", iter_p2n->first.c_str(), iter_pa2n->first) << ": " << iter_pa2n->second.size() << endl;
      }

      int num_really_unifiable = 0;

//#pragma omp parallel for
      repeat(i, iter_pa2n->second.size()) {
        repeatf(j, i+1, iter_pa2n->second.size()) {
          if(c.isTimeout()) continue;

          int ni = iter_pa2n->second[i], nj = iter_pa2n->second[j];
          unifier_t unic;
          hash<string> hashier;

//          if(0 < already_ua_produced.count(::toString("%d,%d", ni, nj)) || 0 < already_ua_produced.count(::toString("%d,%d", nj, ni)))
//            continue;
//
//          already_ua_produced.insert(::toString("%d,%d", ni, nj));


          if(!getMGU(&unic, nodes[ni].lit, nodes[nj].lit, false, true)) continue;
          //if(nodes[ni].lit.wa_number >= 9999.0 && nodes[nj].lit.wa_number >= 9999.0) continue;

          /* TWO NODES SHARING IT'S PARENT ARE NOT UNIFIABLE. */
//          if(has_intersection(nodes[ni].nodes_appeared.begin(), nodes[ni].nodes_appeared.end(),
//                              nodes[nj].nodes_appeared.begin(), nodes[nj].nodes_appeared.end()))
//            continue;

          if(nodes[ni].lit.backchained_on == nodes[nj].lit.backchained_on) continue;


          /* TWO NODES WHICH ARE PRODUCED FROM DISJOINT AXIOMS CANNOT BE UNIFIED. */
          if("" != nodes[ni].axiom_disj && "" != nodes[nj].axiom_disj &&
             nodes[ni].axiom_disj == nodes[nj].axiom_disj) {
            V(6) cerr << TS() << "Canceled: " << nodes[ni].toString() << "," << nodes[nj].toString() << " by " << nodes[ni].axiom_disj << endl;
            continue;
          }

          /* TWO LITERALS L1, L2 CANNOT BE UNIFIED IF THEY ARE IN EXPLAINER-EXPLAINEE RELATIONSHIP. */
          if(nodes[ni].nodes_appeared.end() != nodes[ni].nodes_appeared.find(nj) ||
             nodes[nj].nodes_appeared.end() != nodes[nj].nodes_appeared.find(ni) )
            continue;

          /* NODES IN nodes_appeared ARE SIMULTANEOUSLY
             HYPOTHESIZED. CHECK IF THEY ARE CONTRADICTORY OR NOT. */
          bool fIncImplyBreak = false;
          unifier_t uni;
          getMGU(&uni, nodes[ni].lit, nodes[nj].lit);

          if(c.implybreak) {
            for(unordered_set<int>::const_iterator k=nodes[ni].nodes_appeared.begin(); nodes[ni].nodes_appeared.end()!=k; ++k) {
              for(unordered_set<int>::const_iterator l=nodes[nj].nodes_appeared.begin(); nodes[nj].nodes_appeared.end()!=l; ++l) {
                V(6) {
                  cerr << nodes[ni].toString() << " => " << nodes[*k].toString() << endl;
                  cerr << nodes[nj].toString() << " => " << nodes[*l].toString() << endl;
                }
              
                for(int n=0; n<kb.mxpairs.size(); n++) {
                  vector<pair<int, int> > mxeqs;
                  int numImpliedEqs = 0;
                
                  if(kb.mxpairs[n].first.predicate == nodes[*k].lit.predicate &&
                     kb.mxpairs[n].second.predicate == nodes[*l].lit.predicate) {
                    for(int mx=0; mx<kb.mxpairs[n].first.terms.size(); mx++) {
                      for(int my=0; my<kb.mxpairs[n].second.terms.size(); my++) {
                        if(kb.mxpairs[n].first.terms[mx] == kb.mxpairs[n].first.terms[my]) {
                          V(6) cerr << kb.mxpairs[n].first.toString() << " & " << kb.mxpairs[n].second.toString() << " => _|_: " << mx << "," << my << endl;
                      
                          mxeqs.push_back(make_pair(mx, my));
                        }
                      } }
                
                    for(int o=0; o<mxeqs.size(); o++) {
                      if(doesMGUimply(uni, nodes[*k].lit.terms[mxeqs[o].first], nodes[*l].lit.terms[mxeqs[o].second]) ||
                         nodes[*k].lit.terms[mxeqs[o].first] == nodes[*l].lit.terms[mxeqs[o].first]
                         ) numImpliedEqs++;
                    }
                    
                    if(numImpliedEqs == mxeqs.size()) { fIncImplyBreak = true; break; }
                  } else if(kb.mxpairs[n].first.predicate == nodes[*l].lit.predicate &&
                            kb.mxpairs[n].second.predicate == nodes[*k].lit.predicate) {
                    for(int mx=0; mx<kb.mxpairs[n].first.terms.size(); mx++) {
                      for(int my=0; my<kb.mxpairs[n].second.terms.size(); my++) {
                        if(kb.mxpairs[n].first.terms[mx] == kb.mxpairs[n].first.terms[my]) {
                          V(6) cerr << kb.mxpairs[n].first.toString() << " & " << kb.mxpairs[n].second.toString() << " => _|_: " << mx << "," << my << endl;
                      
                          mxeqs.push_back(make_pair(mx, my));
                        }
                      } }
                
                    for(int o=0; o<mxeqs.size(); o++) {
                      if(doesMGUimply(uni, nodes[*l].lit.terms[mxeqs[o].first], nodes[*k].lit.terms[mxeqs[o].second]) ||
                         nodes[*k].lit.terms[mxeqs[o].first] == nodes[*l].lit.terms[mxeqs[o].first]
                         ) numImpliedEqs++;
                    }
                    
                    if(numImpliedEqs == mxeqs.size()) { fIncImplyBreak = true; break; }
                  }
                  
                }
              }
            }

            if(fIncImplyBreak) {
              V(4) cerr << TS() << "EqImplyBreak: " << nodes[ni].toString() << "," << nodes[nj].toString() << endl;
              continue;
            }
          }
          
          V(6) cerr << TS() << "Unifiable pair: " << nodes[ni].toString() << "," << nodes[nj].toString() << "/" << uni.toString() << endl;

          num_really_unifiable++;
          //unifiables.push_back(make_pair(ni, nj));

          int explainer = ni, explainee = nj;

          /* MAKE SURE THAT WA_NUMBER OF EXPLAINEE IS LARGER THAN THAT OF EXPLAINER. */
          if(nodes[explainee].lit.wa_number < nodes[explainer].lit.wa_number)
            swap(explainer, explainee);

          vector<int> nodes_explaining;
          nodes_explaining.push_back(explainer);

          // RENEW THE UNIFIER
          getMGU(&uni, nodes[explainee].lit, nodes[explainer].lit);

          char p[1024];
          strcpy(p, nodes[explainee].lit.predicate.c_str());


          /* TWO VARIABLES MUST BE THE SAME TYPE. */
          // bool f_incompatible = false;

          // repeat(k, uni.substitutions.size()) {
          //   if(!isCompatibleType(uni.substitutions[k].terms[0], uni.substitutions[k].terms[1])) {
          //     V(5) cerr << TS() << "Incompatible unification: " <<
          //         uni.substitutions[k].terms[0] << ":" << mget(var_type, uni.substitutions[k].terms[0], (string)"?") << "~" <<
          //         uni.substitutions[k].terms[1] << ":" << mget(var_type, uni.substitutions[k].terms[1], (string)"?") << endl;
          //     f_incompatible = true;
          //   }
          // }

          // if(f_incompatible) continue;

          //if(c.use_only_user_score && nodes[explainee].lit.predicate != "mention'") continue;

          if(LazyBnB != c.method) {
            repeat(k, uni.substitutions.size()) {
              if(c.isTimeout()) continue;
              if(uni.substitutions[k].terms[0] == uni.substitutions[k].terms[1]) continue;
              if(!kb.isUnifiable(p, nodes[explainee].lit.terms.size(), k)) continue;

              store_item_t t1=uni.substitutions[k].terms[0], t2=uni.substitutions[k].terms[1]; if(t1 > t2) swap(t1, t2);

              //if(t1.isUnknown() && t2.isUnknown()) continue;

              int node_sub = getSubNode(t1, t2);
              if(-1 == node_sub) {

                node_sub = addNode(literal_t("=", t1, t2), HypothesisNode);

                V(6) cerr << TS() << nodes[explainee].toString() << "~" << nodes[explainer].toString() << ": " << vc_unifiable.toString() << endl;

                if(!t1.isUnknown() && !t2.isUnknown())
                  nodes[node_sub].lit.wa_number = 0;
                if(t1.isUnknown() && t2.isUnknown())
                  nodes[node_sub].lit.wa_number = 0.1;
                else
                  nodes[node_sub].lit.wa_number = 0.05;

                nodes[node_sub].lit.wa_number = 0;
              }

              nodes_explaining.push_back(node_sub);
            }
          }

          V(6) cerr << TS() << nodes[explainee].toString() << "~" << nodes[explainer].toString() << endl;

          // repeat(k, uni.substitutions.size()) {
          //   if(!isCompatibleType(uni.substitutions[k].terms[0], uni.substitutions[k].terms[1])) {
          //     V(5) cerr << TS() << "Incompatible unification: " <<
          //         uni.substitutions[k].terms[0] << ":" << mget(var_type, uni.substitutions[k].terms[0], (string)"?") << "~" <<
          //         uni.substitutions[k].terms[1] << ":" << mget(var_type, uni.substitutions[k].terms[1], (string)"?") << endl;
          //   } else {
          //     /* IF THERE IS SOME TYPE RESTRICTION... */
          //     string &tv1 = var_type_var[uni.substitutions[k].terms[0]],
          //       &tv2 = var_type_var[uni.substitutions[k].terms[1]];

          //     if(!("" == tv1 || "" == tv2)) {
          //       int eqConstraint = getSubNode(store_item_t(tv1), store_item_t(tv2)),
          //         eqDesired = getSubNode(uni.substitutions[k].terms[0], uni.substitutions[k].terms[1]);

          //       if(-1 != eqDesired) {
          //         if(-1 == eqConstraint)
          //           eqConstraint = addNode(literal_t("=", store_item_t(tv1), store_item_t(tv2)), HypothesisNode);

          //         type_restriction[eqDesired] = eqConstraint;
          //       }
          //     }
          //   }
          // }
          
          //cerr << nodes_explaining.size() << endl;

          /* ADD EXPLAIN BY UNIFICATION RELATION. */
          string pn = nodes[explainee].lit.predicate.toString();
          if(string::npos != pn.find("-"))
            pn = pn.substr(pn.find("-")+1);

          pg_hypernode_t hn = addHyperNode(nodes_explaining, true);
          u2hn[explainer < explainee ? explainer : explainee][explainer < explainee ? explainee : explainer] = hn;

          /* LINK EQUALITIES TO THE HYPERNODE. */
          repeat(k, uni.substitutions.size()) {
            store_item_t t1=uni.substitutions[k].terms[0], t2=uni.substitutions[k].terms[1]; if(t1 > t2) swap(t1, t2);
            eq2hnu[t1][t2].push_back(hn);
          }

          //addEdge(unifiables[i].first, hn, c.use_only_user_score ? "0": "UNIFY_" + pn);
          addEdge(explainee, hn, "0", 1);

        } }

      V(5) cerr << TS() << "-> " << num_really_unifiable << endl;
    }
  }

  if(c.isTimeout()) return false;

  return produceEqualityAssumptions(kb, c);
}

bool proof_graph_t::produceEqualityAssumptions(const knowledge_base_t &kb, const inference_configuration_t &c) {

  V(3) cerr << TS() << "Generating unification assumptions... (2/2)" << endl;

  /* MAKE SURE EQUALITY NODES FOR THE SET OF UNIFIABLE VARIABLES. */
  for(variable_cluster_t::cluster_t::iterator iter_c2v=vc_unifiable.clusters.begin(); vc_unifiable.clusters.end()!=iter_c2v; ++iter_c2v) {
    vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );

    for( uint_t i=0; i<variables.size(); i++ ) {
      for( uint_t j=i+1; j<variables.size(); j++ ) {
        store_item_t t1=variables[i], t2=variables[j]; if(t1 > t2) swap(t1, t2);
        if(c.isTimeout()) return false;
        //if(t1.isConstant() && t2.isConstant()) continue;

        /* IF THE NODE ISN'T CREATED, THEN GENERATE IT. */
        int node_sub = getSubNode(t1, t2);
        if(-1 == node_sub) node_sub = addNode(literal_t("=", t1, t2), HypothesisNode);

        nodes[node_sub].lit.wa_number = 0;

        /* TWO VARIABLES MUST BE THE SAME TYPE. */
        // if((t1.isConstant() && t2.isConstant()) || !isCompatibleType(t1, t2)) {
        //   V(4) cerr << TS() << "Incompatible unification: " << t1 << ":" << mget(var_type, t1, (string)"?") << "~" << t2 << ":" << mget(var_type, t2, (string)"?") << endl;
        //   nodes[node_sub].lit.wa_number = 9999;
        // }

      } }
  }

  return true;

}

void function::initializeWeight(sparse_vector_t *p_w, const string &name, const inference_configuration_t &ic) {
  (*p_w)[name] = 1.0;
  return;

  if(!ic.no_prior) {
    if(string::npos != name.find("_EXPLAINED_")) {
      (*p_w)[name] = 1.0;
      return;
    }

    if(string::npos != name.find("_AXIOM_")) {
      (*p_w)[name] = -1.2;
      return;
    }
  }
  
  if(!g_ext.isFunctionDefined("cbInitializeWeight")) {
    (*p_w)[name] = 0;
    //(*p_w)[name] = -0.0001 - (0.0001 * ic.i_initializer);
    return;
  }
  
  mypyobject_t::buyTrashCan();

  external_module_context_t emc = {NULL, NULL, &ic, 0.0, ""};
  mypyobject_t pycon(PyCapsule_New( (void*)&emc, NULL, NULL));
  mypyobject_t pyarg(Py_BuildValue("(Os)", pycon.p_pyobj, name.c_str()));
  mypyobject_t pyret(g_ext.call("cbInitializeWeight", pyarg.p_pyobj));

  if(NULL != pyret.p_pyobj)
    (*p_w)[name] = PyFloat_AsDouble(pyret.p_pyobj);
  else
    (*p_w)[name] = 0.0;
            
  mypyobject_t::cleanTrashCan();
}

bool function::augmentTheLoss(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &pg, inference_configuration_t& c) {
  repeat(i, pg.nodes.size()) {
    if(pg.nodes[i].lit.predicate == "!=") continue;
    
    /* IS THIS AN LABEL? */
    if(c.training_instance.isLabel(pg.nodes[i].lit)) {
      p_out_lprel->feature_vector[p_out_cache->createNodeVar(i)][PrefixFixedValue + string("LOSS_")] = -1;
      V(3) cerr << TS() << "Loss is augmented for: " << pg.nodes[i].toString() << endl;
    }
  }
  
  return true;
}

bool function::convertToFeatureVector(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &pg, inference_configuration_t& c) {
  
  /* Start creating factors... */
  p_out_lp->addVariable( lp_variable_t( "dummy" ) );
  
  sparse_vector_t    v_inf, v_minf; v_inf[store_item_t("FIXED")] = 9999.0; v_minf[store_item_t("FIXED")] = -9999.0;
  variable_cluster_t vc_gold;
  unordered_set<int> vars_unification;

  /* BASIC COMPONENT. */
  V(1) cerr << TS() << "Processing basic score function..." << endl;

  unordered_map<int, unordered_set<int> > ncnj, cnjimp;
  
  repeat(i, pg.nodes.size()) {
    if( c.isTimeout() ) return false;

    p_out_cache->createNodeVar(i);

    pg_edge_set_t::const_iterator iter_eg = pg.edges.find(i);
    if( pg.edges.end() != iter_eg ) {
      repeat(j, iter_eg->second.size()) {
        p_out_cache->createConjVar(iter_eg->second[j]);

        const vector<int> &hn = pg.hypernodes[iter_eg->second[j]];
        
        repeat(k, hn.size()) {
          /* A NODE BEING TRUE IMPLIES THAT AT LEAST ONE CONJUNCTION BELONGING TO THE NODE
             IS TRUE. EXCEPT CONJUNCTION FOR UNIFICATION. */
          //if(HypothesisNode == pg.nodes[hn[k]].type && (pg.nodes[hn[k]].lit.predicate == "=" || !pg.isHyperNodeForUnification(iter_eg->second[j])))
          //if(string::npos == pg.hypernodeToString(iter_eg->second[j]).find("mention") && (pg.nodes[hn[k]].lit.predicate == "=" || !pg.isHyperNodeForUnification(iter_eg->second[j])))

          //
          if(!pg.isHyperNodeForUnification(iter_eg->second[j]))
            ncnj[hn[k]].insert(iter_eg->second[j]);

          // cerr << pg.nodes[hn[k]].toString() << ":" << pg.hypernodeToString(iter_eg->second[j]) << endl;
        }

        /* BEING THE HYPOTHETICAL CONJUNCTION TRUE IMPLIES THAT AT LEAST ONE HEAD NODE IS TRUE. */
        if(!pg.isHyperNodeForUnification(iter_eg->second[j]) && HypothesisNode == pg.nodes[i].type && !pg.isAllObserved(iter_eg->second[j]))
          cnjimp[iter_eg->second[j]].insert(i);
      }
    }
  }

  /* CREATE ILP CONSTRAINTS FOR TYPE RESTRICTION. */
  for(unordered_map<int, int>::const_iterator i=pg.type_restriction.begin(); pg.type_restriction.end()!=i; ++i) {
    V(5) cerr << TS() << "TYPE RESTR: " << pg.nodes[i->first].toString() << " => " << pg.nodes[i->second].toString() << endl;
    
    lp_constraint_t con_tr("typeRestr", LessEqual, 0);
    con_tr.push_back(p_out_cache->createNodeVar(i->first), 1.0);
    con_tr.push_back(p_out_cache->createNodeVar(i->second), -1.0);
    p_out_lp->addConstraint(con_tr);
  }
  
  for(unordered_map<int, unordered_set<int> >::iterator iter_imp=ncnj.begin(); ncnj.end()!=iter_imp; ++iter_imp) {
    lp_constraint_t con_imp(::toString("imp%d:%s", iter_imp->first, pg.nodes[iter_imp->first].toString().c_str()), LessEqual, 0);

    if(pg.nodes[iter_imp->first].lit.predicate == PredicateSubstitution) continue;
    
    V(6) cerr << TS() << "CON_IMP: " << pg.nodes[iter_imp->first].toString() << " => ";
    
    foreach(unordered_set<int>, i, iter_imp->second) {
      // if(string::npos != pg.hypernodeToString(iter_imp->second[i]).find("mention"))
      //   continue;
      
      //if(!pg.isAllObserved(iter_imp->second[i]))
      {
        con_imp.push_back(p_out_cache->createConjVar(*i), -1.0);
        V(6) cerr << pg.hypernodeToString(*i) << " ";
      }
    }

    //if(0 == con_imp.vars.size()) p_out_lp->variables[p_out_cache->createNodeVar(iter_imp->first)].fixValue(0.0);
    
    con_imp.push_back(p_out_cache->createNodeVar(iter_imp->first), 1.0);
    if(1 < con_imp.vars.size()) p_out_lp->addConstraint(con_imp); // x

    V(6) cerr << endl;
  }

  for(unordered_map<int, unordered_set<int> >::iterator iter_imp=cnjimp.begin(); cnjimp.end()!=iter_imp; ++iter_imp) {
    lp_constraint_t con_imp(::toString("imp%d", iter_imp->first), LessEqual, 0);
    
    V(6) cerr << TS() << "CON_IMP2: " << pg.hypernodeToString(iter_imp->first) << " => ";

    foreach(unordered_set<int>, i, iter_imp->second) {
      int v_node = p_out_cache->createNodeVar(*i);

//      if(pg.nodes[*i].rhs.size() > 1) {
//        factor_t fc_and(AndFactorTrigger);
//        foreachc(unordered_set<int>, j, pg.nodes[*i].rhs)
//          fc_and.push_back(p_out_cache->createNodeVar(*j), 1.0);
//        v_node = fc_and.apply(&p_out_cache->lp, "fc_and");
//      }

      con_imp.push_back(v_node, -1.0);
      V(6) cerr << pg.nodes[*i].toString() << " ";
    }
    
    con_imp.push_back(p_out_cache->createConjVar(iter_imp->first), 1.0);
    if(1 < con_imp.vars.size()) p_out_lp->addConstraint(con_imp);

    V(6) cerr << endl;
  }
  
          // lp_constraint_t con_imp(::toString("imp%d-%d:%s", i, iter_eg->second[j], pg.nodes[i].toString().c_str()), LessEqual, 0);
          // con_imp.push_back(v_cnj, 1.0);
          // con_imp.push_back(p_out_cache->createNodeVar(i), -1.0);
          // p_out_lp->addConstraint(con_imp);
  
  /* INCONSISTENT NODES. */
  repeat(i, pg.mutual_exclusive_nodes.size()) {
    if( c.isTimeout() ) return false;

    V(6) cerr << TS() << "MUTUAL EXCLUSIVE: "
              << pg.nodes[pg.mutual_exclusive_nodes[i].first.first].toString() << ","
              << pg.nodes[pg.mutual_exclusive_nodes[i].first.second].toString() << endl;
    
    p_out_cache->createConsistencyConstraint(pg.mutual_exclusive_nodes[i].first.first,
                                             pg.mutual_exclusive_nodes[i].first.second,
                                             pg.mutual_exclusive_nodes[i].second);
  }

  /* DISJOINT AXIOMS. */
  foreachc(axiom_disjoint_set_t, i, pg.axiom_disjoint_set) {
    lp_constraint_t con_d(::toString("axdisj_%d", i), LessEqual, 1);

    if(i->second.size() <= 1) continue;
    
    foreachc(unordered_set<int>, j, i->second)
      con_d.push_back(p_out_cache->createConjVar(*j), 1.0);

    p_out_lp->addConstraint(con_d);
  }

  /* BEST-LINK STRATEGY. */
  // foreachc(proof_graph_t::var2var2node_t, iter_v2v2n, pg.nodes_sub) {
  //   V(5) cerr << TS() << "BEST-LINK FOR: " << iter_v2v2n->first.toString() << endl;

  //   lp_constraint_t con_bl(::toString("bestlink_%s", iter_v2v2n->first.toString().c_str()), LessEqual, 1);
    
  //   foreachc(proof_graph_t::var2node_t, iter_v2n, iter_v2v2n->second)
  //     con_bl.push_back(p_out_cache->createNodeVar(iter_v2n->second), 1.0);

  //   p_out_lp->addConstraint(con_bl);
  // }
  
  /* USED-DEFINED SCORE FUNCTION. */  
  V(1) cerr << TS() << "Processing user-defined score function..." << endl;

  struct mycontext_t {
    lp_inference_cache_t                    *p_out_cache;
    score_function_t                        *p_out_psfunc;
    const score_function_t::function_unit_t *p_unit;
    const inference_configuration_t         *p_ic;
  } con;

  struct { static void callback(const vector<int> &stack, void *p_context) {
    mycontext_t *p_con = (mycontext_t*)p_context;
    const score_function_t::function_unit_t &unit = *p_con->p_unit;
    const proof_graph_t &pg = p_con->p_out_cache->pg;
    string str_lf = unit.lf.toString(), str_feature;
      
    /* GOOD BOY! */
    unifier_t      mgu;
    bool           f_unification_succeeded = true;
    vector<string> instances;
    vector<string> comb;
    factor_t       fc_cnj(AndFactorTrigger), fc_neg_cnj(AndFactorTrigger);
    int            lc = 0;
    
    foreachc(vector<int>, i, stack) {
      const string &predicate_name = unit.lf.branches[lc].lit.predicate;

      //if(ObservableNode != pg.nodes[*i].type) {
        fc_cnj.push_back(p_con->p_out_cache->createNodeVar(*i), '?' != predicate_name[0]);
        fc_neg_cnj.push_back(p_con->p_out_cache->createNodeVar(*i), predicate_name == "=" ? !('?' != predicate_name[0]) : '?' != predicate_name[0]);
        // fc_neg_cnj.push_back(p_con->p_out_cache->createNodeVar(predicate_name != "=" ? *i : pg.getNegSubNode(pg.nodes[*i].lit.terms[0], pg.nodes[*i].lit.terms[1])), '?' != predicate_name[0]);
        //}
      
      if(!(f_unification_succeeded = getMGU(&mgu, literal_t(pg.nodes[*i].lit.predicate, unit.lf.branches[lc].lit.terms) , pg.nodes[*i].lit, true))) break;
      instances.push_back(pg.nodes[*i].lit.toString());

      string str_signature = predicate_name + "(";
      repeat(j, unit.lf.branches[lc].lit.terms.size()) {
        if(unit.lf.branches[lc].lit.terms[j] == "_") str_signature += (j > 0 ? ",_" : "_");
        else                                        str_signature += (j > 0 ? "," : "") + (const string&)pg.nodes[*i].lit.terms[j];
      }

      str_signature += ")";
      comb.push_back(str_signature);
      
      lc++;
    }
      
    str_feature = (p_con->p_ic->fix_user_weight && 0 != unit.name.find("~") ? "!USER_" : "USER_") +
      (("?" == unit.name || 0 == unit.name.find("+")) ? /* IF THE NAME IS NOT SPECIFIED, THEN WEIGHTING FOR EACH AXIOM. */
       unit.name + "_" + str_lf + mgu.toString() : unit.name); /* CONSIDER VARIABLE BINDING FOR EXCLAMATION-MARKED VARIABLES. */
      
    /* AVOID DUPLICATING IT. */
    sort(comb.begin(), comb.end());
    string str_comb = str_feature + ":" + ::join(comb.begin(), comb.end(), ",");
      
    if(0 < p_con->p_out_cache->user_defined_features.count(str_comb)) return;
    if(!f_unification_succeeded) return;

    p_con->p_out_cache->user_defined_features.insert(str_comb);

    /* FIX THE WEIGHT IF NEEDED. */
    cerr << "W:" << unit.weight << endl;
    if(0.0 != unit.weight) {
      str_feature = "!" + str_feature;
      p_con->p_out_psfunc->weights[str_feature] = unit.weight;
    }
      
    V(5) cerr << TS() << str_feature << ": " << ::join(instances.begin(), instances.end()) << "/MGU: " << mgu.toString() << endl;

    int v_cnj = fc_cnj.apply(&p_con->p_out_cache->lp, "fc_" + str_comb);
    if(-1 == v_cnj) return;

    if(0.0 != unit.weight) {
      p_con->p_out_cache->lprel.feature_vector[v_cnj][store_item_t(str_feature)] = unit.weight;
    }
    
    //p_con->p_out_cache->lprel.feature_vector[v_cnj][store_item_t("AAAA")] = 1;
  
    // int v_neg_cnj = fc_neg_cnj.apply(&p_con->p_out_cache->lp, "fc_" + str_comb);
    // p_con->p_out_cache->lprel.feature_vector[v_neg_cnj][str_feature + "_NEG"] = 1;
          
    return;
  } } cb;

  repeat(i, c.p_sfunc->units.size()) {
    if( c.isTimeout() ) return false;
    V(5) cerr << TS() << "Score function: " << c.p_sfunc->units[i].lf.toString() << endl;

    con.p_ic         = &c;
    con.p_out_cache  = p_out_cache;
    con.p_out_psfunc = c.p_sfunc;
    con.p_unit       = &c.p_sfunc->units[i];
    
    _query(cb.callback, (void*)&con, pg, pg.nodes.size(), c, c.p_sfunc->units[i]);
  }

  /* SET GOLD CLUSTERING. ASSUME THAT LABELS FOLLOW OPEN WORLD ASSUMPTIONS. */
  //if(LabelGiven == c.objfunc) p_out_cache->fixGoldClustering();
  
  /* TRANSITIVE RELATIONS OVER EQUALITIES. */
  if(LazyBnB == c.method || BnB == c.method || LocalSearch == c.method) {
    V(2) cerr << TS() << "enumerateP: Creating transitivity constraints..." << endl;

    for( variable_cluster_t::cluster_t::const_iterator iter_c2v=pg.vc_unifiable.clusters.begin(); pg.vc_unifiable.clusters.end()!=iter_c2v; ++iter_c2v ) {
      vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
      
      for( uint_t i=0; i<variables.size(); i++ ) {
        for( uint_t j=i+1; j<variables.size(); j++ ) {
          for( uint_t k=j+1; k<variables.size(); k++ ) {            
            if( c.isTimeout() ) return false;
            p_out_cache->createTransitivityConstraint(variables[i], variables[j], variables[k]);
          } } }
    }
  }

  /* MULTIPLE VARIABLES CAN BE BOUND TO AT MOST ONE CONSTANT. */
  for(unordered_map<store_item_t, unordered_set<store_item_t> >::const_iterator iter_cm=pg.constants_sub.begin(); pg.constants_sub.end()!=iter_cm; ++iter_cm) {
    if( 1 == iter_cm->second.size() ) continue;

    V(4) cerr << TS() << "MX: " << iter_cm->first << ": ";

    lp_constraint_t con_con( "mxc", LessEqual, 1.0 );

    foreachc(unordered_set<store_item_t>, iter_t, iter_cm->second) {
      con_con.push_back( p_out_cache->createNodeVar(pg.getSubNode(iter_cm->first, *iter_t)), 1.0 );
      V(4) cerr << *iter_t << ", ";
    }

    V(4) cerr << "." << endl;

    p_out_lp->addConstraint( con_con );
  }

  return true;
}

bool function::convertToLP(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &pg, inference_configuration_t& c) {
  
  /* SET THE OBJECTIVE OF ILP OPTIMIZATION PROBLEM. */
  V(2) cerr << TS() << "Transforming the feature vector into LP objectives..." << endl;
  
  for(unordered_map<int, sparse_vector_t>::iterator iter_o2v=p_out_lprel->feature_vector.begin(); p_out_lprel->feature_vector.end() != iter_o2v; ++iter_o2v) {
    foreach(sparse_vector_t, iter_v, iter_o2v->second) {
      if(c.scaling_score_func)
        iter_v->second *= 100.0 * pg.getNormalizer(); //1000.0 * pg.getNormalizer();
      
      if(0 == ((const string&)iter_v->first).find(PrefixInvisibleElement) || 0 == ((const string&)iter_v->first).find(PrefixFixedValue))
        p_out_lp->variables[iter_o2v->first].obj_val += iter_v->second; /* IGNORE THE WEIGHT. */
      else {
        /* IF THE WEIGHT HAS NOT BEEN SET YET, THEN INITIALIZE IT. */
        if(0 == c.p_sfunc->weights.count(iter_v->first)) {
          function::initializeWeight(&c.p_sfunc->weights, iter_v->first, c);
          c.i_initializer += 1;
        }

//        cerr << iter_v->first << c.p_sfunc->weights[iter_v->first] << " /" <<
//        		(string::npos != ((const string&)iter_v->first).find(PrefixFixedWeight) ? 1.0 : c.p_sfunc->weights[iter_v->first]) * iter_v->second << endl;

        p_out_lp->variables[iter_o2v->first].obj_val +=
        		(string::npos != ((const string&)iter_v->first).find(PrefixFixedWeight) ? 1.0 : c.p_sfunc->weights[iter_v->first]) * iter_v->second;
          //(c.ignore_weight && 0 != ((const string&)iter_v->first).find(PrefixFixedWeight) ? 1.0 : c.p_sfunc->weights[iter_v->first]) * iter_v->second;
      }
      
      p_out_lprel->input_vector[iter_v->first]+= iter_v->second;
    } }

  /* INTERACTIVE DEBUG MODE (LET'S WHEN IT WILL BE IMPLEMENTED). */
  
  return true;
}

void function::convertLPToHypothesis( logical_function_t *p_out_h, logical_function_t *p_out_obs, sparse_vector_t *p_out_fv, const lp_solution_t &sol, const lp_inference_cache_t &cache ) {

  p_out_obs->opr = AndOperator;
  p_out_h->opr = AndOperator;
  p_out_h->branches.clear();
  
  variable_cluster_t vc;

  /* CREATE LITERALS EXCEPT EQUALITIES. */
  for( uint_t i=0; i<cache.pg.nodes.size(); i++ ) {
    if(cache.pg.nodes[i].f_removed) continue;
    unordered_map<int, int>::const_iterator iter_v = cache.lprel.n2v.find(i);
    if( cache.lprel.n2v.end() == iter_v ) continue;
    else {
      if( 0.5 > sol.optimized_values[ iter_v->second ] ) continue;
    }

    if(cache.pg.nodes[i].lit.predicate == PredicateSubstitution) {
      repeat(j, cache.pg.nodes[i].lit.terms.size()) {
        repeatf(k, j+1, cache.pg.nodes[i].lit.terms.size()) {
          vc.add(cache.pg.nodes[i].lit.terms[j], cache.pg.nodes[i].lit.terms[k]);
        } }
      continue;
    }

    p_out_h->branches.push_back( logical_function_t( cache.pg.nodes[i].lit ) );
    p_out_h->branches[p_out_h->branches.size()-1].lit.i_am_from = i;

    if(ObservableNode == cache.pg.nodes[i].type) {
      p_out_obs->branches.push_back( logical_function_t( cache.pg.nodes[i].lit ) );
      p_out_h->branches[p_out_obs->branches.size()-1].lit.i_am_from = i;
    }
  }

  /* FOR EQUALITIES. */
  foreach( variable_cluster_t::cluster_t, iter_vc, vc.clusters )
    if( iter_vc->second.size() > 1) {
      literal_t equality( PredicateSubstitution );
      
      for( unordered_set<store_item_t>::iterator iter_v=iter_vc->second.begin(); iter_vc->second.end()!=iter_v; ++iter_v )
        equality.terms.push_back( *iter_v );
      
      p_out_h->branches.push_back( logical_function_t( equality ) );
    }

  /* CREATE FEATURE VECTOR. */
  if( NULL != p_out_fv ) {
    repeat( i, cache.lp.variables.size() ) {
      if(0.5 < sol.optimized_values[i]) {
        if(cache.lprel.feature_vector.end() != cache.lprel.feature_vector.find(i)) {
          foreachc( sparse_vector_t, iter_fv, cache.lprel.feature_vector.find(i)->second )
            (*p_out_fv)[iter_fv->first] += iter_fv->second;
        }
      }
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
    if(iter_v->isConstant()) return *iter_v;
  foreach( unordered_set<store_item_t>, iter_v, vars )
    if(!iter_v->isUnknown()) return *iter_v;
  return *vars.begin();
}

void proof_graph_t::printGraph( const lp_solution_t &sol, const linear_programming_problem_t &lpp, const lp_problem_mapping_t &lprel, const string& property, ostream* p_out, logical_function_t *p_hypothesis ) const {

  (*p_out) << "<proofgraph" << ("" != property ? (" " + property) : "") << ">" << endl;
  
  for( uint_t i=0; i<nodes.size(); i++ ) {
    if(nodes[i].f_removed) continue;
    
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find(i);
    if( lprel.n2v.end() == iter_v ) continue;
    
    (*p_out) << ::toString("<literal id=\"%d\" type=\"%d\" depth=\"%d\" active=\"%s\">",
                           i, nodes[i].type, nodes[i].depth, (sol.optimized_values[iter_v->second] < 0.5 ? "no" : "yes"))
             << _sanitize(nodes[i].toString()) << "</literal>" << endl;
  }
  
  for( pg_edge_set_t::const_iterator iter_eg = edges.begin(); edges.end() != iter_eg; ++iter_eg ) {
    unordered_map<int, int>::const_iterator iter_v = lprel.n2v.find( iter_eg->first );
    if(lprel.n2v.end() == iter_v) continue;
    if(nodes[iter_eg->first].f_removed) continue;
    
    for( uint_t i=0; i<iter_eg->second.size(); i++ ) {

      bool   f_removed = false;
      uint_t n_active = 0;
      
      for( uint_t j=0; j<hypernodes[ iter_eg->second[i] ].size(); j++ ) {
        unordered_map<int, int>::const_iterator iter_vt = lprel.n2v.find( hypernodes[ iter_eg->second[i] ][j] );
        if(lprel.n2v.end() == iter_vt) continue;
        if(nodes[hypernodes[ iter_eg->second[i] ][j]].f_removed) { f_removed = true; break; }
        if(0.5 < sol.optimized_values[ iter_vt->second ]) n_active++;
      }

      if(f_removed) continue;

      if(isHyperNodeForUnification(iter_eg->second[i])) {
        vector<string> subs;
        
        repeat(j, hypernodes[iter_eg->second[i]].size()) {
          if(nodes[hypernodes[iter_eg->second[i]][j]].lit.predicate != PredicateSubstitution) continue;
          subs.push_back((const string&)nodes[hypernodes[iter_eg->second[i]][j]].lit.terms[0] + "=" + (const string&)nodes[hypernodes[iter_eg->second[i]][j]].lit.terms[1]);
        }
        
        (*p_out) << ::toString("<unification l1=\"%d\" l2=\"%d\" unifier=\"%s\" active=\"%s\" />",
                               hypernodes[iter_eg->second[i]][0], iter_eg->first, ::join(subs.begin(), subs.end(), ", ").c_str(),
                               0.5 < sol.optimized_values[iter_v->second] && n_active == hypernodes[iter_eg->second[i]].size() ? "yes" : "no") << endl;

      } else {
        (*p_out) << "<explanation name=\""<< edges_name.find(iter_eg->second[i])->second <<"\" active=\""<< (0.5 < sol.optimized_values[ iter_v->second ] && hypernodes[ iter_eg->second[i] ].size() == n_active ? "yes" : "no") <<"\" axiom=\"\">";
      
        for( uint_t j=0; j<hypernodes[ iter_eg->second[i] ].size(); j++ ) {
          (*p_out) << hypernodes[ iter_eg->second[i] ][j];
          if( j < hypernodes[ iter_eg->second[i] ].size()-1 ) (*p_out) << " ^ ";
        }

        (*p_out) << " => " << iter_eg->first << "</explanation>" << endl;
      }
    }
  }

  vector<const literal_t*> literals;

  p_hypothesis->getAllLiterals(&literals);

  int cluster_id = 0;

  repeat(i, literals.size()) {
    if(literals[i]->predicate == "=") {
      (*p_out) << "<variable-cluster name=\"C"<< cluster_id++ <<"\">";

      repeat(j, literals[i]->terms.size()) {
        (*p_out) << literals[i]->terms[j];
        if(j != literals[i]->terms.size()-1) (*p_out) << ",";
      }

      (*p_out) << "</variable-cluster>" << endl;
    }
  }

  (*p_out) << "</proofgraph>" << endl;
  
}

/* Thanks for https://gist.github.com/240957. */
sexp_reader_t &sexp_reader_t::operator++() {

  bool f_comment = false;
  char last_c    = 0;
  char buffer[1024];
  int  n_buffer_size = 0;
  
  memset(buffer, 0, sizeof(buffer));
  sexp_stack_t *p_s_back;

  while(-1 == m_string_stream_counter ? m_stream->good() : m_string_stream_counter < m_string_stream->length()) {
    char c = -1 == m_string_stream_counter ? m_stream->get() : (*m_string_stream)[m_string_stream_counter++];

//    if(-1 != m_string_stream_counter)
//      cerr << m_string_stream_counter <<"/"<< m_string_stream->length() << c << endl;
//    else
//      cerr << m_stream->tellg() <<"/?"  << c << endl;

    if(-1 == m_string_stream_counter) read_bytes = m_stream->tellg(); else read_bytes = ((size_t)m_string_stream_counter);
    if( '\n' == c ) n_line++;

    p_s_back = m_stack.back();
    
    if( StringStack != p_s_back->type && '\\' != last_c && ';' == c ) { f_comment = true; continue; }
    if( f_comment ) {
      if( '\n' == c ) f_comment = false;
      continue;
    }

    switch(p_s_back->type) {
    case ListStack: {
      if( '(' == c ) {
        /* IF IT WERE TOP STACK, THEN CLEAR. */
        if(1 == m_stack.size()) clearStack();
        m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); }
      else if( ')' == c ) {
        _A( m_stack.size() >= 2, "Syntax error at " << n_line << ": too many parentheses." << endl << p_s_back->toString() );
        //m_stack[ m_stack.size()-2 ]->children.push_back( p_s_back ); m_stack.pop_back();
        (*(++m_stack.rbegin()))->children.push_back( p_s_back ); m_stack.pop_back();
        if( TupleStack == m_stack.back()->children[0]->type && "quote" == m_stack.back()->children[0]->children[0]->str ) {
          (*(++m_stack.rbegin()))->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
        stack = *m_stack.back()->children.back();
        return *this;
      } else if( '"' == c ) m_stack.push_back( new_stack( sexp_stack_t(StringStack) ) );
      //else   if( '\'' == c ) m_stack.push_back( new_stack( sexp_stack_t(TupleStack, "quote", m_stack_list) ) );
      else if( isSexpSep(c) ) break;
      else { m_stack.push_back( new_stack( sexp_stack_t(TupleStack, string(1, c), m_stack_list) ) ); n_buffer_size=0; memset(buffer, 0, sizeof(buffer)); }
      break; }
      
    case StringStack: {
      if( '"' == c ) {
        (*(++m_stack.rbegin()))->children.push_back( p_s_back ); m_stack.pop_back();
        if( m_stack.back()->children[0]->type == TupleStack && m_stack.back()->children[0]->children[0]->str == "quote" ) {
          (*(++m_stack.rbegin()))->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
      } else if( '\\' == c ) p_s_back->str += -1 == m_string_stream_counter ? m_stream->get() : (*m_string_stream)[m_string_stream_counter++];
      else p_s_back->str += c;
      break; }

    case TupleStack: {
      if( isSexpSep(c) ) {
        p_s_back->children[0]->str += buffer;
        sexp_stack_t *p_atom = p_s_back; m_stack.pop_back();
        m_stack.back()->children.push_back(p_atom);
        if( TupleStack == m_stack.back()->children[0]->type && "quote" == m_stack.back()->children[0]->children[0]->str ) {
          (*(++m_stack.rbegin()))->children.push_back( m_stack.back() ); m_stack.pop_back();
        }
        if(-1 == m_string_stream_counter) m_stream->unget(); else m_string_stream_counter--;
      } else if( '\\' == c ) buffer[n_buffer_size++] = -1 == m_string_stream_counter ? m_stream->get() : (*m_string_stream)[m_string_stream_counter++]; //p_s_back->children[0]->str += m_stream.get();
      else buffer[n_buffer_size++] = c; //p_s_back->children[0]->str += c;
      break; }
    }

    last_c = c;
  }

  if(-1 != m_string_stream_counter)
    m_string_stream_counter = m_string_stream->length()+1;

  clearStack();
    
  return *this;
}






/*
   GGG  RRRRRR   AA    VV     VV  EEEEEEEE
  G   G R    R  A  A    VV   VV   EE
  G     RRRRRR  AAAA    VV   VV   EEEEEEEE
  G  GG RRR    A    A    VV VV    EE
   G  G R  RR  A    A     V V     EE
    GGG R    R A    A      V      EEEEEEEE
*/
  
bool _processFeatureFunction(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const mypyobject_t &pyret, const inference_configuration_t &c, const proof_graph_t &pg) {
  
  /* [ (["FC_1", "FC_2", ...], "FEATURE_ELEMENT", 1.0), ... ] */
  unordered_map<string, int> fc_map;
      
  repeat( i, PyList_Size(pyret.p_pyobj) ) {
    if( c.isTimeout() ) return false;

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
          fc_cnf.push_back( p_out_cache->createNodeVar(p_id), !f_negation );
          break; }
        case 'c': {
          char var1[32], var2[32]; sscanf( fc_name.substr(1).c_str(), "%s %s", var1, var2 );
          int v_coref = p_out_cache->createNodeVar(pg.getSubNode(store_item_t(var1), store_item_t(var2)) );
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

    //if(is_vua_included && 0 != feature_element_name.find(PrefixFixedWeight)) vars_unification.insert(v_fc);
        
    if( f_prohibiting || -1 != v_fc ) {
      V(5) cerr << TS() << "New factor: " << ::join(signature.begin(), signature.end(), "/") << ":" << PyString_AsString(p_pyfen) << ":" << PyFloat_AsDouble(p_pyfev) << ":w=" << c.p_sfunc->weights[store_item_t(PyString_AsString(p_pyfen))] << ":" << is_vua_included << endl;
      if(-1 != v_fc) p_out_lp->variables[ v_fc ].name += "/" + string(PyString_AsString(p_pyfen));
    }
    if( !f_prohibiting && -1 != v_fc ) { p_out_lprel->feature_vector[ v_fc ][ store_item_t(PyString_AsString(p_pyfen)) ] += PyFloat_AsDouble(p_pyfev); }

  }
}

int _createFeatureFunction(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const proof_graph_t &pg, const logical_function_t &lf, const vector<int> &node_mapping, int *p_out_literal_no) {
  if(AndOperator == lf.opr || OrOperator == lf.opr) {
    factor_t fc_opr(OrOperator == lf.opr ? OrFactorTrigger : AndFactorTrigger);
    
    repeat(i, lf.branches.size()) {
      int v_active = _createFeatureFunction(p_out_lp, p_out_lprel, p_out_cache, pg, lf.branches[i], node_mapping, p_out_literal_no);
      fc_opr.push_back(v_active);
    }
    
    int v_opr = fc_opr.apply(p_out_lp, "fc_");
    return v_opr;
  } else if(Literal == lf.opr) {
    if(-1 == node_mapping[*p_out_literal_no]) {
      (*p_out_literal_no)++;
      return 0;
    }
    
    int v_lit = p_out_cache->createNodeVar(node_mapping[*p_out_literal_no]);
    (*p_out_literal_no)++;
    return v_lit;
  }
  
  return -1;
}


      /* Switch off all the feature condition constraints. */
      // repeat(i, p_out_cache->lp.constraints.size()) {
      //   lp_constraint_t &con = p_out_cache->lp.constraints[i];
      //   if(string::npos != con.name.find("fc_")) {
      //     if(0.0 == p_out_cache->lp.variables[con.vars[con.vars.size()-1]].obj_val) continue;
          
      //     con.is_active = false;
      //     p_out_cache->lp.variables[con.vars[con.vars.size()-1]].fixValue(0.0);
      //   }
      // }

      // while(true) {
      //   function::solveLP_BnB(&p_out_cache->lp, &p_out_cache->lprel, c, p_out_cache);

      //   int num_added = 0;
        
      //   repeat(i, p_out_cache->lp.constraints.size()) {
      //     lp_constraint_t &con = p_out_cache->lp.constraints[i];
      //     if(con.is_active || 0 != con.name.find("fc_cost_")) continue;

      //     cerr << con.toString(p_out_cache->lp.variables) << endl;
          
      //     /* Is this not maximally satisfied? */
      //     p_out_cache->lp.variables[con.vars[con.vars.size()-1]].optimized = 1.0;
      //     double score      = p_out_cache->lp.variables[con.vars[con.vars.size()-1]].obj_val;
      //     bool   f_satisfied = con.isSatisfied(p_out_cache->lp.variables), f_add = false;

      //     f_add = (score > 0 && !f_satisfied) || (score < 0 && f_satisfied);

      //     if(f_add) {
      //       con.is_active = true; num_added++;
      //       p_out_cache->lp.variables[con.vars[con.vars.size()-1]].fixValue(InvalidFixedValue);
      //     }
          
      //     p_out_cache->lp.variables[con.vars[con.vars.size()-1]].optimized = 0.0;
      //   }

      //   repeat(i, p_out_cache->lp.variables.size())
      //     p_out_cache->lp.variables[i].setInitialValue(p_out_cache->lp.variables[i].optimized);
        
      //   V(3) cerr << "CPI: " << num_added << " features were added." << endl;
        
      //   if(0 == num_added) break;

      //   //p_out_cache->lp.cutoff = p_out_cache->lp.optimized_obj-1.0;
      // }
      
      // break;
