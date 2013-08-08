
#include "defs.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>

#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/mman.h>

#include <fstream>
#include <map>
#include <algorithm>

#include <tr1/unordered_set>

/* Instances. */
ofstream           g_out_file;
ostream           *g_p_out         = &cout;
external_module_t  g_ext;
int                g_verbose_level = 0;
deque<void(*)(int)> g_exit_callbacks;
deque<string>      g_xml_stack;
list<list<PyObject*> > mypyobject_t::trash_cans;

/* STATIC MEMBER. */
unordered_map<size_t, string> store_item_t::m_items;
int                           store_item_t::m_issued_variable_count = 0;
hash<string>                  store_item_t::m_hashier;

inference_result_type_t algorithm::infer(vector<explanation_t> *p_out_expls, lp_inference_cache_t *p_out_cache, lp_inference_cache_t *p_old_cache, inference_configuration_t& c, const logical_function_t &obs, const knowledge_base_t& kb, ostream *p_out ) {

  inference_result_type_t ret = GenerationTimeout;
  p_out_cache->elapsed_prepare = getTimeofDaySec();
  c.timestart                  = getTimeofDaySec();

  // {
  //   c.depthlimit = 0;
    
  //   repeat(i, 3) {
  //     c.n_start = p_out_cache->pg.n_start;
  //     function::enumeratePotentialElementalHypotheses(&p_out_cache->pg, &p_out_cache->evc, obs, kb, c);
  //     function::convertToLP(&p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, p_out_cache->evc, c);
      
  //     vector<lp_solution_t> lpsols;
  //     function::solveLP_BnB(&lpsols, p_out_cache->lp, p_out_cache->lprel, c, p_out_cache);

  //     repeat(i, p_out_cache->lp.variables.size()) {
  //       p_out_cache->lp.variables[i].setInitialValue(lpsols[0].optimized_values[i]);
  //     }
      
  //     c.depthlimit++;
  //     string t;
  //     getline(cin, t);
  //   }
    
  // }
  
  if( !c.use_cache ) {
    V(1) cerr << TS() << "Generating potential hypothesis graph..." << endl;
    if( function::enumeratePotentialElementalHypotheses( &p_out_cache->pg, obs, kb, c ) ) {
      if(LabelGiven == c.objfunc && p_out_cache->pg.f_label_not_found) {
        V(1) cerr << TS() << "Label is not derived by inference." << endl;
        //return GenerationTimeout;
      }
      
      V(1) cerr << TS() << "Converting the graph to LP optimization problem..." << endl;
      if(!function::convertToFeatureVector( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, c ))
        V(1) cerr << TS() << "Timeout." << endl;

      //if(LabelGiven == c.objfunc || LossAugmented == c.objfunc) {
      if(LossAugmented == c.objfunc) {
        V(1) cerr << TS() << "Augmenting the loss function..." << endl;
        function::augmentTheLoss(&p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, c);
      }
      
      if(!function::convertToLP( &p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, c ))
        V(1) cerr << TS() << "Timeout." << endl;
      
    } else
      V(1) cerr << TS() << "Timeout." << endl;
  }
  
  p_out_cache->elapsed_prepare = getTimeofDaySec() - p_out_cache->elapsed_prepare;

  if(c.isOutput(OutputInfoILP)) (*g_p_out) << p_out_cache->lp.toString() << endl;

  vector<lp_solution_t> lpsols;
  ilp_solution_type_t   lpsol_type;
    
  if(p_out_cache->elapsed_prepare < c.timelimit) {
    ret = ILPTimeoutAvailable;
   
    V(1) cerr << TS() << "Start inference with " << (BnB == c.method ? "BnB" : (c.method == CuttingPlaneBnB ? "BnB (with CPI)" : (c.method == NoTransitivity ? "BnB (wo transitivity)" : "LocalSearch"))) << "..." << endl;
    
    /* Reset the time. */
    c.timestart = getTimeofDaySec();
    
    switch( c.method ) {
    case LazyBnB: {
      unordered_set<string> g;
      double last_cost = -9999.0;
      vector<int> activated_nodes;

      for(int n=1; n<=100; n++) {
        function::solveLP_BnB(&lpsols, p_out_cache->lp, p_out_cache->lprel, c, p_out_cache);

        explanation_t expl(lpsols[0]);
        function::convertLPToHypothesis(&expl.lf, &expl.lf_obs, &expl.fv, lpsols[0], *p_out_cache);

        cerr << TS() << "I=" << n << ": HYPOTHESIS: " << expl.lf.toString() << endl;
        cerr << TS() << "I=" << n << ": COST: " << expl.lpsol.optimized_obj << " (DIFF:"<< (expl.lpsol.optimized_obj-last_cost) <<")" << endl;
        
//        if(fabs(expl.lpsol.optimized_obj - last_cost) <= 1e-10) {
//          cerr << TS() << "I=" << n << ": NO COST INCREASED." << endl;
//          break;
//        }

        last_cost = expl.lpsol.optimized_obj;

        /* CALCULATE THE COST WITH EQUALITIES. */
        size_t size_g = g.size();

        activated_nodes.clear();

        repeat(i, expl.lf.branches.size()) {
          repeatf(j, i+1, expl.lf.branches.size()) {
            literal_t &l_i = expl.lf.branches[i].lit, &l_j = expl.lf.branches[j].lit;

            if(!(l_i.predicate != "!=" && l_i.predicate != "=" && l_i.predicate == l_j.predicate &&
                 l_i.terms.size() == l_j.terms.size())) continue;
            
            unifier_t theta;
            pg_hypernode_t hn4u = p_out_cache->pg.getUnifierHyperNode(l_i.i_am_from, l_j.i_am_from);

            if(-1 == hn4u) continue;
            if(0.5 > expl.lpsol.optimized_values[p_out_cache->lprel.hn2v[hn4u]]) continue;
            if(!function::getMGU(&theta, l_i, l_j)) continue;

            V(4) cerr << TS() << "UNIFIED: " << l_i.toString() << "~" << l_j.toString() << "/" << theta.toString() << endl;
            V(5) cerr << TS() << l_i.i_am_from << ":" << l_j.i_am_from << "/" << theta.toString() << endl;

            V(5) cerr << TS() << p_out_cache->pg.hypernodeToString(hn4u) << endl;
            
            repeat(k, theta.substitutions.size()) {
              store_item_t t1 = theta.substitutions[k].terms[0],
                t2 = theta.substitutions[k].terms[1];

              if(t1 > t2) swap(t1, t2);
              if(t1 == t2 || (t1 != t2 && t1.isConstant() && t2.isConstant())) continue;

              if(0 < g.count(t1.toString()+t2.toString())) {
                V(4) cerr << TS() << "... Already passed." << endl;
                continue;
              }

              g.insert(t1.toString()+t2.toString());

              int node_sub = p_out_cache->pg.getSubNode(t1, t2);

              /* CREATE A NEW NODE IF IT DOESN'T EXIST. */
              if(-1 == node_sub) {
                node_sub = p_out_cache->pg.addNode(literal_t("=", t1, t2), HypothesisNode);
                activated_nodes.push_back(node_sub);
              }

              /* ACTIVATE. */
              V(4) cerr << TS() << "ADDED: " << literal_t("=", t1, t2).toString() << endl;
                
              p_out_cache->pg.nodes[node_sub].lit.wa_number = 0;
              
              vector<int> &hn4us = p_out_cache->pg.eq2hnu[t1][t2];

              repeat(l, hn4us.size()) {
                p_out_cache->pg.hypernodes[hn4us[l]].push_back(node_sub);
              }
            }
          }
        }

        if(size_g == g.size()) {
          cerr << TS() << "I=" << n << ": TERMINATED (NO NEW POTENTIAL EQUALITY ASSUMPTIONS)." << endl;
          break;
        }

        p_out_cache->pg.produceEqualityAssumptions(kb, c);

        /* STORE THE CURRENT SOLUTION. */
        unordered_map<int, double> n2sol, hn2sol, n2esol;
        
        for(unordered_map<int, int>::iterator j=p_out_cache->lprel.n2v.begin(); p_out_cache->lprel.n2v.end()!=j; ++j)
          n2sol[j->first] = lpsols[0].optimized_values[j->second];
        
        for(unordered_map<int, int>::iterator j=p_out_cache->lprel.n2ev.begin(); p_out_cache->lprel.n2ev.end()!=j; ++j)
          n2esol[j->first] = lpsols[0].optimized_values[j->second];

        for(unordered_map<int, int>::iterator j=p_out_cache->lprel.hn2v.begin(); p_out_cache->lprel.hn2v.end()!=j; ++j)
          hn2sol[j->first] = lpsols[0].optimized_values[j->second];

        /* REFRESH THE LP PROBLEM. */
        p_out_cache->lp = linear_programming_problem_t();
        p_out_cache->lprel = lp_problem_mapping_t();

        function::convertToFeatureVector(&p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, c);
        function::convertToLP(&p_out_cache->lp, &p_out_cache->lprel, p_out_cache, kb, p_out_cache->pg, c);

        /* SET MIP START. */
        for(unordered_map<int, double>::iterator j=n2sol.begin(); n2sol.end()!=j; ++j)
          p_out_cache->lp.variables[p_out_cache->lprel.n2v[j->first]].setInitialValue(j->second);

        for(unordered_map<int, double>::iterator j=n2esol.begin(); n2esol.end()!=j; ++j)
          p_out_cache->lp.variables[p_out_cache->lprel.n2ev[j->first]].setInitialValue(j->second);

        for(unordered_map<int, double>::iterator j=hn2sol.begin(); hn2sol.end()!=j; ++j)
          p_out_cache->lp.variables[p_out_cache->lprel.hn2v[j->first]].setInitialValue(j->second);

        repeat(i, activated_nodes.size())
          p_out_cache->lp.variables[p_out_cache->lprel.n2v[activated_nodes[i]]].setInitialValue(1.0);

        repeat(i, p_out_cache->lp.variables.size()) {
          if(-9999.0 == p_out_cache->lp.variables[i].init_val)
            p_out_cache->lp.variables[i].setInitialValue(1);
        }

        if(c.isOutput(OutputInfoILP)) (*g_p_out) << p_out_cache->lp.toString() << endl;

        lpsols.clear();
      }

    } break;

    case NoTransitivity:
#ifdef USE_GUROBI
    case CuttingPlaneBnB:
    case BnB: { lpsol_type = function::solveLP_BnB(&lpsols, p_out_cache->lp, p_out_cache->lprel, c, p_out_cache); break; }
#endif
#ifdef USE_LPSOLVE
    case CuttingPlaneBnB:
    case BnB: { lpsol_type = function::solveLP_BnB(&lpsols, p_out_cache->lp, p_out_cache->lprel, c, p_out_cache); break; }
#endif
#ifdef USE_LOCALSOLVER
    case LocalSearch: { lpsol_type = function::solveLP_LS(&lpsols, p_out_cache->lp, p_out_cache->lprel, c, p_out_cache); break; }
#endif
    default: break;
    };
  
  }

  if(NotAvailable == lpsol_type)
    ret = ILPTimeoutNotAvailable;
  else
    ret = 0 < lpsols.size() ? Success : ILPTimeoutAvailable;
  
  /* k-best explanation. */
  repeat(s, lpsols.size()) {
    explanation_t expl(lpsols[s]);

    if(c.isOutput(OutputInfoILP)) (*g_p_out) << lpsols[s].toString(p_out_cache->lp) << endl;

    foreachc( pairwise_vars_t, iter_t1, p_out_cache->lprel.pp2v )
      for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
        if( 0.5 < lpsols[s].optimized_values[ iter_t2->second ] ) lpsols[s].optimized_obj -= -EqBias;
      }
    
    function::convertLPToHypothesis( &expl.lf, &expl.lf_obs, &expl.fv, lpsols[s], *p_out_cache );
    p_out_cache->loss.setLoss(c.training_instance, expl.lf, p_out_cache->lprel, lpsols[s].optimized_obj);
    p_out_cache->loss.minimum_loss = p_out_cache->loss.loss;
    expl.loss                      = p_out_cache->loss.loss;

    (*p_out) << "<observed size=\"" << obs.branches.size() << "\">" << endl << _sanitize(expl.lf_obs.toString(c.isOutput(OutputInfoColored), c.isOutput(OutputInfoWithNumbers))) << endl << "</observed>" << endl
             << "<hypothesis score=\"" << lpsols[s].optimized_obj << "\">" << endl << _sanitize(expl.lf.toString(c.isOutput(OutputInfoColored), c.isOutput(OutputInfoWithNumbers))) << endl << "</hypothesis>" << endl
             << "<vector score=\""<< score_function_t::getScore(c.p_sfunc->weights, expl.fv, c.ignore_weight) <<"\">" << endl << _sanitize(function::toString(expl.fv, c.isOutput(OutputInfoColored))) << endl << "</vector>" << endl;

    if(c.isOutput(OutputInfoWeights))
      *p_out << "<weight-vector>" << endl << _sanitize(function::toString(c.p_sfunc->weights, c.isOutput(OutputInfoColored))) << endl << "</weight-vector>" << endl;
    
    if(c.isOutput(OutputInfoFactors)) {
      (*p_out) << "<score-function>" << endl;

      repeat( i, p_out_cache->lp.variables.size() ) {
        if(0 == p_out_cache->lp.variables[i].name.find("fc_"))
          cout << toString(c.isOutput(OutputInfoColored) ?
                           "<factor name=\"\33[0;33m%s\33[0m\" value=\"\33[0;34m%f\33[0m\">%f</factor>" : "<factor name=\"%s\" value=\"%f\">%f</factor>",
                           p_out_cache->lp.variables[i].name.c_str(), p_out_cache->lp.variables[i].obj_val, lpsols[s].optimized_values[i]) << endl;
      }
      
      (*p_out) << "</score-function>" << endl;
    }
    
    p_out_expls->push_back(expl);
  }
  
  if(c.isOutput(OutputInfoAxioms)) {
    (*p_out) << "<instantiated-axioms>" << endl;

    foreach(unordered_set<string>, i, p_out_cache->pg.used_axiom_types)
      (*p_out) << "<axiom>" << *i << "</axiom>" << endl;
    
    (*p_out) << "</instantiated-axioms>" << endl;
  }

  return ret;
}

void algorithm::learn( score_function_t *p_out_sfunc, const learn_configuration_t &c, vector<training_data_t>& t, const knowledge_base_t& kb ) {

  unordered_map<string, int> num_diff;
  unordered_map<string, int> gave_up_in_generation;

  /* SHARED MEMORY FOR ALL FORKS. */
  struct shared_memory_t {
    size_t num_processed;
    bool   f_in_process;
    double total_updates, total_loss;
    int    num_vectors;

    inline void initialize() {
      num_processed = 0;
      f_in_process  = false;
      total_updates = 0.0;
      total_loss    = 0.0;
      num_vectors   = 0;
    }

    inline void join() { while(f_in_process); }
    inline void lock() { join(); f_in_process = true; }
    inline void unlock() { f_in_process = false; }
  };
  
  char            *p_shared_mmap   = (char *)mmap(0, sizeof(shared_memory_t), PROT_READ | PROT_WRITE, MAP_ANON | MAP_SHARED, -1, 0);
  shared_memory_t *p_shared_buffer = (shared_memory_t*)p_shared_mmap;

  /* DUPLICATE KNOWLEDGE BASE. */
  vector<knowledge_base_t*> duplicated_kbs;

  repeat(s, c.S)
    duplicated_kbs.push_back(new knowledge_base_t(false, kb));

  repeat(n, c.N) {
    cerr << TS() << "Iteration: " << 1+n << endl;
    function::beginXMLtag( "learn-process", "iteration=\"" + toString("%d", 1+n) +"\"" );

    /* Initialize the weights with the current weights. */
    int             num_local_vectors = 0;
    sparse_vector_t weight_pool;
    pid_t           forked_pid, child_pid;
    vector<pid_t>   child_processes;

    p_shared_buffer->initialize();

    /* Shuffle the training set. */
    random_shuffle( t.begin(), t.end() );
    
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

      knowledge_base_t &another_kb = *duplicated_kbs[s];
      
      while(true) {
        store_item_t::cleanupUnknowns();

        /* POP THE TRAINING PROBLEM. */
        p_shared_buffer->lock();
        size_t i = p_shared_buffer->num_processed++;
        p_shared_buffer->unlock();
        
        if(i >= t.size()) break;
        
        stringstream ss;
        unordered_map<int, unordered_map<string, double> > sol_cache;
        
        string log_head = toString("I=%d: S=%d/%d: P=%d/%d: ",
                                   1+n, 1+s, c.S, p_shared_buffer->num_processed, t.size());
        
        cerr << endl;
        _N(" * Target: " << t[i].name << " / " << log_head);

        if( 1 == gave_up_in_generation[t[i].name] ) {
          cerr << TS() << "Skipped because it failed in search space generation process before." << endl; continue;
        }

        _N( " * Current prediction" );
      
        function::beginXMLtag( "training", "instance=\"" + t[i].name + "\"", &ss );

        /* I) Predict! */
        function::beginXMLtag( "current-prediction", "gold-structure=\""+ t[i].y_lf.toString() +"\"", &ss );
      
        /* arg max_{x_i, y^, h^}. */
        inference_configuration_t ci = c.ci;
        vector<explanation_t>     expls_current, expls_correct;
        vector<const literal_t*>  y_literals;
        lp_inference_cache_t      cache(ci, another_kb);

        t[i].y_lf.getAllLiterals(&y_literals);
        ci.training_instance = t[i];
        ci.objfunc           = LossAugmented;
        ci.sol_cache         = sol_cache[i];
        ci.target_name       = t[i].name;
        ci.k_best            = c.ci.k_best;
        
        inference_result_type_t ret = infer(&expls_current, &cache, NULL, ci, t[i].x, another_kb, &ss );
        
        if(0 == expls_current.size()) {
          function::endXMLtag( "current-prediction", &ss );
          function::endXMLtag( "training", &ss );
          (*g_p_out) << ss.str() << endl;
          continue;
        }
        
        if(GenerationTimeout == ret) gave_up_in_generation[t[i].name] = 1;
        
        cache.printStatistics(expls_current[0].lpsol, &ss);
        if(ci.isOutput(OutputInfoProofgraph)) cache.pg.printGraph(expls_current[0].lpsol, cache.lp, cache.lprel, "id=\"i"+ toString("%d", 1+n) +"pred\" type=\"Prediction\"", &ss);
        
        function::endXMLtag( "current-prediction", &ss );

        if(GenerationTimeout == ret || ILPTimeoutNotAvailable == ret) { // || expls_current[0].lpsol.sol_type == SubOptimal) {
          V(2) cerr << TS() << log_head << "Result of inference is not available." << endl;
          ss << "<update loss=\"0\" coefficient=\"-\" />" << endl;
          function::endXMLtag( "training", &ss );
          (*g_p_out) << ss.str() << endl;
          continue;
        }

        /* Caching the solution. */
        repeat(j, cache.lp.variables.size())
          sol_cache[i][ cache.lp.variables[j].name ] = expls_current[0].lpsol.optimized_values[j];
      
        ci.sol_cache = sol_cache[i];

        p_shared_buffer->lock();
        p_shared_buffer->total_loss += expls_current[0].loss;
        p_shared_buffer->unlock();
        
        //if(Optimal != expls_current[0].lpsol.sol_type) continue;
        
        if( 0.0 == expls_current[0].loss ) {
          cerr << TS() << "No loss!" << endl;
          ss << "<update loss=\"0\" coefficient=\"0\" />" << endl;
          function::endXMLtag( "training", &ss );
          (*g_p_out) << ss.str() << endl;
          continue; }
        
        sparse_vector_t v_current = expls_current[0].fv, v_correct;
        lp_inference_cache_t another_cache(ci, another_kb);
        
        if(Structure == t[i].type_output) {
          /* I-2) k-best Hiden variable completion! */
          cerr << endl;
          _N( " * Hidden variable completion" );
        
          /* arg max_{x_i, y_i, h} */
          function::beginXMLtag( "hidden-variable-completion", "", &ss );
      
          ci.objfunc             = LabelGiven;
          //ci.method            = BnB;
          //ci.use_cache         = true;
          ci.initial_label_index = t[i].x.branches.size();
          ci.target_name         = t[i].name;
          ci.k_best              = 1; 

          logical_function_t       x_prime = t[i].x;
      
          for( uint_t j=0; j<y_literals.size(); j++ ) {
            V(5) cerr << TS() << "Label: " << y_literals[j]->toString() << endl;
            if(!y_literals[j]->predicate.isNegative()) { x_prime.branches.push_back( *y_literals[j] ); }
          }
        
          ret = infer(&expls_correct, &another_cache, NULL, ci, x_prime, another_kb, &ss);

          if(0 == expls_correct.size()) {
            function::endXMLtag( "hidden-variable-completion", &ss );
            function::endXMLtag( "training", &ss );
            (*g_p_out) << ss.str() << endl;
            continue; }

          another_cache.printStatistics(expls_correct[0].lpsol, &ss);
          cerr << TS() << "Keep going..." << endl;
          
          if(ci.isOutput(OutputInfoProofgraph))
            another_cache.pg.printGraph(expls_correct[0].lpsol, another_cache.lp, another_cache.lprel, "id=\"i"+ toString("%d", 1+n) +"hvc\" type=\"HiddenVariableCompletion\"", &ss );

          if(GenerationTimeout == ret || ILPTimeoutNotAvailable == ret) {// || expls_correct[0].lpsol.sol_type == SubOptimal) {
            function::endXMLtag( "hidden-variable-completion", &ss );
            function::endXMLtag( "training", &ss );
            (*g_p_out) << ss.str() << endl;
            continue; }
        }

        function::endXMLtag( "hidden-variable-completion", &ss );
        
        cerr << TS() << "Upadting weight vector..." << endl;
        
        sparse_vector_t             difference;
        unordered_set<store_item_t> feature_indices;
        vector<pair<sparse_vector_t*, double> > wrong_best;
        
        repeat(k, expls_current.size())
          wrong_best.push_back(make_pair(&expls_current[k].fv, expls_current[k].loss));

        sparse_vector_t myweight = p_out_sfunc->weights;
        algorithm::kbestMIRA(&myweight, &difference, &feature_indices, expls_correct[0].fv, wrong_best, c, another_cache.pg.getNormalizer(), cache.pg.getNormalizer());
        
        /* SHOW SOME STATISTICS. */
        double                      f_vecdiff = 0.0;
        stringstream                ss_content;
        
        foreach(unordered_set<store_item_t>, iter_fi, feature_indices) {
          if(0.0 == difference[*iter_fi]) continue;
          
          ss_content << toString("<element name=\"%s\" diff=\"%f\">", _sanitize(*iter_fi).c_str(), difference[*iter_fi])
                     << (myweight[*iter_fi] - difference[*iter_fi]) << " -> " << myweight[*iter_fi] << "</element>" << endl;

          f_vecdiff += fabs(difference[*iter_fi]);
        }
        
        function::beginXMLtag("update", toString("loss=\"%f\" vector-diff=\"%f\"", expls_current[0].loss, f_vecdiff), &ss);
        ss << ss_content.str();
        function::endXMLtag("update", &ss);

        foreach(sparse_vector_t, iter_wv, myweight) {
          if(0 == weight_pool.count(iter_wv->first)) {
            /* IF THE WEIGHT IS NOT INITIALIZED, PRETEND AS IT WERE NOT UPDATED FOR N-TIMES. */
            //function::initializeWeight(&weight_pool, iter_wv->first, c.ci);
            weight_pool[iter_wv->first] = iter_wv->second * num_local_vectors;
          }
          
          weight_pool[iter_wv->first] += iter_wv->second;
        }

        /* OH GOD..., NO YOU DON'T NEED IT! */
        //p_out_sfunc->weights = myweight;
        
        num_local_vectors++;
        
        p_shared_buffer->lock();
        p_shared_buffer->num_vectors++;
        p_shared_buffer->total_updates += f_vecdiff;
        p_shared_buffer->unlock();
        
        cerr << TS() << "Good." << endl;
        
        //   /* TODO: Not updated if it is not good solution. */
        //   if(0 == expls_correct.size() || s_current < s_correct) {
        //     V(2) cerr << TS() << log_head << toString("Could not find a better completion. (HVC: %f > CURR: %f)", s_correct, s_current) << endl;
        //     ss << "<update loss=\""+ toString( "%f", cache.loss.loss ) +"\" coefficient=\"-\" />" << endl; function::endXMLtag( "training", &ss );
        //     (*g_p_out) << ss.str() << endl;            
        //     continue;
        //   }

        function::endXMLtag( "training", &ss );

        (*g_p_out) << ss.str() << endl;
      }

      break;
    }

    /* CHILD:  WRITE THE RESULTS TO THE FILE, AND JUST BREAK. */
    if( 0 == forked_pid ) {
      cerr << TS() << "fork() = " << child_pid << " will exit." << endl;

      /* WRITE THE TRAINED WEIGHTS. */
      ofstream ofs(toString("/tmp/w-fork-%d.tmp", child_pid).c_str(), ofstream::out);

      ofs << num_local_vectors;
      
      /* WEIGHT VECTOR. */
      foreach(sparse_vector_t, iter_fi, weight_pool) {
        if(0.0 != iter_fi->second && 0 != iter_fi->first.toString().find(PrefixFixedWeight) && 0 != iter_fi->first.toString().find(PrefixFixedValue))
          ofs << iter_fi->first << "\t" << iter_fi->second << endl;
      }

      ofs << "_END_\t0.0" << endl;

      /* GAVE_UP_IN_GENERATION. */
      for(unordered_map<string,int>::iterator iter_gug=gave_up_in_generation.begin(); gave_up_in_generation.end()!=iter_gug; ++iter_gug)
        if(1 == iter_gug->second) ofs << iter_gug->first << endl;
      
      ofs.close();
      g_ext.finalize();
      exit(0);
    }

    /* PARENT: WAIT FOR ALL THE PROCESSES TO END, AND MERGE THE RESULTS. */
    pid_t                      ret;
    unordered_map<string, int> count_received;
      
    while((ret = waitpid(-1, NULL, WNOHANG)) >= 0) {
      if( 0 == ret ) continue;
      cerr << TS() << "Welcome home, " << ret << "." << endl;

      ifstream        ifs(toString("/tmp/w-fork-%d.tmp", ret).c_str());
      string          name, value, local_gug;

      ifs >> num_local_vectors;

      V(3) cerr << TS() << ret << ": # of added: " << num_local_vectors << endl;
      
      while(!ifs.eof()) {
        string name, value;
        getline(ifs, name, '\t'); if('\n' == name[0]) name = name.substr(1);
        getline(ifs, value, '\n');
        if("_END_" == name || ("" == name && "" == value)) break;

        count_received[name] += num_local_vectors;
        weight_pool[name]    += atof(value.c_str());
      }
      
      while( ifs >> local_gug )
        gave_up_in_generation[local_gug] = 1;
      
      ifs.close();
      remove(toString("/tmp/w-fork-%d.tmp", ret).c_str());
    }

    /* UPDATE THE WEIGHT. */
    foreach(sparse_vector_t, iter_fi, weight_pool) {
      if(0 != ((const string&)iter_fi->first).find(PrefixFixedWeight) && 0 != ((const string&)iter_fi->first).find(PrefixFixedValue))
        p_out_sfunc->weights[iter_fi->first] = iter_fi->second / (1.0*mymax(1, count_received[iter_fi->first]));
    }

    /* OUTPUT THE CURRENT MODEL. */
    function::beginXMLtag( "model" );
    (*g_p_out) << "(model ";
    for( sparse_vector_t::iterator iter_fi = p_out_sfunc->weights.begin(); p_out_sfunc->weights.end() != iter_fi; ++iter_fi ) {
      if(0 == ((const string&)iter_fi->first).find(PrefixInvisibleElement)) continue; /* Fixed weight. */
      if( 0.0 != iter_fi->second ) (*g_p_out) << "(weight \"" << _sanitize(sexp_reader_t::escape(iter_fi->first)) << "\" " << iter_fi->second << ") ";
    }
    
    (*g_p_out) << ")" << endl;
    function::endXMLtag( "model" );

    cerr << TS() << "# -- Total loss: " << p_shared_buffer->total_loss << " (avg. = " << (p_shared_buffer->total_loss / t.size()) << ")" << endl;
    cerr << TS() << "# -- Total update: " << p_shared_buffer->total_updates << " (avg. = " << (p_shared_buffer->total_updates / t.size()) << ")" << endl;

    //cout << toString("<total-update total-loss=\"%f\" minimum-loss=\"%f\" averaged-loss=\"%f\" averaged-update=\"%f\" />", total_loss, total_minimum_loss, total_loss/t.size(), total_updates/t.size()) << endl;
    
    function::endXMLtag( "learn-process" );
    
    if(c.E >= p_shared_buffer->total_updates || 0.0 == p_shared_buffer->total_loss) {
      cerr << TS() << "# ... Ok, that's enough. "
           << "Henry terminated the training procedure in " << 1+n << "-th iteration." << endl;
      break;
    }
    
    cerr << " > " << c.E << endl << "# " << endl;
  }

  repeat(s, c.S)
    delete duplicated_kbs[s];
  
}

#define _SYNCHK(x, s, e) _A(x, "Syntax error at line " << s.n_line << ":" << e << endl << s.stack.toString());

bool _moduleProcessInput( vector<training_data_t>   *p_out_t,
                          score_function_t          *p_out_sfunc,
                          knowledge_base_t          *p_out_kb,
                          learn_configuration_t     *p_out_lc,
                          inference_configuration_t *p_out_ic,
                          command_option_t          &cmd, vector<string> &args ) {

  if( 0 == args.size() ) args.push_back( "-" );

  unordered_map<string, int> confusion_matrix;
  bool                       f_classified = false, f_structured = false, f_p_found = false, f_registered_axiom;
    
  for( uint_t a=0; a<args.size(); a++ ) {
    /* Start interpreting the input. */
    istream  *p_is      = &cin;
    ifstream  file;
    size_t    file_size = 0;

    if( "-" != args[a] ) {
      file.open( args[a].c_str() );
      p_is = &file;
      
      if( file.fail() ) {
        E( "File not found: " << args[a] );
        break;
      }

      file_size = function::getFileSize(*p_is);
    }

    sexp_reader_t sr(*p_is);
    int           num_b = 0;
    
    unordered_set<long> notified;
    
    for( ; !sr.isEnd(); ++sr ) {
      if(0 != file_size) {
        int progress = (int)(10.0 * (double)sr.read_bytes / (file_size));
        if(0 == notified.count(progress)) {
          notified.insert(progress);
          cerr << TS() << args[a] << ":" << sr.read_bytes << "/" << file_size << " bytes processed (" << (int)(100.0*((double)sr.read_bytes/file_size)) << "%)." << endl;
        }
      }
      
      if( sr.stack.isFunctor(FnInclude) ) {
        _SYNCHK(2 <= sr.stack.children.size(), sr, "what is included should be a string.");
        _SYNCHK(StringStack == sr.stack.children[1]->children[0]->type, sr, "what is included should be a string.");

        repeatf(i, 1, sr.stack.children.size()) {
          vector<string> args_once( 1, sr.stack.children[i]->getString() );
          _moduleProcessInput( p_out_t, p_out_sfunc, p_out_kb, p_out_lc, p_out_ic, cmd, args_once );
        }
      }

      if( sr.stack.isFunctor(FnWeight) ) {
        if(FnModel == sr.getQueue().back()->children[0]->toString()) {
          /* Set the model weights. */
          p_out_ic->ignore_weight = false;
        
          string index  = _desanitize(sr.stack.children[1]->getString());

          if(0 == index.find("USER_") && p_out_ic->fix_user_weight) index = "!" + index;
          
          double weight = atof(sr.stack.children[2]->getString().c_str());
          V(4) cerr << TS() << "Weight loaded: " << index << ":" << weight << "(" << sr.stack.children[1]->getString() << ")" << endl;

          p_out_sfunc->weights[store_item_t(index)] = weight;

          // foreach(list<sexp_stack_t>, i, sr.getList())
          //   cerr << i->toString() << endl;
          
          sr.clearLatestStack(3);
        }
      }

      if(sr.stack.isFunctor(FnScoreFunc) && NULL != p_out_sfunc) {
        /* ADDITIONAL SCORE FUNCTION. */
        _SYNCHK(sr.isRoot(), sr, "Function " << FnScoreFunc << " should be root.");
          
        int i_name = sr.stack.findFunctorArgument(FnName), i_lf = sr.stack.findFunctorArgument(AndString),
          i_weight = sr.stack.findFunctorArgument(FnWeight);
        _SYNCHK(-1 != i_lf, sr, "no logical connectors found.");
        
        p_out_sfunc->units.push_back(score_function_t::function_unit_t(-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "?",
                                                                       logical_function_t(*sr.stack.children[i_lf]),
                                                                       -1 == i_weight ? 0.0 : atof(sr.stack.children[i_weight]->children[1]->getString().c_str())
                                                                       ));

        if(-1 != i_weight) {
          V(5) cerr << TS() << sr.stack.children[i_lf]->toString() << ": weight is fixed ("<< sr.stack.children[i_weight]->toString() <<")." << endl;
        }
      }
      
      if(sr.stack.isFunctor(FnBackgroundKnowledge)) {
        num_b++;

        /* SHOULD BE ROOT. */
        _SYNCHK(sr.isRoot(), sr, "Function " << FnBackgroundKnowledge << " should be root.")
          
        V(5) cerr << TS() << "Background knowledge " << sr.stack.toString() << " added." << endl;
        
        /* IDENTIFY THE LOGICAL FORM PART. */
        int
          i_lf = sr.stack.findFunctorArgument( ImplicationString ),
          i_inc = sr.stack.findFunctorArgument( IncString ),
          i_name = sr.stack.findFunctorArgument(FnName);
        
        _SYNCHK(-1 != i_lf || -1 != i_inc, sr, "no logical connectors found.");

        /* REGISTER THE LF. */
        bool f_register_success = false;

        if(-1 != i_lf) {
          if(FnDoNotUnify == sr.stack.children[i_lf]->children[2]->toString()) {
            /* ENUMERATE THE STOP PREDICATES. */
            logical_function_t lf( *sr.stack.children[i_lf] );

            if(Literal == lf.branches[0].opr)
              p_out_kb->registerDoNotUnify(lf.branches[0].lit.toString());
            else {
              repeat(i, lf.branches[0].branches.size())
                p_out_kb->registerDoNotUnify(lf.branches[0].branches[i].lit.toString());
            }

            f_register_success = true;
          }

          if(FnDoNotCare == sr.stack.children[i_lf]->children[2]->toString()) {
            /* ENUMERATE THE STOP ARGUMENTS. */
            logical_function_t lf( *sr.stack.children[i_lf] );

            if(Literal == lf.branches[0].opr)
              p_out_kb->registerDoNotCare(lf.branches[0].lit.toString());
            else {
              repeat(i, lf.branches[0].branches.size())
                p_out_kb->registerDoNotCare(lf.branches[0].branches[i].lit.toString());
            }

            f_register_success = true;
          }

          if(FnSearchWithConst == sr.stack.children[i_lf]->children[2]->toString()) {
            /* ENUMERATE THE STOP PREDICATES. */
            logical_function_t lf( *sr.stack.children[i_lf] );

            if(Literal == lf.branches[0].opr)
              p_out_kb->registerSearchWithConstant(lf.branches[0].lit.toString());
            else {
              repeat(i, lf.branches[0].branches.size())
                p_out_kb->registerSearchWithConstant(lf.branches[0].branches[i].lit.toString());
            }

            f_register_success = true;
          }
            
          if(FnExplainedFeatureGroup == sr.stack.children[i_lf]->children[2]->toString()) {
            /* ENUMERATE THE STOP PREDICATES. */
            logical_function_t lf( *sr.stack.children[i_lf] );

            _SYNCHK(-1 != i_name, sr, "Must have a name.");

            if(Literal == lf.branches[0].opr)
              p_out_kb->registerExplainedFeatureGroup(lf.branches[0].lit.toString(), sr.stack.children[i_name]->children[1]->getString());
            else {
              repeat(i, lf.branches[0].branches.size())
                p_out_kb->registerExplainedFeatureGroup(lf.branches[0].branches[i].lit.toString(), sr.stack.children[i_name]->children[1]->getString());
            }

            f_register_success = true;
          }
        }
        
        if(!f_register_success) {
          if(NULL != p_out_kb)
            p_out_kb->beginTransaction();

          f_registered_axiom = true;

          if(-1 != i_lf) {
            _SYNCHK(sr.stack.children[i_lf]->children.size() == 3, sr, "function '=>' takes two arguments. ");
            if(NULL != p_out_kb) f_register_success = p_out_kb->registerAxiom(sr.stack, *sr.stack.children[i_lf]);
          } else if(-1 != i_inc) {
            _SYNCHK(sr.stack.children[i_inc]->children.size() == 3, sr, "function '_|_' takes two arguments. ");
            if(NULL != p_out_kb) f_register_success = p_out_kb->registerIncAxiom(sr.stack, *sr.stack.children[i_inc]);
          }
        }
        
        if(!f_register_success) W("Background knowledge cannot be updated when you specify -b option.");
      }

      if(sr.stack.isFunctor(FnObservation) && NULL != p_out_ic) {
        /* SHOULD BE ROOT. */
        _SYNCHK(sr.isRoot(), sr, "Function "<< FnObservation <<" should be root.");
        
        /* UPDATE THE KB. */
        p_out_kb->commit();
        p_out_kb->beginTransaction();
        p_out_kb->writeBcMatrix();
        p_out_kb->commit();
        
        int
          i_x    = sr.stack.findFunctorArgument(AndString), i_y    = sr.stack.findFunctorArgument(FnTrainingLabel),
          i_name = sr.stack.findFunctorArgument(FnName),    i_cls  = -1, i_structure = -1;
        
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

        /* For an example-specific training. */
        if( has_key( cmd, 'p' ) ) {
          if( -1 == i_name ) continue;
          if(0 == cmd['p'].find("/") ?
             !pcrecpp::RE(cmd['p'].substr(1)).FullMatch(sr.stack.children[i_name]->children[1]->getString()) :
              sr.stack.children[i_name]->children[1]->getString() != cmd[ 'p' ])
            continue;
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
          
          lp_inference_cache_t  cache(*p_out_ic, *p_out_kb);
          vector<explanation_t> expls;

          (*g_p_out) << "<result-inference target=\"" << (-1 != i_name ? sr.stack.children[i_name]->children[1]->getString() : "") << "\">" << endl;

          p_out_ic->target_name       = the_name;
          p_out_ic->training_instance = td;
          
          algorithm::infer(&expls, &cache, NULL, *p_out_ic, obs, *p_out_kb);
        
          /* Basic output. */
          if(0 == expls.size())
            cache.printStatistics();

          repeat(k, expls.size()) {
            vector<const literal_t*> literals_obs;
            obs.getAllLiterals(&literals_obs);

            cache.printStatistics(expls[k].lpsol);
            if(p_out_ic->isOutput(OutputInfoProofgraph)) cache.pg.printGraph(expls[k].lpsol, cache.lp, cache.lprel, "", &cout, &expls[k].lf);
        
            if( -1 != i_y ) {
              if( -1 != i_cls ) {
                confusion_matrix[ (expls[k].lpsol.optimized_obj >= 0 ? "+1" : "-1") + sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() ]++;
                f_classified = true;
              
                (*g_p_out) << "<task-result"
                           << " predicted-class=\""<< (expls[k].lpsol.optimized_obj >= 0 ? "+1" : "-1") << "\""
                           << " gold-class=\""<< sr.stack.children[ i_y ]->children[ i_cls ]->children[1]->getString() << "\""
                           << " target=\""<< the_name <<"\""
                           << " loss=\""<< cache.loss.loss <<"\""
                           << " loss-msg=\""<< cache.loss.loss_msg <<"\" />" << endl;
              } else {
                confusion_matrix[ 0.0 == cache.loss.loss ? "+1" : "-1" ]++;
                f_structured = true;
              
                (*g_p_out) << "<task-result"
                           << " gold-structure=\""<< logical_function_t( *sr.stack.children[ i_y ]->children[ i_structure ] ).toString() << "\""
                           << " target=\""<< the_name <<"\""
                           << " loss=\""<< cache.loss.loss <<"\""
                           << " loss-msg=\""<< cache.loss.loss_msg <<"\" />" << endl;
              }
            }
          }
          
          (*g_p_out) << "</result-inference>" << endl;

        }

      }
    }

    if( "-" != args[a] ) file.close();

    _A(sr.getQueue().size() == 1, "Syntax error: too few parentheses. Around here, or line " << num_b << " (typically the expression followed by this):" << endl << sr.stack.toString());
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

  /* Compile the knowledge base. */
  cerr << TS() << "Inserting the source axioms into the DB..." << endl;

  knowledge_base_t kb(true, cmd['o']);
  kb.newTable();
  
  _moduleProcessInput(NULL, NULL, &kb, NULL, NULL, cmd, args);
  
  cerr << TS() << "Done." << endl;
  cerr << TS() << "Writing backward-chaining matrix..." << endl;
  kb.commit();

  kb.beginTransaction();
  kb.writeBcMatrix();
  kb.commit();

  cerr << TS() << "Done." << endl;
  cerr << TS() << "Defragmenting the database..." << endl;
  kb.vacuum();
  
  cerr << TS() << "Bon Appetit!" << endl;
  
  return true;
  
}

bool _moduleProcessInferOptions( inference_configuration_t *p_out_con, command_option_t &cmd ) {
  
  if( !has_key( cmd, 'd' ) ) cmd[ 'd' ] = "6";
  if( !has_key( cmd, 'T' ) ) cmd[ 'T' ] = "9999";
  if( !has_key( cmd, 't' ) ) cmd[ 't' ] = "1";
  if( !has_key( cmd, 'O' ) ) cmd[ 'O' ] = "";
  if( !has_key( cmd, 'i' ) ) cmd[ 'i' ] = "bnb";
  if( !has_key( cmd, 'k' ) ) cmd[ 'k' ] = "1";

  p_out_con->depthlimit           = atoi( cmd[ 'd' ].c_str() );
  p_out_con->timelimit            = atof( cmd[ 'T' ].c_str() );
  p_out_con->nbthreads            = atof( cmd[ 't' ].c_str() );
  p_out_con->extension_module     = cmd[ 'e' ];
  p_out_con->k_best               = atoi(cmd[ 'k' ].c_str());
  p_out_con->explanation_disjoint = has_key(cmd, 'D');
  p_out_con->use_only_user_score  = has_key(cmd, 'u');
  p_out_con->fix_user_weight      = has_key(cmd, 'U');
  p_out_con->scaling_score_func   = has_key(cmd, 's');
  p_out_con->no_prior             = has_key(cmd, 'z');
  p_out_con->no_explained         = has_key(cmd, 'I');
  p_out_con->no_pruning           = has_key(cmd, 'n');

  if(has_key(cmd, 'X')) {
    p_out_con->prohibited_literals.insert(atoi(cmd['X'].c_str()));
  }
  
  if(has_key(cmd, 'x')) {
    p_out_con->hypothesized_literals.insert(atoi(cmd['x'].c_str()));
  }

  if( has_key( cmd, 'e' ) ) {
    g_ext.filename = p_out_con->extension_module;
    g_ext.args     = cmd[ 'f' ];
  }
    
  if( "ls" == cmd['i'] )  p_out_con->method       = LocalSearch;
  else if( "rlp" == cmd['i'] )  p_out_con->method = RoundLP;
  else if( "bnb" == cmd['i'] )  p_out_con->method = BnB;
  else if( "cpi" == cmd['i'] )  p_out_con->method = CuttingPlaneBnB;
  else if( "ntr" == cmd['i'] )  p_out_con->method = NoTransitivity;
  else if( "lazy" == cmd['i'] )  p_out_con->method = LazyBnB;

  p_out_con->p_sfunc->tp = WeightedAbduction;

  p_out_con->output_info = cmd[ 'O' ];
  if( atoi( cmd['v'].c_str() ) >= 2 ) p_out_con->output_info += OutputInfoILPlog;

  return true;
  
}

bool _moduleInfer(command_option_t &cmd, vector<string> &args) {

  score_function_t          sfunc;
  inference_configuration_t c( sfunc );
  knowledge_base_t          kb(has_key(cmd, 'b') ? false : true, has_key(cmd, 'b') ? cmd['b'] : ":memory:");
  
  if(has_key(cmd, 'c')) {
    kb.setContextDatabase(cmd['c']);
    cerr << TS() << "Contextual pruning activated." << endl;
  }

  if(has_key(cmd, 'h')) {
    kb.num_branches = atoi(cmd['h'].c_str());
  }

  /* Setting the parameters. */
  c.ignore_weight = true;
  
  _moduleProcessInferOptions( &c, cmd );
  _moduleProcessInput( NULL, &sfunc, &kb, NULL, &c, cmd, args );
  
  return true;
  
}

bool _moduleLearn( command_option_t &cmd, vector<string> &args ) {

  vector<training_data_t> t;
  score_function_t        sfunc;
  knowledge_base_t        kb(has_key(cmd, 'b') ? false : true, has_key(cmd, 'b') ? cmd['b'] : ":memory:");
  learn_configuration_t   c( sfunc );

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

  _moduleProcessInput( &t, &sfunc, &kb, &c, &c.ci, cmd, args );
  
  algorithm::learn( &sfunc, c, t, kb );

  return true;
  
}

int main( int argc, char **pp_args ) {

  string exec_options;
  
  for( int i=1; i<argc; i++ ) exec_options += (1 != i ? " " : "") + string( pp_args[i] );
  
  if( 1 == argc ) { cerr << str_usage << endl; return 1; }

  command_option_t cmd;
  vector<string>   args;
  function::getParsedOption( &cmd, &args, "IzsUDh:m:uv:i:r:b:C:N:nt:T:w:E:O:o:p:d:c:e:f:k:S:X:x:", argc, pp_args );

  if( !has_key( cmd, 'm' ) ) { cerr << str_usage << endl; return 1; }
  srand(has_key(cmd, 'r') ? atoi(cmd['r'].c_str()) : time(NULL));
  
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
