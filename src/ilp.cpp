
#include "defs.h"
#include "signal.h"
#include "math.h"

#ifdef USE_GUROBI
#include "gurobi_c++.h"

#define GRBEXECUTE(x) \
  try{ x; } \
  catch( GRBException e ) { cerr << TS() << __FILE__ << ":" << __LINE__ << ": " << e.getErrorCode() << ": " << e.getMessage() << endl; }

#define GRBEXECUTEMSG(x, y)                          \
  try{ x; } \
  catch( GRBException e ) { cerr << TS() << __FILE__ << ":" << __LINE__ << ": " << e.getErrorCode() << ": " << e.getMessage() << ": " << y << endl; }

typedef unordered_map<int, GRBVar> gurobi_varmap_t;

GRBModel *g_p_model = NULL;

inline void _cb_stop_ilp( int sig_num ) {

  signal( SIGINT, _cb_stop_ilp );
  g_p_model->terminate();
  
}

class gurobi_callback_t : public GRBCallback {
  const linear_programming_problem_t &m_lp;
  const lp_problem_mapping_t         &m_lprel;
  lp_inference_cache_t         &m_cache;
  gurobi_varmap_t              &m_varmap;

  const inference_configuration_t    &m_conf;
  
public:
  int                   num_activated, num_evaluated;
  double                m_timeout, m_last_best;
  bool                  m_last_checked, m_exact_try;
  vector<GRBTempConstr> m_added_constr;
  bool                  m_gap_skip;
  
  inline gurobi_callback_t( const linear_programming_problem_t& _lp, const lp_problem_mapping_t &_lprel, lp_inference_cache_t &_cache, const inference_configuration_t &_conf, gurobi_varmap_t& _varmap ) :
    m_lp( _lp ), m_lprel( _lprel ), m_cache( _cache ), m_varmap( _varmap ), m_conf( _conf ), num_activated(0), num_evaluated(0), m_timeout(0), m_last_best(0.0), m_last_checked(false), m_exact_try(false),
    m_gap_skip(false)
  {};

  inline int _getCorefVar( store_item_t t1, store_item_t t2 ) {
    store_item_t t1s = t1, t2s = t2; if( t1s > t2s ) swap( t1s, t2s );
    
    pairwise_vars_t::const_iterator k1 = m_lprel.pp2v.find(t1s);
    if( m_lprel.pp2v.end() == k1 ) return -1;

    unordered_map<store_item_t, int>::const_iterator k2 = k1->second.find(t2s);
    return k1->second.end() == k2 ? -1 : k2->second;
  }
  
  inline void callback() {
    switch( where ) {
    case GRB_CB_MIPSOL: {
      V(1) cerr << TS() << "New solution! (Obj:"<< getDoubleInfo( GRB_CB_MIPSOL_OBJ ) <<")" << endl;

      if( CuttingPlaneBnB != m_conf.method ) break;
      if(!m_gap_skip) break;
      
      double f_gap = (getDoubleInfo( GRB_CB_MIPSOL_OBJBND ) - getDoubleInfo( GRB_CB_MIPSOL_OBJ )) / getDoubleInfo( GRB_CB_MIPSOL_OBJ );
      
      num_evaluated++;
      V(1) cerr << "CPI: " << "I=" << num_evaluated << ": New solution! (Obj = "<< getDoubleInfo( GRB_CB_MIPSOL_OBJ ) <<"Gap = "<< f_gap <<")" << endl;

      if( !m_exact_try ) {
        if( fabs(f_gap) >= 0.5 ) { m_last_checked = false; break; }
      }

      m_last_checked   = true;
      
      /* Identify activated unification. */
      variable_cluster_t         vc;
      unordered_map<int, double> sol_cache;

      /* Create equivalent clusters. */
      unordered_map<store_item_t, unordered_set<store_item_t> > potentially_unified;

      foreachc( pairwise_vars_t, iter_t1, m_lprel.pp2v )
        for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
          potentially_unified[iter_t1->first].insert( iter_t2->first );
          potentially_unified[iter_t2->first].insert( iter_t1->first );
          sol_cache[iter_t2->second] = getSolution( m_varmap[ iter_t2->second ] );
          //if( 0.5 < sol_cache[iter_t2->second] ) vc.add( iter_t1->first, iter_t2->first );
        }

      foreachc( pairwise_vars_t, iter_t1, m_lprel.pp2v )
        for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
          store_item_t t1 = iter_t1->first, t2 = iter_t2->first;

          foreach( unordered_set<store_item_t>, iter_tu, potentially_unified[t1] ) {
            if( potentially_unified[t2].end() == potentially_unified[t2].find(*iter_tu) ) continue;

            int v_ij = _getCorefVar(t1, t2), v_ik = _getCorefVar(t1, *iter_tu), v_jk = _getCorefVar(t2, *iter_tu);
            int s_ij = sol_cache[v_ij], s_ik = sol_cache[v_ik], s_jk = sol_cache[v_jk];

            if( 2 != (s_ij+s_ik+s_jk) ) continue;

            if( 1 == s_ij && 1 == s_ik )      { addLazy( -m_varmap[v_ij] - m_varmap[v_ik] + m_varmap[v_jk] >= -1 ); m_added_constr.push_back( -m_varmap[v_ij] - m_varmap[v_ik] + m_varmap[v_jk] >= -1 ); }
            else if( 1 == s_ij && 1 == s_jk ) { addLazy( -m_varmap[v_ij] - m_varmap[v_jk] + m_varmap[v_ik] >= -1 ); m_added_constr.push_back( -m_varmap[v_ij] - m_varmap[v_jk] + m_varmap[v_ik] >= -1 ); }
            else if( 1 == s_ik && 1 == s_jk ) { addLazy( -m_varmap[v_ik] - m_varmap[v_jk] + m_varmap[v_ij] >= -1 ); m_added_constr.push_back( -m_varmap[v_ik] - m_varmap[v_jk] + m_varmap[v_ij] >= -1 ); }

            num_activated++;

            // cerr << g_store.claim(t1) << "," << g_store.claim(t2) << "(" << sol_cache[v_ij] << ")" << ","
            //      << g_store.claim(t1) << "," << g_store.claim(*iter_tu) << "(" << sol_cache[v_ik] << ")" << ","
            //      << g_store.claim(t2) << "," <<  g_store.claim(*iter_tu) << "(" << sol_cache[v_jk] << ")" << "," << endl;

          }

        }
      
      break;
      
      // repeat( i, m_lp.constraints.size() ) {
      //   if( !m_lp.constraints[i].is_lazy ) continue;

      //   double                 val = 0.0;
      //   const lp_constraint_t &con = m_lp.constraints[i];
        
      //   repeat( j, con.vars.size() )
      //     val += con.coes[j] * getSolution( m_varmap[ con.vars[j] ] );

      //   if( !con.isSatisfied(val) ) {
      //     GRBLinExpr expr_lin;

      //     repeat( j, con.vars.size() )
      //       expr_lin  += con.coes[j] * m_varmap[ con.vars[j] ];

      //     GRBEXECUTE(
      //                if( LessEqual == con.opr )         addLazy( expr_lin, GRB_LESS_EQUAL, con.rhs );
      //                else if( GreaterEqual == con.opr ) addLazy( expr_lin, GRB_GREATER_EQUAL, con.lhs );
      //                else if( Equal == con.opr )        addLazy( expr_lin, GRB_EQUAL, con.rhs );
      //                else if( Range == con.opr ) {      addLazy( expr_lin, GRB_LESS_EQUAL, con.rhs ); addLazy( expr_lin, GRB_GREATER_EQUAL, con.lhs ); }
      //                );

      //     num_activated++;
          
      //     con.is_lazy = false;
      //   }
      // }
      break; }
    }
  }
    
};

inline int _getCorefVar( store_item_t t1, store_item_t t2, const lp_problem_mapping_t &lprel ) {
  store_item_t t1s = t1, t2s = t2; if( t1s > t2s ) swap( t1s, t2s );
    
  pairwise_vars_t::const_iterator k1 = lprel.pp2v.find(t1s);
  if( lprel.pp2v.end() == k1 ) return -1;

  unordered_map<store_item_t, int>::const_iterator k2 = k1->second.find(t2s);
  return k1->second.end() == k2 ? -1 : k2->second;
}

ilp_solution_type_t function::solveLP_BnB(vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache ) {

  GRBEnv            env;
  GRBModel          model( env );

  gurobi_varmap_t   var_map;
  gurobi_callback_t cb( lp, lprel, *p_out_cache, c, var_map );
  
  cb.m_timeout = c.timelimit;

  V(2) cerr << TS() << "Converting the problem into LP optimization problem..." << endl;
  
  /* Create variables. */
  GRBEXECUTE(
  repeat( i, lp.variables.size() ) {
    if( InvalidFixedValue != lp.variables[i].fixed_val ) {
      var_map[i] = model.addVar( lp.variables[i].fixed_val, lp.variables[i].fixed_val,
                                 lp.variables[i].obj_val, lp.variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == lp.variables[i].ub - lp.variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    } else {
      var_map[i] = model.addVar( lp.variables[i].lb, lp.variables[i].ub,
                                 lp.variables[i].obj_val, lp.variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == lp.variables[i].ub - lp.variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    }
    
  }
             );

  GRBEXECUTE( model.update() );

  /* Set MIP starts. */
  GRBEXECUTE(
  repeat( i, lp.variables.size() ) {
  
    if( -9999.0 != lp.variables[i].init_val && !lp.variables[i].isFixed() )
      var_map[i].set( GRB_DoubleAttr_Start, lp.variables[i].init_val );
  }
  );
  
  /* Create constraints. */
  repeat( i, lp.constraints.size() ) {
    if( !lp.constraints[i].is_active || lp.constraints[i].is_lazy ) continue;

    const lp_constraint_t &con = lp.constraints[i];
    GRBLinExpr             expr_lin;

    repeat( j, con.vars.size() )
      expr_lin  += con.coes[j] * var_map[ con.vars[j] ];
    
    GRBEXECUTEMSG(
    switch( con.opr ) {
    case SOS1:
    case SOS2: {
      vector<GRBVar> sosv;
      repeat( j, con.vars.size() ) sosv.push_back( var_map[ con.vars[j] ] );
      model.addSOS( &sosv[0], &con.coes[0], sosv.size(), SOS1 == con.opr ? GRB_SOS_TYPE1 : GRB_SOS_TYPE2 );
      break; }
    case Equal: {        model.addConstr( expr_lin, GRB_EQUAL, con.lhs, con.name.substr(0, 32) );         break; }
    case LessEqual: {    model.addConstr( expr_lin, GRB_LESS_EQUAL, con.rhs, con.name.substr(0, 32) );    break; }
    case GreaterEqual: { model.addConstr( expr_lin, GRB_GREATER_EQUAL, con.rhs, con.name.substr(0, 32) ); break; }
    case Range: {        model.addRange( expr_lin, con.lhs, con.rhs, con.name.substr(0, 32) );            break; }
    default:             cerr << TS() << "SolveLP_BnB: Unknown constraint type." << endl;
    }, lp.constraints[i].toString( lp.variables )
                  );
  }

  /* State a maximization objective. */
  model.set( GRB_IntAttr_ModelSense, GRB_MAXIMIZE );
  
  /* Go to hell! */
  GRBEXECUTE(model.getEnv().set( GRB_IntParam_OutputFlag, c.is_ilp_verbose ? 1 : 0 );
             model.getEnv().set( GRB_DoubleParam_TimeLimit, c.timelimit );
             model.getEnv().set( GRB_IntParam_Threads, c.nbthreads );
             //model.getEnv().set( GRB_IntParam_MIPFocus, 2 );
             );

  if( InvalidCutoff != lp.cutoff ) model.getEnv().set( GRB_DoubleParam_Cutoff, lp.cutoff );
  if( string::npos != c.output_info.find("GAP") && CuttingPlaneBnB == c.method ) { cb.m_gap_skip=true; GRBEXECUTE(model.getEnv().set( GRB_IntParam_DualReductions, 0 )); }
  //GRBEXECUTE(model.getEnv().set( GRB_IntParam_DualReductions, 0 ));
                                               
  GRBEXECUTE(model.setCallback( &cb ));
  
  if( c.is_ilp_verbose ) beginXMLtag( "ilp-log", "solver=\"gurobi\"" );

  double time_start     = getTimeofDaySec();
  bool   f_got_solution = false;
  
  g_p_model = &model;
  
  if( CuttingPlaneBnB == c.method ) {

    if( string::npos != c.output_info.find("GAP") ) {
      signal( SIGINT, _cb_stop_ilp );
      GRBEXECUTE(model.optimize());
      signal( SIGINT, catch_int );
      
    } else {
    
      int n, num_constraints_added = 0;
      lp_solution_t sol(lp);
    
      for( n=0; !c.isTimeout(); n++ ) {

        cerr << TS() << "CPI: I=" << n << ": Started." << endl;

        model.getEnv().set( GRB_DoubleParam_TimeLimit, c.timelimit - (getTimeofDaySec() - time_start) );

        signal( SIGINT, _cb_stop_ilp );
        GRBEXECUTE( model.optimize() );
        signal( SIGINT, catch_int );
      
        if( GRB_TIME_LIMIT == model.get(GRB_IntAttr_Status) ) { cerr << TS() << "CPI: I=" << n << ": Timeout." << endl; break; }
        else if( GRB_CUTOFF == model.get(GRB_IntAttr_Status) )     { cerr << TS() << "CPI: I=" << n << ": Cutoff." << endl; break; }
        else if( GRB_INFEASIBLE == model.get(GRB_IntAttr_Status) ) { cerr << TS() << "CPI: I=" << n << ": Infeasible." << endl; f_got_solution = false; break; }
        else if( GRB_OPTIMAL != model.get(GRB_IntAttr_Status) ) {cerr << TS() << "CPI: I=" << n << ": ?" << endl; f_got_solution = false; break; }

        /* Any constraints violated? */
        int                        num_constraints_locally_added = 0;

        for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
          vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
      
          for( uint_t i=0; i<variables.size(); i++ ) {
            for( uint_t j=i+1; j<variables.size(); j++ ) {
              if( c.isTimeout() ) goto BED;
        
              store_item_t t1 = variables[i], t2 = variables[j];
              unordered_set<store_item_t> &vs = p_out_cache->evc.clusters[p_out_cache->evc.map_v2c[t1]];

              /* TRANSITIVE RELATIONS SHOULD HOLD WITH THE OTHER VARIABLES
                 IN THE SAME EQV CLUSTER. */
              foreach( unordered_set<store_item_t>, iter_tu, vs ) {
                if(c.isTimeout()) goto BED;
                if(*iter_tu == t1 || *iter_tu == t2) continue;

                int    v_ij = _getCorefVar(t1, t2, lprel), v_ik = _getCorefVar(t1, *iter_tu, lprel), v_jk = _getCorefVar(t2, *iter_tu, lprel);
                if(-1 == v_ij || -1 == v_ik || -1 == v_jk) continue;
            
                double s_ij = var_map[v_ij].get(GRB_DoubleAttr_X), s_ik = var_map[v_ik].get(GRB_DoubleAttr_X), s_jk = var_map[v_jk].get(GRB_DoubleAttr_X);

                if( -s_ij - s_jk + s_ik < -1 ) { model.addConstr( -var_map[v_ij] - var_map[v_jk] + var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
                if( -s_ij + s_jk - s_ik < -1 ) { model.addConstr( -var_map[v_ij] + var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
                if(  s_ij - s_jk - s_ik < -1 ) { model.addConstr(  var_map[v_ij] - var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
              }
            
            } }
        }
      
        // foreachc( pairwise_vars_t, iter_t1, p_out_lprel->pp2v )
        //   for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
        //     if( c.isTimeout() ) goto BED;
        //     if( !p_out_cache->evc.isInSameCluster(iter_t1->first, iter_t2->first) ) continue;
          
        //     store_item_t                 t1 = iter_t1->first, t2 = iter_t2->first;
        //     unordered_set<store_item_t> &vs = p_out_cache->evc.clusters[p_out_cache->evc.map_v2c[t1]];

        //     /* TRANSITIVE RELATIONS SHOULD HOLD WITH THE OTHER VARIABLES
        //        IN THE SAME EQV CLUSTER. */
        //     foreach( unordered_set<store_item_t>, iter_tu, vs ) {
        //       if(c.isTimeout()) goto BED;
        //       if(*iter_tu == t1 || *iter_tu == t2) continue;

        //       int    v_ij = _getCorefVar(t1, t2, *p_out_lprel), v_ik = _getCorefVar(t1, *iter_tu, *p_out_lprel), v_jk = _getCorefVar(t2, *iter_tu, *p_out_lprel);
        //       if(-1 == v_ij || -1 == v_ik || -1 == v_jk) continue;
            
        //       double s_ij = var_map[v_ij].get(GRB_DoubleAttr_X), s_ik = var_map[v_ik].get(GRB_DoubleAttr_X), s_jk = var_map[v_jk].get(GRB_DoubleAttr_X);

        //       if( -s_ij - s_jk + s_ik < -1 ) { model.addConstr( -var_map[v_ij] - var_map[v_jk] + var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //       if( -s_ij + s_jk - s_ik < -1 ) { model.addConstr( -var_map[v_ij] + var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //       if(  s_ij - s_jk - s_ik < -1 ) { model.addConstr(  var_map[v_ij] - var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //     }
        //   }


        num_constraints_added += num_constraints_locally_added;
      
        cerr << TS() << "CPI: I=" << n << ": Finished. Obj:"<< model.get(GRB_DoubleAttr_ObjVal) <<": Violated:" << num_constraints_locally_added << " (Total: " << num_constraints_added << ")" << endl;

        f_got_solution = true;
      
        repeat( j, lp.variables.size() )
          sol.optimized_values[j] = var_map[j].get(GRB_DoubleAttr_X);

        sol.optimized_obj = model.get(GRB_DoubleAttr_ObjVal);
      
        if( 0 == num_constraints_locally_added ) { cerr << TS() << "CPI: I=" << n << ": No violation." << endl; break; }
      
        model.reset();
      
        continue;
      
      BED:
        break;
      
      }

      if(f_got_solution) p_out_sols->push_back(sol);
        

      if( !c.isTimeout() ) {
        cerr << TS() << "CPI: Finished: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
      } else {
        cerr << TS() << "CPI: Finished: Timeout: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
      }
    }
    
  } else {
    repeat(k, c.k_best) {      
      for(int lv=0;;lv++) {
        int n_prohibited = 0;
      
        repeat(i, lp.variables.size()) {
          if(lp.variables[i].opt_level > lv) { var_map[i].set(GRB_DoubleAttr_UB, 0.0); n_prohibited++; }
          else                                      if(!lp.variables[i].isFixed()) var_map[i].set(GRB_DoubleAttr_UB, 1.0);
        }
      
        signal( SIGINT, _cb_stop_ilp );
        GRBEXECUTE(model.optimize());
        signal( SIGINT, catch_int );

        if(0 == n_prohibited) break;
            
        // model.reset();

        // repeat( j, lp.variables.size() )
        //   var_map[j].set(GRB_DoubleAttr_Start, var_map[j].get(GRB_DoubleAttr_X));
      }

      if(0 != model.get(GRB_IntAttr_SolCount)) {
        lp_solution_t sol(lp);
    
        repeat( j, lp.variables.size() )
          sol.optimized_values[j] = var_map[j].get(GRB_DoubleAttr_X);

        sol.optimized_obj = model.get(GRB_DoubleAttr_ObjVal);
        sol.sol_type      = GRB_OPTIMAL == model.get(GRB_IntAttr_Status) ? Optimal : SubOptimal;
    
        p_out_sols->push_back(sol);

        /* Degrade the current solution. */
        GRBVar     penalizer = model.addVar(0, 1, -100.0, GRB_BINARY);
        GRBLinExpr exprSol;
        double     rhs = 0, num_neg = 0;

        repeat(j, lp.variables.size())
          if(string::npos != lp.variables[j].name.find("/EXPLAINED_BY")) {
            rhs += 1.0;
            
            if(1.0 == sol.optimized_values[j]) exprSol += 1.0 * var_map[j];
            else                               { exprSol += -1.0 * var_map[j]; num_neg += 1.0; }
          }

        exprSol += -1.0 * penalizer;

        model.update();
        
        GRBEXECUTE( model.addRange(exprSol, -num_neg, rhs-1.0-num_neg) );
      }
    }
  }
  
  if( NULL != p_out_cache ) p_out_cache->elapsed_ilp = getTimeofDaySec() - time_start;
  
  if( c.is_ilp_verbose ) endXMLtag( "ilp-log" );

  if( !f_got_solution && 0 == model.get(GRB_IntAttr_SolCount) ) {
    if( GRB_INFEASIBLE == model.get(GRB_IntAttr_Status) ) {
      GRBEXECUTE(
                 model.computeIIS();
                 GRBConstr *cnstrs = model.getConstrs();

                 repeat(i, (uint_t)model.get(GRB_IntAttr_NumConstrs)) {
                   if (cnstrs[i].get(GRB_IntAttr_IISConstr) == 1) {
                     cout << "Infeasible: " << cnstrs[i].get(GRB_StringAttr_ConstrName) << endl;
                   } }
                 
                 delete[] cnstrs;
                 );
    }
        
    return NotAvailable;
  }

  /* RETURN THE OBSERVATION IF THERE IS NO SOLUTION FOUND. */
  if(0 == p_out_sols->size()) {
    lp_solution_t sol(lp);
    sol.optimized_obj = 0.0;
    sol.sol_type      = SubOptimal;
    
    repeat( i, lp.variables.size() ) {
      if( lp.variables[i].isFixed() )                sol.optimized_values[i] = lp.variables[i].fixed_val;
      else if( -9999.0 != lp.variables[i].init_val ) sol.optimized_values[i] = lp.variables[i].init_val;
      else                                           sol.optimized_values[i] = lp.variables[i].lb;
      
      sol.optimized_obj += lp.variables[i].obj_val * sol.optimized_values[i];
    }
  }
  
  return c.isTimeout() ? SubOptimal :
    ((BnB == c.method ?
      GRB_OPTIMAL == model.get(GRB_IntAttr_Status) :
     GRB_OPTIMAL == model.get(GRB_IntAttr_Status) || GRB_CUTOFF == model.get(GRB_IntAttr_Status)) ?
     Optimal : SubOptimal);
  
}

#endif /* #ifdef GUROBI */



#ifdef USE_LOCALSOLVER
#include "localsolver.h"

using namespace localsolver;

ilp_solution_type_t function::solveLP_LS(vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache ) {

  LocalSolver ls;
  LSModel *p_model = ls.getModel();

  LSExpression *p_cost = p_model->createExpression(O_Sum);

  /* Convert variables. */
  unordered_map<int, LSExpression*> var_map;
  
  repeat( i, lp.variables.size() ) {
    if( lp.variables[i].isFixed() ) {
      LSExpression *p_var = p_model->createExpression( O_Bool );
      var_map[i] = p_var;

      if( 0 != lp.variables[i].obj_val ) {
        p_cost->addOperand(p_model->createExpression(O_Prod, lp.variables[i].obj_val, p_var));
        p_model->addConstraint(p_model->createExpression(O_Eq, p_var, lp.variables[i].fixed_val));
      }
    } else {
      LSExpression *p_var = p_model->createExpression( O_Bool );
      var_map[i] = p_var;

      if( 0 != lp.variables[i].obj_val ) p_cost->addOperand( p_model->createExpression( O_Prod, lp.variables[i].obj_val, p_var ) );
    }
  }

  if( 0 == p_cost->getNbOperands() )
    p_cost->addOperand( p_model->createConstant( 0.0 ) );

  /* Convert constraints. */
  repeat( i, lp.constraints.size() ) {
    if( !lp.constraints[i].is_active ) continue;
    
    LSExpression *p_sum = p_model->createExpression( O_Sum );

    repeat( j, lp.constraints[i].vars.size() )
      p_sum->addOperand( p_model->createExpression( O_Prod, lp.constraints[i].coes[j], var_map[ lp.constraints[i].vars[j] ] ) );
    
    switch( lp.constraints[i].opr ) {
    case Equal: {      
      p_model->addConstraint( p_model->createExpression( O_Eq, p_sum, lp.constraints[i].lhs ) );
      break; }
      
    case LessEqual: {
      p_model->addConstraint( p_model->createExpression( O_Leq, p_sum, lp.constraints[i].rhs ) );
      break; }

    case GreaterEqual: {
      p_model->addConstraint( p_model->createExpression( O_Geq, p_sum, lp.constraints[i].lhs ) );
      break; }

    case Range: {
      p_model->addConstraint( p_model->createExpression( O_Leq, p_sum, lp.constraints[i].rhs ) );
      p_model->addConstraint( p_model->createExpression( O_Geq, p_sum, lp.constraints[i].lhs ) );
      break; }
      
    }
  }

  /* State a maximization objective. */
  p_model->addObjective( p_cost, OD_Maximize );

  /* Go to hell! */
  try {
    p_model->close();
  } catch( LSException* p_e ) {
    cerr << TS() << p_e->getMessage() << endl;
  }
  
  LSPhase *p_phase = ls.createPhase();
  p_phase->setTimeLimit( c.timelimit );
  
  ls.getParam()->setNbThreads( c.nbthreads );
  ls.getParam()->setVerbosity( 1 );
  ls.solve();

  /* Update the optimized value based on the solution of LP. */
  lp_solution_t sol(lp);
  sol.sol_type      = SubOptimal;
  sol.optimized_obj = 0.0;
  
  repeat( i, lp.variables.size() ) {
    sol.optimized_values[i]  = var_map[i]->getValue();
    sol.optimized_obj       += sol.optimized_values[i] * lp.variables[i].obj_val;
  }

  p_out_sols->push_back(sol);

  return SubOptimal;
  
}

#endif /* #ifdef LOCAL_SOLVER */






/* GRAVE. */
    // for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->evc.clusters.begin(); p_out_cache->evc.clusters.end()!=iter_c2v; ++iter_c2v ) {
      
    //   vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );
      
    //   for( uint_t i=0; i<variables.size(); i++ ) {
    //     for( uint_t j=i+1; j<variables.size(); j++ ) {
    //       for( uint_t k=j+1; k<variables.size(); k++ ) {
    //         store_item_t ti = variables[i], tj = variables[j], tk = variables[k];
    //         int
    //           v_titj        = _getCorefVar(ti, tj, *p_out_lprel),
    //           v_tjtk        = _getCorefVar(tj, tk, *p_out_lprel),
    //           v_titk        = _getCorefVar(ti, tk, *p_out_lprel);

    //         if( c.isTimeout() ) goto BED;
    //         if( -1 == v_titj || -1 == v_tjtk || -1 == v_titk ) continue;

    //         double s_ij = var_map[v_titj].get(GRB_DoubleAttr_X), s_ik = var_map[v_titk].get(GRB_DoubleAttr_X), s_jk = var_map[v_tjtk].get(GRB_DoubleAttr_X);
            
    //         if( -s_ij - s_jk + s_ik < -1 ) { model.addConstr( -var_map[v_titj] - var_map[v_tjtk] + var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
    //         if( -s_ij + s_jk - s_ik < -1 ) { model.addConstr( -var_map[v_titj] + var_map[v_tjtk] - var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
    //         if(  s_ij - s_jk - s_ik < -1 ) { model.addConstr(  var_map[v_titj] - var_map[v_tjtk] - var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
            
    //       } } }
    // }
    
