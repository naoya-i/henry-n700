
#include "defs.h"
#include "signal.h"
#include "math.h"

#include <algorithm>

#ifdef USE_GUROBI
#include "gurobi_c++.h"

#define GRBEXECUTE(x) \
  try{ x; } \
  catch(GRBException &e) { E("Gurobi threw exception ("<< __FILE__ << ":" << __LINE__ << "): " << e.getErrorCode() << ": " << e.getMessage()); }

#define GRBEXECUTE_OR_DIE(x, y)                          \
  try{ x; } \
  catch(GRBException &e) { E("Gurobi threw exception: " << e.getErrorCode() << ": " << e.getMessage()); return y; }

#define GRBEXECUTEMSG(x, y)\
  try{ x; } \
  catch(GRBException &e) { E("Gurobi threw exception: " << e.getErrorCode() << ": " << e.getMessage() << ": " << y); }

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
      break;

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

            int v_ij = m_cache.createNodeVar(m_cache.pg.getSubNode(t1, t2), false),
              v_ik = m_cache.createNodeVar(m_cache.pg.getSubNode(t1, *iter_tu), false),
              v_jk = m_cache.createNodeVar(m_cache.pg.getSubNode(t2, *iter_tu), false);
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

  GRBEnv            *p_env = NULL;
  GRBModel          *p_model = NULL;

  GRBEXECUTE_OR_DIE(p_env = new GRBEnv(), NotAvailable);
  GRBEXECUTE_OR_DIE(p_model = new GRBModel(*p_env), NotAvailable);

  gurobi_varmap_t   var_map;
  gurobi_callback_t cb( lp, lprel, *p_out_cache, c, var_map );
  
  cb.m_timeout = c.timelimit;

  V(2) cerr << TS() << "Converting the problem into LP optimization problem..." << endl;
  
  /* Create variables. */
  GRBEXECUTE_OR_DIE(
  repeat( i, lp.variables.size() ) {
    if( InvalidFixedValue != lp.variables[i].fixed_val ) {
      var_map[i] = p_model->addVar( lp.variables[i].fixed_val, lp.variables[i].fixed_val,
                                 lp.variables[i].obj_val, lp.variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == lp.variables[i].ub - lp.variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    } else {
      var_map[i] = p_model->addVar( lp.variables[i].lb, lp.variables[i].ub,
                                 lp.variables[i].obj_val, lp.variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == lp.variables[i].ub - lp.variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    }
    
  },
  NotAvailable
                    );

  GRBEXECUTE_OR_DIE(p_model->update(), NotAvailable);

  /* Set MIP starts. */
  GRBEXECUTE_OR_DIE(
  repeat( i, lp.variables.size() ) {
  
    if( -9999.0 != lp.variables[i].init_val && !lp.variables[i].isFixed() )
      var_map[i].set(GRB_DoubleAttr_Start, lp.variables[i].init_val);
  },
  NotAvailable
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
      p_model->addSOS( &sosv[0], &con.coes[0], sosv.size(), SOS1 == con.opr ? GRB_SOS_TYPE1 : GRB_SOS_TYPE2 );
      break; }
    case Equal: {        p_model->addConstr( expr_lin, GRB_EQUAL, con.lhs, con.name.substr(0, con.name.length()) );         break; }
    case LessEqual: {    p_model->addConstr( expr_lin, GRB_LESS_EQUAL, con.rhs, con.name.substr(0, con.name.length()) );    break; }
    case GreaterEqual: { p_model->addConstr( expr_lin, GRB_GREATER_EQUAL, con.rhs, con.name.substr(0, con.name.length()) ); break; }
    case Range: {
      if(con.lhs == con.rhs)
        p_model->addConstr( expr_lin, GRB_EQUAL, con.lhs, con.name.substr(0, con.name.length()) );
      else
        p_model->addRange( expr_lin, con.lhs, con.rhs, con.name.substr(0, con.name.length()) );
      break; }
    default:             cerr << TS() << "SolveLP_BnB: Unknown constraint type." << endl;
    }, lp.constraints[i].toString( lp.variables )
                  );
  }
  
  /* State a maximization objective. */
  p_model->set( GRB_IntAttr_ModelSense, GRB_MAXIMIZE );
  
  /* Go to hell! */
  GRBEXECUTE(p_model->getEnv().set( GRB_IntParam_OutputFlag, c.isOutput(OutputInfoILPlog) ? 1 : 0 );
             p_model->getEnv().set( GRB_DoubleParam_TimeLimit, c.timelimit );
             p_model->getEnv().set( GRB_IntParam_Threads, c.nbthreads );
             //p_model->getEnv().set( GRB_IntParam_MIPFocus, 3 );
             );

  if( InvalidCutoff != lp.cutoff ) p_model->getEnv().set( GRB_DoubleParam_Cutoff, lp.cutoff );
  if( string::npos != c.output_info.find("GAP") && CuttingPlaneBnB == c.method ) { cb.m_gap_skip=true; GRBEXECUTE(p_model->getEnv().set( GRB_IntParam_DualReductions, 0 )); }
  //GRBEXECUTE(p_model->getEnv().set( GRB_IntParam_DualReductions, 0 ));
                                               
  GRBEXECUTE_OR_DIE(p_model->setCallback( &cb ), NotAvailable);
  
  if(c.isOutput(OutputInfoILPlog)) beginXMLtag( "ilp-log", "solver=\"gurobi\"" );

  double time_start     = getTimeofDaySec();
  bool   f_got_solution = false;
  
  g_p_model = p_model;
  
  if( LazyBnB == c.method ) {
    signal( SIGINT, _cb_stop_ilp );
    GRBEXECUTE_OR_DIE(p_model->optimize(), NotAvailable);
    signal( SIGINT, catch_int );

    if(0 != p_model->get(GRB_IntAttr_SolCount)) {
      lp_solution_t sol(lp);

      repeat( j, lp.variables.size() )
        sol.optimized_values[j] = var_map[j].get(GRB_DoubleAttr_X);

      sol.optimized_obj = p_model->get(GRB_DoubleAttr_ObjVal);
      sol.sol_type      = GRB_OPTIMAL == p_model->get(GRB_IntAttr_Status) ? Optimal : SubOptimal;
      f_got_solution    = true;

      p_out_sols->push_back(sol);
    }
  } else if( CuttingPlaneBnB == c.method ) {
    if( string::npos != c.output_info.find("GAP") ) {
      signal( SIGINT, _cb_stop_ilp );
      GRBEXECUTE_OR_DIE(p_model->optimize(), NotAvailable);
      signal( SIGINT, catch_int );
      
    } else {
    
      int n, num_constraints_added = 0;
      lp_solution_t sol(lp);
    
      for( n=0; !c.isTimeout(); n++ ) {

        V(1) cerr << TS() << "CPI: I=" << n << ": Started." << endl;

        GRBEXECUTE_OR_DIE(p_model->getEnv().set(GRB_DoubleParam_TimeLimit, c.timelimit - (getTimeofDaySec() - time_start)), NotAvailable);

        signal( SIGINT, _cb_stop_ilp );
        GRBEXECUTE_OR_DIE(p_model->optimize(), NotAvailable);
        signal( SIGINT, catch_int );

        if( GRB_CUTOFF == p_model->get(GRB_IntAttr_Status) )     { cerr << TS() << "CPI: I=" << n << ": Cutoff." << endl; break; }
        else if( GRB_INFEASIBLE == p_model->get(GRB_IntAttr_Status) ) { cerr << TS() << "CPI: I=" << n << ": Infeasible." << endl; f_got_solution = false; break; }
        
        /* Any constraints violated? */
        int                num_constraints_locally_added = 0, num_examined = 0;
        vector<GRBLinExpr> violated_constraints;
        vector<GRBVar>     penalizing_vars;

        /* GET THE VARIABLES. */
        GRBVar *p_vars      = NULL;
        double *p_vals_vars = NULL;
        int     num_sols    = 0;

        GRBEXECUTE_OR_DIE(num_sols = p_model->get(GRB_IntAttr_SolCount), NotAvailable);
        
        if(0 != num_sols) {
          p_vars      = p_model->getVars();
          p_vals_vars = p_model->get(GRB_DoubleAttr_X, p_vars, lp.variables.size());

          if(GRB_OPTIMAL == p_model->get(GRB_IntAttr_Status)) {
            repeat( j, lp.variables.size() )
              sol.optimized_values[j] = p_vals_vars[j];

            sol.sol_type      = SubOptimal;
            sol.optimized_obj = p_model->get(GRB_DoubleAttr_ObjVal);
          }
          
          f_got_solution = true;
        }
        
        if(GRB_TIME_LIMIT == p_model->get(GRB_IntAttr_Status)) { V(1) cerr << TS() << "CPI: I=" << n << ": Timeout." << endl; break; }
        else if(GRB_OPTIMAL != p_model->get(GRB_IntAttr_Status)) { V(1) cerr << TS() << "CPI: I=" << n << ": ?" << endl; f_got_solution = false; break; }

        V(1) cerr << TS() << "CPI: I=" << n << ": " << "Checking violation..." << endl;
        
        for( variable_cluster_t::cluster_t::iterator iter_c2v=p_out_cache->pg.vc_unifiable.clusters.begin(); p_out_cache->pg.vc_unifiable.clusters.end()!=iter_c2v; ++iter_c2v ) {
          vector<store_item_t> variables( iter_c2v->second.begin(), iter_c2v->second.end() );

          V(6) cerr << TS() << "CPI: I=" << n << ": # of vars = " << variables.size() << endl;
          V(6) cerr << TS() << "CPI: I=" << n << ": " << store_item_t::toString(variables) << endl;
          
          for( uint_t i=0; i<variables.size(); i++ ) {
            for( uint_t j=i+1; j<variables.size(); j++ ) {
              if( c.isTimeout() ) goto BED;
              if(1000 < num_constraints_locally_added) break;
        
              store_item_t &t1 = variables[i], &t2 = variables[j];

              /* TRANSITIVE RELATIONS SHOULD HOLD WITH THE OTHER VARIABLES
                 IN THE SAME EQV CLUSTER. */
              for( uint_t k=j+1; k<variables.size(); k++ ) {
                store_item_t &t3 = variables[k];
                
                if(c.isTimeout()) goto BED;
                if(t3 == t1 || t3 == t2) continue;

                int
                  v_ij = p_out_cache->createNodeVar(p_out_cache->pg.getSubNode(t1, t2), false),
                  v_ik = p_out_cache->createNodeVar(p_out_cache->pg.getSubNode(t1, t3), false),
                  v_jk = p_out_cache->createNodeVar(p_out_cache->pg.getSubNode(t2, t3), false);
                if(-1 == v_ij || -1 == v_ik || -1 == v_jk) continue;

                num_examined++;
                double s_ij = p_vals_vars[v_ij], s_ik = p_vals_vars[v_ik], s_jk = p_vals_vars[v_jk];

                GRBEXECUTE_OR_DIE(
                  if( -s_ij - s_jk + s_ik < -1 ) { violated_constraints.push_back(-var_map[v_ij] - var_map[v_jk] + var_map[v_ik]); num_constraints_locally_added++; }
                  if( -s_ij + s_jk - s_ik < -1 ) { violated_constraints.push_back(-var_map[v_ij] + var_map[v_jk] - var_map[v_ik]); num_constraints_locally_added++; }
                  if(  s_ij - s_jk - s_ik < -1 ) { violated_constraints.push_back( var_map[v_ij] - var_map[v_jk] - var_map[v_ik]); num_constraints_locally_added++; },
                  NotAvailable);
              }
            
            } }

          V(6) cerr << TS() << "CPI: I=" << n << ": " << num_examined << "..." << endl;
        }

        if(NULL != p_vars )     { delete[] p_vars; p_vars = NULL; }
        if(NULL != p_vals_vars) { delete[] p_vals_vars; p_vals_vars = NULL; }
         
        /* VIOLATED CONSTRAINTS ARE PENALIZED. */
        repeat(i, violated_constraints.size()) {
          GRBEXECUTE_OR_DIE(p_model->addConstr(violated_constraints[i] >= -1), NotAvailable);
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

        //       if( -s_ij - s_jk + s_ik < -1 ) { p_model->addConstr( -var_map[v_ij] - var_map[v_jk] + var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //       if( -s_ij + s_jk - s_ik < -1 ) { p_model->addConstr( -var_map[v_ij] + var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //       if(  s_ij - s_jk - s_ik < -1 ) { p_model->addConstr(  var_map[v_ij] - var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
        //     }
        //   }


        num_constraints_added += num_constraints_locally_added;
      
        V(3) cerr << TS() << "CPI: I=" << n << ": " << num_examined << " explored." << endl;
        V(1) cerr << TS() << "CPI: I=" << n << ": Finished. Obj:"<< sol.optimized_obj <<": Violated:" << num_constraints_locally_added << " (Total: " << num_constraints_added << ")" << endl;

        if( 0 == num_constraints_locally_added ) {
          V(1) cerr << TS() << "CPI: I=" << n << ": No violation." << endl;
          
          sol.sol_type = Optimal;
          break;
        }
        
        //p_model->reset();
      
        continue;
      
      BED:
        break;
      
      }

      if(f_got_solution) {
        if(p_out_sols->size() > 0) {
          
          /* CHECK THE SCORE OF SOLUTION IS GREATER THAN THE CURRENT BEST. */
          if((*p_out_sols)[p_out_sols->size()-1].optimized_obj <= sol.optimized_obj)
            p_out_sols->push_back(sol);
          
        } else if(NotAvailable != sol.sol_type)
          p_out_sols->push_back(sol);
      }
        

      if( !c.isTimeout() ) {
        V(1) cerr << TS() << "CPI: Finished: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
      } else {
        V(1) cerr << TS() << "CPI: Finished: Timeout: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
      }
    }
    
  } else {
    repeat(k, c.k_best) {
      for(int lv=0;;lv++) {
        int n_prohibited = 0;
      
        // repeat(i, lp.variables.size()) {
        //   if(lp.variables[i].opt_level > lv) { var_map[i].set(GRB_DoubleAttr_UB, 0.0); n_prohibited++; }
        //   else                                      if(!lp.variables[i].isFixed()) var_map[i].set(GRB_DoubleAttr_UB, 1.0);
        // }
      
        signal( SIGINT, _cb_stop_ilp );
        GRBEXECUTE_OR_DIE(p_model->optimize(), NotAvailable);
        signal( SIGINT, catch_int );

        if(0 == n_prohibited) break;
            
        // p_model->reset();

        // repeat( j, lp.variables.size() )
        //   var_map[j].set(GRB_DoubleAttr_Start, var_map[j].get(GRB_DoubleAttr_X));
      }

      if(0 != p_model->get(GRB_IntAttr_SolCount)) {
        lp_solution_t sol(lp);
    
        repeat( j, lp.variables.size() )
          sol.optimized_values[j] = var_map[j].get(GRB_DoubleAttr_X);

        sol.optimized_obj = p_model->get(GRB_DoubleAttr_ObjVal);
        sol.sol_type      = GRB_OPTIMAL == p_model->get(GRB_IntAttr_Status) ? Optimal : SubOptimal;
        f_got_solution    = true;
    
        p_out_sols->push_back(sol);
        
        continue;
        
        /* Degrade the current solution. */
        GRBVar     penalizer = p_model->addVar(0, 1, -100.0, GRB_BINARY);
        GRBLinExpr exprSol;
        double     rhs = 0, num_neg = 0;

        repeat(j, lp.variables.size())
          if(string::npos != lp.variables[j].name.find("/EXPLAINED_BY")) {
            rhs += 1.0;
            
            if(1.0 == sol.optimized_values[j]) exprSol += 1.0 * var_map[j];
            else                               { exprSol += -1.0 * var_map[j]; num_neg += 1.0; }
          }

        exprSol += -1.0 * penalizer;

        GRBEXECUTE_OR_DIE(p_model->update(), NotAvailable);
        GRBEXECUTE_OR_DIE(p_model->addRange(exprSol, -num_neg, rhs-1.0-num_neg), NotAvailable);
      }
    }
  }
  
  if( NULL != p_out_cache ) p_out_cache->elapsed_ilp = getTimeofDaySec() - time_start;
  
  if(c.isOutput(OutputInfoILPlog)) endXMLtag( "ilp-log" );

  if( !f_got_solution && 0 == p_model->get(GRB_IntAttr_SolCount) ) {
    if( GRB_INFEASIBLE == p_model->get(GRB_IntAttr_Status) ) {
      GRBEXECUTE(
                 p_model->computeIIS();
                 GRBConstr *cnstrs = p_model->getConstrs();

                 repeat(i, (uint_t)p_model->get(GRB_IntAttr_NumConstrs)) {
                   if (cnstrs[i].get(GRB_IntAttr_IISConstr) == 1) {
                     cout << "Infeasible: " << cnstrs[i].get(GRB_StringAttr_ConstrName) << endl;
                   } }
                 
                 delete[] cnstrs; cnstrs = NULL;
                 );
    }

    delete p_model; p_model = NULL;
    delete p_env;   p_env = NULL;
    
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
  
  ilp_solution_type_t ret = c.isTimeout() ? SubOptimal :
    (((BnB == c.method || NoTransitivity == c.method) ?
      GRB_OPTIMAL == p_model->get(GRB_IntAttr_Status) :
     GRB_OPTIMAL == p_model->get(GRB_IntAttr_Status) || GRB_CUTOFF == p_model->get(GRB_IntAttr_Status)) ?
     Optimal : SubOptimal);
  
  delete p_model; p_model = NULL;
  delete p_env;   p_env = NULL;

  return ret;
}

#endif /* #ifdef GUROBI */

void algorithm::kbestMIRA(sparse_vector_t *p_out_new, sparse_vector_t *p_out_diff, unordered_set<store_item_t> *p_out_fi, const sparse_vector_t &fv_gold, const vector<pair<sparse_vector_t*, double> > &wrong_best, const learn_configuration_t &c, double normer_gold, double normer_wrong) {
  function::getVectorIndices(p_out_fi, fv_gold);

  repeat(i, wrong_best.size())
    function::getVectorIndices(p_out_fi, *wrong_best[i].first);

  /* IF K=1, THE CLOSED FORM SOLUTION IS AVAILABLE. */
  //if(1 == wrong_best.size()) {
  if(false) {
    const sparse_vector_t &fv_current = *wrong_best[0].first;
    double                 loss       = wrong_best[0].second;
    double                 s_current  = score_function_t::getScore(*p_out_new, fv_current),
                           s_gold     = score_function_t::getScore(*p_out_new, fv_gold);
    double                 numerator  = s_current - s_gold + loss, denominator = 0.0;

    foreach(unordered_set<store_item_t>, iter_fi, *p_out_fi) {
      denominator += pow(get_value(fv_gold, *iter_fi, 0.0) - get_value(fv_current, *iter_fi, 0.0), 2);
    }

    double tau, TauTolerance = c.E * 0.1;
    if(TauTolerance > fabs(numerator))   numerator = numerator >= 0 ? TauTolerance : -TauTolerance;

    if(0.0 == denominator) tau = 0.0;
    else                   tau = min( c.C, numerator / denominator );

    foreach(unordered_set<store_item_t>, iter_fi, *p_out_fi) {
      if(0 == iter_fi->toString().find(PrefixInvisibleElement) || 0 == iter_fi->toString().find(PrefixFixedWeight))
        continue;

      double diff = get_value(fv_gold, *iter_fi, 0.0) - get_value(fv_current, *iter_fi, 0.0);
      (*p_out_new)[*iter_fi] += tau * diff;
      (*p_out_diff)[*iter_fi] += tau * diff;
    }

    return;
  }

#ifdef USE_GUROBI
  GRBEnv   env;
  GRBModel model(env);

  GRBQuadExpr                  expr_obj;
  unordered_map<string,GRBVar> new_weights;
  GRBVar                       var_epsilon = model.addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS);

  function::getVectorIndices(p_out_fi, *p_out_new);

  /* Create the objective function. */
  foreach(unordered_set<store_item_t>, iter_fe, *p_out_fi) {
    if(0 == iter_fe->toString().find(PrefixInvisibleElement)) continue;
    if(0 == iter_fe->toString().find(PrefixFixedValue)) continue;

    new_weights[*iter_fe] = model.addVar(-GRB_INFINITY, GRB_INFINITY, 0.0, GRB_CONTINUOUS);
    expr_obj += new_weights[*iter_fe]*new_weights[*iter_fe];
    expr_obj += -2.0 * new_weights[*iter_fe] * get_value(*p_out_new, *iter_fe, 0.0);
  }

  expr_obj += c.C * var_epsilon;

  GRBEXECUTE(model.update());
  GRBEXECUTE(model.setObjective(expr_obj));

  /* IMPOSE MARGIN CONSTRAINT. */
  GRBEXECUTE(model.addConstr(var_epsilon >= 0));

  repeat(i, wrong_best.size()) {
    GRBLinExpr expr_lhs;

    foreach(unordered_set<store_item_t>, iter_fe, *p_out_fi) {
      if(0 == iter_fe->toString().find(PrefixInvisibleElement)) continue;
      if(0 == iter_fe->toString().find(PrefixFixedValue))
        expr_lhs += get_value(fv_gold, *iter_fe, 0.0) - get_value(*wrong_best[i].first, *iter_fe, 0.0);
      else
        expr_lhs += new_weights[*iter_fe]*get_value(fv_gold, *iter_fe, 0.0) - new_weights[*iter_fe]*get_value(*wrong_best[i].first, *iter_fe, 0.0);
    }

    GRBEXECUTE(model.addConstr(expr_lhs + var_epsilon >= wrong_best[i].second));
  }

  /* FIX THE WEIGHT THAT HAS "!" AS THE BEGINNING OF THE NAME.*/
  foreach(unordered_set<store_item_t>, iter_fe, *p_out_fi) {
    if(0 == iter_fe->toString().find(PrefixInvisibleElement)) continue;
    if(0 == iter_fe->toString().find(PrefixFixedValue)) continue;
    if(0 == iter_fe->toString().find(PrefixFixedWeight))
      GRBEXECUTE(model.addConstr(new_weights[*iter_fe] == (double)(*p_out_new)[*iter_fe]));

    // if(string::npos != iter_fe->toString().find("EXPLAINED"))
    //   GRBEXECUTE(model.addConstr(new_weights[*iter_fe] >= 0.0));

    // if(string::npos != iter_fe->toString().find("AXIOM"))
    //   GRBEXECUTE(model.addConstr(new_weights[*iter_fe] <= 0.0));
  }

  GRBEXECUTE(model.set( GRB_IntAttr_ModelSense, GRB_MINIMIZE));
  GRBEXECUTE(model.optimize());

  foreach(unordered_set<store_item_t>, iter_fe, *p_out_fi) {
    if(0 == iter_fe->toString().find(PrefixInvisibleElement)) continue;
    if(0 == iter_fe->toString().find(PrefixFixedValue)) continue;
    if(0 == new_weights.count(*iter_fe)) continue;

    double new_weight = 0.0;
    GRBEXECUTE(new_weight = new_weights[*iter_fe].get(GRB_DoubleAttr_X));
    (*p_out_diff)[*iter_fe] = new_weight - (*p_out_new)[*iter_fe];
    (*p_out_new)[*iter_fe]  = new_weight;
  }
#endif

}

int lp_inference_cache_t::createNodeVar(int n, bool f_brand_new) {
  if(-1 == n) return -1;

  int& v_h = lprel.n2v[n];

  if( 0 != v_h ) return v_h;
  if(!f_brand_new) return -1;

  v_h = lp.addVariable(lp_variable_t( "h_" + pg.nodes[n].toString() ));

  lp_constraint_t con_mrhs("mrhs", GreaterEqual, 0);

  if(ObservableNode == pg.nodes[n].type || LabelNode == pg.nodes[n].type) {
    if(LabelNode == pg.nodes[n].type) {
      V(5) cerr << TS() << " Fxied (label): " << pg.nodes[n].toString() << endl;
    }

    if(ObservableNode == pg.nodes[n].type)
      lp.variables[v_h].fixValue( 1.0 );
    else {
      lprel.feature_vector[v_h][PrefixInvisibleElement + string("REWARD4LABEL_") + pg.nodes[n].toString()] = 9999.0;
      V(1) cerr << TS() << "Rewarded: " << pg.nodes[n].toString() << endl;
    }
  } else if(2 <= pg.nodes[n].rhs.size()) {
    /* Multiple RHS? */
    foreachc(unordered_set<int>, r, pg.nodes[n].rhs)
      con_mrhs.push_back(createNodeVar(*r), 1.0);
  }

  repeat(i, pg.nodes[n].cond_neqs.size()) {
    con_mrhs.push_back(createNodeVar(pg.getSubNode(pg.nodes[n].cond_neqs[i].first, pg.nodes[n].cond_neqs[i].second)), -1.0);
    con_mrhs.rhs -= 1.0;
  }

  if(0 < ci.hypothesized_literals.count(n))// || 1574 == n || 1897 == n)
    lp.variables[v_h].fixValue( 1.0 );

//  if(15 == n || 13 == n)
//    lp.variables[v_h].fixValue( 1.0 );

  if(con_mrhs.vars.size() > 0) {
    con_mrhs.push_back(v_h, -1.0 * con_mrhs.vars.size());
    //p_out_lp->addConstraint(con_mrhs);
  }

  /* COST OF HYPOTHESIS. */
  if(pg.nodes[n].lit.predicate != "=" || (pg.nodes[n].lit.predicate == "=" && pg.nodes[n].lit.wa_number != 0.0)) {
    string str_feature_hypothesized = (string)(LabelNode == pg.nodes[n].type ? PrefixInvisibleElement : "") +
        "BUILTIN_HYPOTHESIZED_" + pg.nodes[n].toString();
    lprel.feature_vector[v_h][str_feature_hypothesized] =
        LabelNode == pg.nodes[n].type ? 9999.0 : -pg.nodes[n].lit.wa_number-0.001;
  }

  /* CONSTANT IS CONSTANT MODE? */
  if(pg.nodes[n].lit.predicate == "=") {
    if(pg.nodes[n].lit.terms[0] != pg.nodes[n].lit.terms[1] &&
        pg.nodes[n].lit.terms[0].isConstant() && pg.nodes[n].lit.terms[1].isConstant()) {
      lp.variables[v_h].fixValue(0.0);
    }
  }

  /* FEATURE: EXPLAINED. */
  factor_t fc_explained(OrFactorTrigger);

  pg_edge_set_t::const_iterator iter_eg = pg.edges.find(n);
  if( pg.edges.end() != iter_eg ) {
    /* WE CAN RECEIVE THE REWARD IF AT LEAST ONE CONJUNCTION EXPLAINING THIS LITERAL IS HYPOTHESIZED. */
    repeat(j, iter_eg->second.size()) {
      //if(!pg.isHyperNodeForUnification(iter_eg->second[j])) continue;
      int v_cnj = createConjVar(iter_eg->second[j]);
      fc_explained.push_back(v_cnj, 1.0);
    }
  }

  //cerr << pg.nodes[n].toString() << ":" << pg.nodes[n].lit.wa_number << endl;

  if(LabelNode == pg.nodes[n].type || (!ci.use_only_user_score && !ci.no_explained)) {
    if(pg.nodes[n].lit.predicate != "mention'") {
      //cerr << pg.nodes[n].toString() << endl;

      string str_feature = (string)(LabelNode == pg.nodes[n].type ? PrefixInvisibleElement : "") +
        "BUILTIN_EXPLAINED_" + kb.getExplainedFeatureGroup(pg.nodes[n].lit.toPredicateArity());

      if(0 < pg.nodes[n].depth) str_feature += "_INFERRED_BY_" + pg.nodes[n].instantiated_by.axiom;

      if(pg.nodes[n].lit.predicate != "=") {
        int v_fc_explained = LabelNode == pg.nodes[n].type && pg.nodes[n].lit.predicate == "=" ? v_h : fc_explained.apply(&lp, "fc_" + str_feature, false, false, true);

        if(-1 != v_fc_explained) {
          lprel.n2ev[n] = v_fc_explained;
          lprel.feature_vector[v_fc_explained][str_feature] =
              LabelNode == pg.nodes[n].type ? 9999.0 : pg.nodes[n].lit.wa_number;
          //cerr << pg.nodes[n].lit.wa_number << endl;
          //lprel.feature_vector[v_fc_explained][str_feature] = LabelNode == pg.nodes[n].type ? 9999.0 : 1.0;

          /* THE LITERAL CAN BE REWARDED IF THE LITERAL IS HYPOTHESIZED. */
          lp_constraint_t con_imp("rew_hypo" + pg.nodes[n].toString(), LessEqual, 0);
          con_imp.push_back(v_fc_explained, 1);
          con_imp.push_back(v_h, -1);
          lp.addConstraint(con_imp);
        }
      }
    }
  }

  // lprel.feature_vector[v_h][store_item_t("PRIOR_" + pg.nodes[n].lit.toPredicateArity())] =
  //   1.0 / mymax(1, (double)(pg.nodes.size()*pg.nodes.size()));
  // if(pg.nodes[n].lit.predicate == "=")
  //   lprel.feature_vector[v_h][store_item_t("UNIFY_PRIOR_EQ")] = 10.0 / mymax(1, (double)(pg.vc_unifiable.variables.size()*pg.vc_unifiable.variables.size()));
    //lprel.feature_vector[v_h][store_item_t("!UNIFY_PRIOR")] = 10.0 / mymax(1, (double)(pg.vc_unifiable.variables.size()*pg.vc_unifiable.variables.size()));

  if(pg.nodes[n].f_prohibited)
    lp.variables[v_h].fixValue(0.0);

  int partner = -1;

  if(pg.nodes[n].lit.predicate == "=" ) {
    if(-1 != (partner = pg.getNegSubNode(pg.nodes[n].lit.terms[0], pg.nodes[n].lit.terms[1]))) {
      lp_constraint_t con_mx(::toString("inc%d", n), LessEqual, 1.0);
      con_mx.push_back(v_h, 1.0);
      con_mx.push_back(createNodeVar(partner), 1.0);
      lp.addConstraint(con_mx);
    }
  } else if(pg.nodes[n].lit.predicate == "!=" ) {
    if(-1 != (partner = pg.getSubNode(pg.nodes[n].lit.terms[0], pg.nodes[n].lit.terms[1]))) {
      lp_constraint_t con_mx(::toString("inc%d", n), LessEqual, 1.0);
      con_mx.push_back(v_h, 1.0);
      con_mx.push_back(createNodeVar(partner), 1.0);
      lp.addConstraint(con_mx);
    }
  }

  return v_h;
}

/* and_{1,2,3} <=> h_i ^ h_c1 ^ h_c2 ^ ... ^ h_c3. */
int lp_inference_cache_t::createConjVar(int hn) {
  int& v_hn = lprel.hn2v[hn];

  if( 0 != v_hn )
    return v_hn;

  char buffer[1024]; sprintf( buffer, "and_%d", hn );
  v_hn = lp.addVariable( lp_variable_t( string( buffer ) ) );

  /* and_{1,2,3} <=> h_i ^ h_c1 ^ h_c2 ^ ... ^ h_c3. */
  lp_constraint_t con(::toString("and_%d", hn), Range, 0, 1 );
  repeat( j, pg.hypernodes[hn].size() )
    con.push_back(createNodeVar(pg.hypernodes[hn][j]), 1.0 );
  con.rhs = 1.0 * con.vars.size() - 1;
  con.push_back(v_hn, -1.0 * con.vars.size());
  lp.addConstraint(con);

  /* THIS NODE NEEDS TO PAY IF THIS CONJUNCTION IS TRUE. */
  if(0 < pg.edges_name.count(hn)) {
    const string &edge_name = pg.edges_name.find(hn)->second;
    if("0" != edge_name && !ci.use_only_user_score) {
      string str_cute_name = "BUILTIN_AXIOM_" + ("?" == edge_name ?
                                           ::toString("%s", pg.edges_axiom.find(hn)->second.c_str()) :
                                           edge_name);

      // factor_t fc_axiom(AndFactorTrigger);
      // fc_axiom.push_back(v_hn);

      // int v_axiom = fc_axiom.apply(&lp, "fc_" + str_cute_name);
      // if(-1 != v_axiom)
      //lprel.feature_vector[v_hn][str_cute_name] = pg.nodes[pg.hypernodes[hn][0]].lit.wa_number;



      //lprel.feature_vector[v_hn][str_cute_name] = 1 * pg.hypernodes[hn].size() * pg.edges_rhs[hn];

      repeat(k, pg.hypernodes[hn].size()) {
        // string str_cute_name = "BUILTIN_" + ("?" == edge_name ?
        //                                      ::toString("AXIOM_%d_AT_%s", k, pg.edges_axiom.find(hn)->second.c_str()) :
        //                                      edge_name);
        // factor_t fc_axiom(AndFactorTrigger);
        // fc_axiom.push_back(v_hn);

        // int v_axiom = fc_axiom.apply(&lp, str_cute_name);
        // lprel.feature_vector[v_axiom][str_cute_name] = pg.nodes[pg.hypernodes[hn][k]].lit.wa_number;

        /* GIVE SOME SCORE FOR EXPLAINING MULTIPLE THINGS TOGETHER. */
        // if(pg.nodes[pg.hypernodes[hn][k]].lit.predicate == "=" || pg.nodes[pg.hypernodes[hn][k]].lit.predicate == "!=")
        //   continue;

        // string str_cute_name = "BUILTIN_INFORMATIVE_" + pg.nodes[pg.hypernodes[hn][k]].lit.toPredicateArity();

        // int v_info = fc_axiom.apply(&lp, str_cute_name);
        // lprel.feature_vector[v_info][str_cute_name] += 1;
      }
    }
  }

  return v_hn;
}

int lp_inference_cache_t::createConsistencyConstraint(int _n1, int _n2, const unifier_t &theta) {
  if(_n1 > _n2) swap(_n1, _n2);

//  static hash<string> hashier;
//  size_t id = hashier(::toString("%d:%d:%s", _n1, _n2, theta.toString().c_str()));
//
//  if(0 < mx_produced.count(id)) return -1;
//  mx_produced.insert(id);

  pg_node_t &n1 = pg.nodes[_n1], &n2 = pg.nodes[_n2];

  lp_constraint_t con_m(::toString("inc%d-%d", n1.n, n2.n), LessEqual, 1);
  con_m.push_back(createNodeVar(n1.n), 1.0);
  con_m.push_back(createNodeVar(n2.n), 1.0);

  bool             f_fails = false;

  repeat(j, theta.substitutions.size()) {
    if(theta.substitutions[j].terms[0] == theta.substitutions[j].terms[1]) continue;
    if(theta.substitutions[j].terms[0].isConstant() && theta.substitutions[j].terms[1].isConstant() &&
       theta.substitutions[j].terms[0] != theta.substitutions[j].terms[1]) { f_fails = true; break; }

    int v_coref = createNodeVar(pg.getSubNode(theta.substitutions[j].terms[0], theta.substitutions[j].terms[1]));
    if(-1 == v_coref) { f_fails=true; break; }

    con_m.push_back(v_coref, 1.0);
    con_m.rhs += 1.0;
  }

  if(f_fails) return -1;

  return lp.addConstraint(con_m);
}

int lp_inference_cache_t::createTransitivityConstraint(const store_item_t &ti, const store_item_t &tj, const store_item_t &tk) {
  int
    v_titj = createNodeVar(pg.getSubNode(ti, tj)),
    v_tjtk = createNodeVar(pg.getSubNode(tj, tk)),
    v_titk = createNodeVar(pg.getSubNode(ti, tk));

  if( -1 == v_titj || -1 == v_tjtk || -1 == v_titk ) return -1;

  vector<size_t> items; items.push_back(ti.getHash()); items.push_back(tj.getHash()); items.push_back(tk.getHash());
  sort(items.begin(), items.end());

  // static hash<string> hashier;
  // size_t id = hashier(::join(items.begin(), items.end(), "%d", ":"));

  // if(0 < tc_produced.count(id)) return -1;
  // tc_produced.insert(id);

  // cerr << ti << tj << tk << endl;
  
  lp_constraint_t con_trans1(::toString("trans%d", lp.constraints.size()), GreaterEqual, -1 );
  con_trans1.push_back( v_titk, 1.0 );
  con_trans1.push_back( v_titj, -1.0 );
  con_trans1.push_back( v_tjtk, -1.0 );
  lp.addConstraint( con_trans1 );

  lp_constraint_t con_trans2(::toString("trans%d", lp.constraints.size()), GreaterEqual, -1 );
  con_trans2.push_back( v_titk, -1.0 );
  con_trans2.push_back( v_titj, 1.0 );
  con_trans2.push_back( v_tjtk, -1.0 );
  lp.addConstraint( con_trans2 );

  lp_constraint_t con_trans3(::toString("trans%d", lp.constraints.size()), GreaterEqual, -1 );
  con_trans3.push_back( v_titk, -1.0 );
  con_trans3.push_back( v_titj, -1.0 );
  con_trans3.push_back( v_tjtk, 1.0 );
  lp.addConstraint( con_trans3 );

  return 1;
}

void lp_inference_cache_t::fixGoldClustering() {
  unordered_set<store_item_t> variables;
  variable_cluster_t          vc_gold;

  /* FIRST WE IDENTIFY THE CLUSTER IN THE CASE THAT USER MAY SPECIFY CONFLICTED CLUSTER. */
  repeat(i, pg.labelnodes.size()) {
    int  n    = pg.labelnodes[i];
    bool f_eq = pg.nodes[n].lit.predicate == "=",
      f_ineq  = pg.nodes[n].lit.predicate == "!=";

    if(f_eq || f_ineq) {
      repeat( j, pg.nodes[n].lit.terms.size() ) {
        repeatf( k, j+1, pg.nodes[n].lit.terms.size() ) {
          variables.insert(pg.nodes[n].lit.terms[j]);
          variables.insert(pg.nodes[n].lit.terms[k]);

          if(f_eq) {
            int n_node = pg.getSubNode(pg.nodes[i].lit.terms[j], pg.nodes[i].lit.terms[k]);
            if(-1 == n_node) {
              cerr << TS() << "Not in search space:" << pg.nodes[i].lit.terms[j] << "," << pg.nodes[i].lit.terms[k] << endl;
              continue;
            }

            int partner = pg.getNegSubNode(pg.nodes[i].lit.terms[j], pg.nodes[i].lit.terms[k]);

            if(-1 != partner) {
              if(ObservableNode == pg.nodes[partner].type || LabelNode == pg.nodes[partner].type) {
                W("Inconsistent: " << pg.nodes[i].toString());
                continue;
              }
            }

            lp.variables[createNodeVar(n_node)].fixValue(1);
          }

          if(f_eq) vc_gold.add(pg.nodes[n].lit.terms[j], pg.nodes[n].lit.terms[k]);
        } }
    }
  }

  repeat(i, pg.nodes.size()) {
    if(pg.nodes[i].lit.predicate != "=") continue;

    if(!vc_gold.isInSameCluster(pg.nodes[i].lit.terms[0], pg.nodes[i].lit.terms[1])) {
      int v_coref = createNodeVar(pg.getSubNode(pg.nodes[i].lit.terms[0], pg.nodes[i].lit.terms[1]));
      if(-1 == v_coref) continue;

      int partner = pg.getSubNode(pg.nodes[i].lit.terms[0], pg.nodes[i].lit.terms[1]);

      if(-1 != partner) {
        if(ObservableNode == pg.nodes[partner].type || LabelNode == pg.nodes[partner].type) {
          W("Inconsistent: " << pg.nodes[i].toString());
          continue;
        }
      }

      lp.variables[v_coref].fixValue(0);
    }
  }

  // vector<store_item_t> ordered_variables(variables.begin(), variables.end());

  // repeat(i, ordered_variables.size()) {
  //   repeatf(j, i+1, ordered_variables.size()) {
  //     bool f_eq = vc_gold.isInSameCluster(ordered_variables[i], ordered_variables[j]);

  //     int v_coref = createNodeVar(f_eq ? pg.getSubNode(ordered_variables[i], ordered_variables[j]) : pg.getNegSubNode(ordered_variables[i], ordered_variables[j]));

  //     /* Shouldn't make the variable, because it means that the
  //        solution is not in the search space.  */
  //     if( -1 == v_coref ) {
  //       cerr << TS() << "Not in the candidate hypothesis space: " << ordered_variables[i] << (f_eq ? "=" : "!=") << ordered_variables[j] << endl;
  //       continue;
  //     }

  //     V(5) cerr << TS() << "Fix: " << ordered_variables[i] << (f_eq ? "=" : "!=") << ordered_variables[j] << endl;
  //     lp.variables[v_coref].fixValue(1);
  //   } }

}

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
    if(!lp.variables[i].isFixed()) {
      LSExpression *p_var = p_model->createExpression(O_Bool);
      var_map[i] = p_var;

      if( 0 != lp.variables[i].obj_val )
    	  p_cost->addOperand( p_model->createExpression(O_Prod, lp.variables[i].obj_val, p_var));

    } else {
      LSExpression *p_var = p_model->createConstant(lp.variables[i].fixed_val);
      var_map[i] = p_var;

      if( 0 != lp.variables[i].obj_val )
        p_cost->addOperand(p_model->createExpression(O_Prod, lp.variables[i].obj_val, p_var));

    }
  }

  if(0 == p_cost->getNbOperands())
    p_cost->addOperand(p_model->createConstant( 0.0 ));

  /* Convert constraints. */
  repeat(i, lp.constraints.size()) {
    if(!lp.constraints[i].is_active) continue;

    LSExpression *p_sum = p_model->createExpression(O_Sum);

    repeat(j, lp.constraints[i].vars.size())
      p_sum->addOperand(p_model->createExpression(O_Prod, lp.constraints[i].coes[j], var_map[lp.constraints[i].vars[j]]));

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
  LSSolution *p_lssol = ls.getSolution();

  lp_solution_t sol(lp);
  sol.sol_type      =
  		SS_Optimal  == p_lssol->getStatus() ? Optimal : (
  		SS_Feasible == p_lssol->getStatus() ? SubOptimal : NotAvailable);
  sol.optimized_obj = 0.0;
  
  repeat( i, lp.variables.size() ) {

    sol.optimized_values[i]  = lp.variables[i].isFixed() ? lp.variables[i].fixed_val : var_map[i]->getValue();
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
            
    //         if( -s_ij - s_jk + s_ik < -1 ) { p_model->addConstr( -var_map[v_titj] - var_map[v_tjtk] + var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
    //         if( -s_ij + s_jk - s_ik < -1 ) { p_model->addConstr( -var_map[v_titj] + var_map[v_tjtk] - var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
    //         if(  s_ij - s_jk - s_ik < -1 ) { p_model->addConstr(  var_map[v_titj] - var_map[v_tjtk] - var_map[v_titk] >= -1 ); num_constraints_locally_added++; }
            
    //       } } }
    // }
    
