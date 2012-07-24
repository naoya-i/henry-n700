
#include "defs.h"
#include "signal.h"
#include "math.h"

#ifdef USE_GUROBI
#include "gurobi_c++.h"

#define GRBEXECUTE(x) \
  try{ x; } \
  catch( GRBException e ) { cerr << __FILE__ << ":" << __LINE__ << ": " << e.getErrorCode() << ": " << e.getMessage() << endl; }

#define GRBEXECUTEMSG(x, y)                          \
  try{ x; } \
  catch( GRBException e ) { cerr << __FILE__ << ":" << __LINE__ << ": " << e.getErrorCode() << ": " << e.getMessage() << ": " << y << endl; }

typedef unordered_map<int, GRBVar> gurobi_varmap_t;

GRBModel *g_p_model = NULL;

inline void _cb_stop_ilp( int sig_num ) {

  signal( SIGINT, _cb_stop_ilp );
  g_p_model->terminate();
  
}

class gurobi_callback_t : public GRBCallback {
  linear_programming_problem_t &m_lp;
  lp_problem_mapping_t         &m_lprel;
  lp_inference_cache_t         &m_cache;
  gurobi_varmap_t              &m_varmap;

  const inference_configuration_t    &m_conf;
  
public:
  int                   num_activated, num_evaluated;
  double                m_timeout, m_last_best;
  bool                  m_last_checked, m_exact_try;
  vector<GRBTempConstr> m_added_constr;
  
  inline gurobi_callback_t( linear_programming_problem_t& _lp, lp_problem_mapping_t &_lprel, lp_inference_cache_t &_cache, const inference_configuration_t &_conf, gurobi_varmap_t& _varmap ) :
    m_lp( _lp ), m_lprel( _lprel ), m_cache( _cache ), m_varmap( _varmap ), m_conf( _conf ), num_activated(0), num_evaluated(0), m_timeout(0), m_last_best(0.0), m_last_checked(false), m_exact_try(false)
  {};

  inline int _getCorefVar( store_item_t t1, store_item_t t2 ) {
    store_item_t t1s = t1, t2s = t2; if( t1s > t2s ) swap( t1s, t2s );
    
    pairwise_vars_t::iterator k1 = m_lprel.pp2v.find(t1s);
    if( m_lprel.pp2v.end() == k1 ) return -1;

    unordered_map<store_item_t, int>::iterator k2 = k1->second.find(t2s);
    return k1->second.end() == k2 ? -1 : k2->second;
  }
  
  inline void callback() {
    switch( where ) {
    case GRB_CB_MIPSOL: {
      double f_gap = (getDoubleInfo( GRB_CB_MIPSOL_OBJBND ) - getDoubleInfo( GRB_CB_MIPSOL_OBJ )) / getDoubleInfo( GRB_CB_MIPSOL_OBJ );
      
      num_evaluated++;
      V(1) cerr << "CPI: " << "I=" << num_evaluated << ": New solution! (Obj = "<< getDoubleInfo( GRB_CB_MIPSOL_OBJ ) <<"Gap = "<< f_gap <<")" << endl;

      if( !m_exact_try ) {
        if( fabs(f_gap) >= 0.1 ) { m_last_checked = false; break; }
      }

      m_last_checked   = true;

      repeat( i, m_lp.constraints.size() ) {
        if( !m_lp.constraints[i].is_lazy ) continue;

        double           val = 0.0;
        lp_constraint_t &con = m_lp.constraints[i];
        
        repeat( j, m_lp.constraints[i].vars.size() )
          val += con.coes[j] * getSolution( m_varmap[ con.vars[j] ] );

        if( !con.isSatisfied(val) ) {
          GRBLinExpr expr_lin;

          repeat( j, con.vars.size() )
            expr_lin  += con.coes[j] * m_varmap[ con.vars[j] ];
          
          if( LessEqual == con.opr )         addLazy( expr_lin <= con.rhs );
          else if( GreaterEqual == con.opr ) addLazy( con.lhs <= expr_lin );
          else if( Equal == con.opr )        addLazy( expr_lin == con.rhs );
          else if( Range == con.opr ) {      addLazy( con.lhs <= expr_lin ); addLazy( expr_lin <= con.rhs ); }

          m_lp.constraints[i].is_lazy = false;
        }        
      }
      
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
      
      /* Remember, you are not wrong. It succeeded when you generate
         all the transitivity constraints in advance and iteratively
         activated them. */
      foreach( variable_cluster_t::cluster_t, iter_vc, vc.clusters ) {
        vector<store_item_t> variables( iter_vc->second.begin(), iter_vc->second.end() );

        /* Identify inactive unification (i,j) in this cluster. */
        repeat( i, variables.size() ) {
          repeatf( j, i+1, variables.size() ) {
            store_item_t ti     = variables[i], tj = variables[j]; if( ti > tj ) swap( ti, tj );
            int          v_titj = _getCorefVar(ti, tj);

            if( -1 == v_titj ) continue;
            if( m_conf.isTimeout() ) return;

            GRBVar &gv_titj = m_varmap[ v_titj ];
                                 
            /* Transitivity constraint is violated. */
              
            repeat( k, variables.size() ) {
              if( i == k || j == k ) continue;
              if( m_conf.isTimeout() ) return;
                
              /* Create transitivity constraint for (i, j, k). It
                 guarantees ik ^ jk => ij. */
              store_item_t tk     = variables[k];
              int          v_titk = _getCorefVar(ti, tk), v_tjtk = _getCorefVar(tj, tk);
              if( -1 == v_titk || -1 == v_tjtk ) continue;
              if( 0.5 < sol_cache[ v_titk ] && 0.5 < sol_cache[ v_tjtk ] ) continue;
              if( 0.5 > sol_cache[ v_titk ] && 0.5 > sol_cache[ v_tjtk ] ) continue;

              GRBVar     gvars[] = { gv_titj, m_varmap[ v_titk ], m_varmap[ v_tjtk ] };
              double     ctc1[]  = {1.0, -1.0, -1.0}, ctc2[] = {-1.0, 1.0, -1.0}, ctc3[] = {-1.0, -1.0, 1.0};
              GRBLinExpr c1, c2, c3;
              c1.addTerms( ctc1, gvars, 3 ); //c2.addTerms( ctc2, gvars, 3 ); c3.addTerms( ctc3, gvars, 3 );
              GRBEXECUTE( addLazy(c1, GRB_GREATER_EQUAL, -1); ); //addLazy(c2, GRB_GREATER_EQUAL, -1); addLazy(c3, GRB_GREATER_EQUAL, -1); );
                
              num_activated++;
            }

          } }
      }
      
      V(1) cerr << "CPI: " << "I=" << num_evaluated << ": Activated constraints: " << num_activated << endl;
      break; }
    }
  }
    
};

ilp_solution_type_t function::solveLP_BnB( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache ) {

  GRBEnv            env;
  GRBModel          model( env );

  gurobi_varmap_t   var_map;
  gurobi_callback_t cb( *p_out_lp, *p_out_lprel, *p_out_cache, c, var_map );
  
  cb.m_timeout = c.timelimit;

  V(2) cerr << "Converting the problem into LP optimization problem..." << endl;
  
  /* Create variables. */
  GRBEXECUTE(
  repeat( i, p_out_lp->variables.size() ) {
    //p_out_lp->variables[i].f_continuous = true;
    if( InvalidFixedValue != p_out_lp->variables[i].fixed_val ) {
      var_map[i] = model.addVar( p_out_lp->variables[i].fixed_val, p_out_lp->variables[i].fixed_val,
                                 p_out_lp->variables[i].obj_val, p_out_lp->variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == p_out_lp->variables[i].ub - p_out_lp->variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    } else {
      var_map[i] = model.addVar( p_out_lp->variables[i].lb, p_out_lp->variables[i].ub,
                                 p_out_lp->variables[i].obj_val, p_out_lp->variables[i].f_continuous ? GRB_CONTINUOUS : (1.0 == p_out_lp->variables[i].ub - p_out_lp->variables[i].lb ? GRB_BINARY : GRB_INTEGER ) );
    }
    
  }
             );

  GRBEXECUTE( model.update() );

  /* Set MIP starts. */
  GRBEXECUTE(
  repeat( i, p_out_lp->variables.size() ) {
  
    if( -9999.0 != p_out_lp->variables[i].init_val && !p_out_lp->variables[i].isFixed() )
      var_map[i].set( GRB_DoubleAttr_Start, p_out_lp->variables[i].init_val );
  }
  );
  
  /* Create constraints. */
  repeat( i, p_out_lp->constraints.size() ) {
    if( !p_out_lp->constraints[i].is_active || p_out_lp->constraints[i].is_lazy ) continue;

    lp_constraint_t &con = p_out_lp->constraints[i];
    GRBLinExpr expr_lin;

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
    case Equal: {        model.addConstr( expr_lin, GRB_EQUAL, con.lhs, con.name );         break; }
    case LessEqual: {    model.addConstr( expr_lin, GRB_LESS_EQUAL, con.rhs, con.name );    break; }
    case GreaterEqual: { model.addConstr( expr_lin, GRB_GREATER_EQUAL, con.rhs, con.name ); break; }
    case Range: {        model.addRange( expr_lin, con.lhs, con.rhs, con.name );            break; }
    default:             cerr << "SolveLP_BnB: Unknown constraint type." << endl;
    }, p_out_lp->constraints[i].toString( p_out_lp->variables )
                  );
  }

  V(2) cerr << "... done." << endl;
 
  /* State a maximization objective. */
  model.set( GRB_IntAttr_ModelSense, GRB_MAXIMIZE );
  
  /* Go to hell! */
  GRBEXECUTE(model.getEnv().set( GRB_IntParam_OutputFlag, c.is_ilp_verbose ? 1 : 0 );
             model.getEnv().set( GRB_DoubleParam_TimeLimit, c.timelimit );
             model.getEnv().set( GRB_IntParam_Threads, c.nbthreads );
             //model.getEnv().set( GRB_IntParam_MIPFocus, 2 );
             );
  
  if( InvalidCutoff != p_out_lp->cutoff ) model.getEnv().set( GRB_DoubleParam_Cutoff, p_out_lp->cutoff );

  if( CuttingPlaneBnB == c.method ) {
    GRBEXECUTE(model.getEnv().set( GRB_IntParam_DualReductions, 0 );
               model.setCallback( &cb )
               );
  }
  
  if( c.is_ilp_verbose ) beginXMLtag( "ilp-log", "solver=\"gurobi\"" );

  double time_start = getTimeofDaySec();
  
  g_p_model = &model;
  
  if( CuttingPlaneBnB == c.method ) {

    signal( SIGINT, _cb_stop_ilp );
    GRBEXECUTE( model.optimize() );
      
    if( !cb.m_last_checked && 0 < model.get( GRB_IntAttr_SolCount ) && GRB_TIME_LIMIT != model.get( GRB_IntAttr_Status ) ) {
      repeat( i, cb.m_added_constr.size() )
        model.addConstr( cb.m_added_constr[i] );

      cb.m_exact_try = true;
      model.reset();

      if( c.timelimit - (getTimeofDaySec()-time_start) > 0 ) {
        model.getEnv().set( GRB_DoubleParam_TimeLimit, c.timelimit - (getTimeofDaySec()-time_start) );
        GRBEXECUTE( model.optimize() );
      }
    }
    signal( SIGINT, catch_int );
    
  } else {
    signal( SIGINT, _cb_stop_ilp );
    GRBEXECUTE( model.optimize() );
    signal( SIGINT, catch_int );
  }

  // model.computeIIS();
  // GRBConstr *cnstrs = model.getConstrs();

  // for (int i = 0; i < model.get(GRB_IntAttr_NumConstrs); ++i) {
  //   if (cnstrs[i].get(GRB_IntAttr_IISConstr) == 1) {
  //     cout << cnstrs[i].get(GRB_StringAttr_ConstrName) << endl;
  //   } }

  // delete[] cnstrs;                                                           
  
  if( NULL != p_out_cache ) p_out_cache->elapsed_ilp = getTimeofDaySec() - time_start;
  
  if( c.is_ilp_verbose ) endXMLtag( "ilp-log" );

  if( 0 == model.get( GRB_IntAttr_SolCount ) ) {
    p_out_lp->optimized_obj = 0.0;
    
    repeat( i, p_out_lp->variables.size() ) {
      if( p_out_lp->variables[i].isFixed() ) p_out_lp->variables[i].optimized                = p_out_lp->variables[i].fixed_val;
      else if( -9999.0 != p_out_lp->variables[i].init_val ) p_out_lp->variables[i].optimized = p_out_lp->variables[i].init_val;
      else p_out_lp->variables[i].optimized                                                  = p_out_lp->variables[i].lb;
          
      p_out_lp->optimized_obj += p_out_lp->variables[i].obj_val * p_out_lp->variables[i].optimized;
    }

    return NotAvailable;
  }

  if( CuttingPlaneBnB == c.method ) {
    V(1) cerr << "CPI: Finished: " << "I=" << cb.num_evaluated << endl
              << "CPI: Finished: Activated constraints: " << cb.num_activated << endl;
  }
  
  /* Update the optimized value based on the solution of LP. */
  repeat( i, p_out_lp->variables.size() )
    p_out_lp->variables[i].optimized = var_map[i].get(GRB_DoubleAttr_X);
    
  p_out_lp->optimized_obj = model.get(GRB_DoubleAttr_ObjVal);

  return GRB_OPTIMAL == model.get(GRB_IntAttr_Status) ? Optimal : SubOptimal;
  
}

#endif /* #ifdef GUROBI */



#ifdef USE_LOCALSOLVER
#include "localsolver.h"

using namespace localsolver;

ilp_solution_type_t function::solveLP_LS( linear_programming_problem_t *p_out_lp, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache ) {
  
  LocalSolver ls;
  LSModel *p_model = ls.getModel();

  LSExpression *p_cost = p_model->createExpression( O_Sum );

  /* Convert variables. */
  unordered_map<int, vector<LSExpression*> > var_map;
  
  repeat( i, p_out_lp->variables.size() ) {

    if( p_out_lp->variables[i].isFixed() ) {
      
      LSExpression *p_var = p_model->createConstant( p_out_lp->variables[i].fixed_val );
      var_map[i].push_back( p_var );
      
      if( 0 != p_out_lp->variables[i].obj_val ) p_cost->addOperand( p_model->createExpression( O_Prod, p_out_lp->variables[i].obj_val, p_var ) );
      
    } else {

      repeat( j, max( 1, int( ceil( log2( p_out_lp->variables[i].ub - p_out_lp->variables[i].lb ) ) ) ) ) {
        LSExpression *p_var = p_model->createExpression( O_Bool );
        var_map[i].push_back( p_var );

        if( 0 != p_out_lp->variables[i].obj_val ) p_cost->addOperand( p_model->createExpression( O_Prod, pow(2, j) * 1000 * p_out_lp->variables[i].obj_val, p_var ) );
      }

      if( p_out_lp->variables[i].ub - p_out_lp->variables[i].lb > 1.0 ) {
        cerr << p_out_lp->variables[i].ub - p_out_lp->variables[i].lb << endl;
        lp_constraint_t con_minmax( "", Range, p_out_lp->variables[i].lb, p_out_lp->variables[i].ub );
        con_minmax.push_back( i, 1.0 );
        p_out_lp->addConstraint( con_minmax );
      }
      
    }
    
  }

  if( 0 == p_cost->getNbOperands() )
    p_cost->addOperand( p_model->createConstant( 0.0 ) );

  /* Convert constraints. */
  repeat( i, p_out_lp->constraints.size() ) {
    if( !p_out_lp->constraints[i].is_active ) continue;
    
    LSExpression *p_sum = p_model->createExpression( O_Sum );

    repeat( j, p_out_lp->constraints[i].vars.size() ) {
      repeat( k, var_map[ p_out_lp->constraints[i].vars[j] ].size() )
        p_sum->addOperand( p_model->createExpression( O_Prod, pow(2, k) * p_out_lp->constraints[i].coes[j], var_map[ p_out_lp->constraints[i].vars[j] ][k] ) );
    }
    
    switch( p_out_lp->constraints[i].opr ) {
    case Equal: {      
      p_model->addConstraint( p_model->createExpression( O_Eq, p_sum, p_out_lp->constraints[i].lhs ) );
      break; }
      
    case LessEqual: {
      p_model->addConstraint( p_model->createExpression( O_Leq, p_sum, p_out_lp->constraints[i].rhs ) );
      break; }

    case GreaterEqual: {
      p_model->addConstraint( p_model->createExpression( O_Geq, p_sum, p_out_lp->constraints[i].lhs ) );
      break; }

    case Range: {
      p_model->addConstraint( p_model->createExpression( O_Leq, p_sum, p_out_lp->constraints[i].rhs ) );
      p_model->addConstraint( p_model->createExpression( O_Geq, p_sum, p_out_lp->constraints[i].lhs ) );
      break; }
      
    }
  }

  /* State a maximization objective. */
  p_model->addObjective( p_cost, OD_Minimize );

  /* Go to hell! */
  try {
    p_model->close();
  } catch( LSException* p_e ) {
    cerr << p_e->getMessage() << endl;
  }
  
  LSPhase *p_phase = ls.createPhase();
  p_phase->setTimeLimit( c.timelimit );
  
  ls.getParam()->setNbThreads( c.nbthreads );
  ls.getParam()->setVerbosity( 1 );
  ls.solve();

  /* Update the optimized value based on the solution of LP. */
  p_out_lp->optimized_obj = 0.0;
  
  repeat( i, p_out_lp->variables.size() ) {
    p_out_lp->variables[i].optimized = 0.0;
    
    repeat( j, var_map[i].size() ) {
      if( var_map[i].size() > 1 ) cerr << var_map[i][j]->getValue() << endl;
      p_out_lp->variables[i].optimized += pow( 2, j ) * var_map[i][j]->getValue();
    }
    
    p_out_lp->optimized_obj += p_out_lp->variables[i].optimized * p_out_lp->variables[i].obj_val;
  }

  return SubOptimal;
  
}

#endif /* #ifdef LOCAL_SOLVER */
