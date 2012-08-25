
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
      V(1) cerr << TS() << "New solution! (Obj:"<< getDoubleInfo( GRB_CB_MIPSOL_OBJ ) <<")" << endl;
      
      /* Push the solution to the stack. */
      m_lp.second_best_solution_stack = m_lp.best_solution_stack;
      m_lp.best_solution_stack.clear();
      
      repeat( i, m_lp.variables.size() ) m_lp.best_solution_stack.push_back( getSolution( m_varmap[i] ) );

      repeat( i, m_lp.constraints.size() ) {
        if( !m_lp.constraints[i].is_lazy ) continue;

        double           val = 0.0;
        lp_constraint_t &con = m_lp.constraints[i];
        
        repeat( j, con.vars.size() )
          val += con.coes[j] * getSolution( m_varmap[ con.vars[j] ] );

        if( !con.isSatisfied(val) ) {
          GRBLinExpr expr_lin;

          repeat( j, con.vars.size() )
            expr_lin  += con.coes[j] * m_varmap[ con.vars[j] ];

          GRBEXECUTE(
                     if( LessEqual == con.opr )         addLazy( expr_lin, GRB_LESS_EQUAL, con.rhs );
                     else if( GreaterEqual == con.opr ) addLazy( expr_lin, GRB_GREATER_EQUAL, con.lhs );
                     else if( Equal == con.opr )        addLazy( expr_lin, GRB_EQUAL, con.rhs );
                     else if( Range == con.opr ) {      addLazy( expr_lin, GRB_LESS_EQUAL, con.rhs ); addLazy( expr_lin, GRB_GREATER_EQUAL, con.lhs ); }
                     );

          num_activated++;
          
          con.is_lazy = false;
        }
      }
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

ilp_solution_type_t function::solveLP_BnB( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache ) {

  GRBEnv            env;
  GRBModel          model( env );

  gurobi_varmap_t   var_map;
  gurobi_callback_t cb( *p_out_lp, *p_out_lprel, *p_out_cache, c, var_map );
  
  cb.m_timeout = c.timelimit;

  V(2) cerr << TS() << "Converting the problem into LP optimization problem..." << endl;
  
  /* Create variables. */
  GRBEXECUTE(
  repeat( i, p_out_lp->variables.size() ) {
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
    case Equal: {        model.addConstr( expr_lin, GRB_EQUAL, con.lhs, con.name.substr(0, 32) );         break; }
    case LessEqual: {    model.addConstr( expr_lin, GRB_LESS_EQUAL, con.rhs, con.name.substr(0, 32) );    break; }
    case GreaterEqual: { model.addConstr( expr_lin, GRB_GREATER_EQUAL, con.rhs, con.name.substr(0, 32) ); break; }
    case Range: {        model.addRange( expr_lin, con.lhs, con.rhs, con.name.substr(0, 32) );            break; }
    default:             cerr << TS() << "SolveLP_BnB: Unknown constraint type." << endl;
    }, p_out_lp->constraints[i].toString( p_out_lp->variables )
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
  
  if( InvalidCutoff != p_out_lp->cutoff ) model.getEnv().set( GRB_DoubleParam_Cutoff, p_out_lp->cutoff );
  //if( CuttingPlaneBnB == c.method ) GRBEXECUTE(model.getEnv().set( GRB_IntParam_DualReductions, 0 ));
  GRBEXECUTE(model.getEnv().set( GRB_IntParam_DualReductions, 0 ));
                                               
  GRBEXECUTE(model.setCallback( &cb ));
  
  if( c.is_ilp_verbose ) beginXMLtag( "ilp-log", "solver=\"gurobi\"" );

  double time_start     = getTimeofDaySec();
  bool   f_got_solution = false;
  
  g_p_model = &model;
  
  if( CuttingPlaneBnB == c.method ) {

    int n, num_constraints_added = 0;
    
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

      foreachc( pairwise_vars_t, iter_t1, p_out_lprel->pp2v )
        for( unordered_map<store_item_t, int>::const_iterator iter_t2=iter_t1->second.begin(); iter_t1->second.end()!=iter_t2; ++iter_t2 ) {
          if( c.isTimeout() ) goto BED;
          if( !p_out_cache->evc.isInSameCluster(iter_t1->first, iter_t2->first) ) continue;
          
          store_item_t                 t1 = iter_t1->first, t2 = iter_t2->first;
          unordered_set<store_item_t> &vs = p_out_cache->evc.clusters[p_out_cache->evc.map_v2c[t1]];

          /* TRANSITIVE RELATIONS SHOULD HOLD WITH THE OTHER VARIABLES
             IN THE SAME EQV CLUSTER. */
          foreach( unordered_set<store_item_t>, iter_tu, vs ) {
            if(c.isTimeout()) goto BED;
            if(*iter_tu == t1 || *iter_tu == t2) continue;

            int    v_ij = _getCorefVar(t1, t2, *p_out_lprel), v_ik = _getCorefVar(t1, *iter_tu, *p_out_lprel), v_jk = _getCorefVar(t2, *iter_tu, *p_out_lprel);
            double s_ij = var_map[v_ij].get(GRB_DoubleAttr_X), s_ik = var_map[v_ik].get(GRB_DoubleAttr_X), s_jk = var_map[v_jk].get(GRB_DoubleAttr_X);

            if( -s_ij - s_jk + s_ik < -1 ) { model.addConstr( -var_map[v_ij] - var_map[v_jk] + var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
            if( -s_ij + s_jk - s_ik < -1 ) { model.addConstr( -var_map[v_ij] + var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
            if(  s_ij - s_jk - s_ik < -1 ) { model.addConstr(  var_map[v_ij] - var_map[v_jk] - var_map[v_ik] >= -1 ); num_constraints_locally_added++; }
          }
        }


      num_constraints_added += num_constraints_locally_added;
      
      cerr << TS() << "CPI: I=" << n << ": Finished. Obj:"<< model.get(GRB_DoubleAttr_ObjVal) <<": Violated:" << num_constraints_locally_added << " (Total: " << num_constraints_added << ")" << endl;

      f_got_solution = true;
      
      repeat( j, p_out_lp->variables.size() )
        p_out_lp->variables[j].optimized = var_map[j].get(GRB_DoubleAttr_X);

      p_out_lp->optimized_obj = model.get(GRB_DoubleAttr_ObjVal);
      model.reset();
      
      if( 0 == num_constraints_locally_added ) { cerr << TS() << "CPI: I=" << n << ": No violation." << endl; break; }
      
      continue;
      
    BED:
      break;
      
    }

    if( !c.isTimeout() ) {
      cerr << TS() << "CPI: Finished: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
    } else {
      cerr << TS() << "CPI: Finished: Timeout: " << "I=" << n << ", Activated constraints:" << num_constraints_added << endl;
    }
    
  } else {
    signal( SIGINT, _cb_stop_ilp );
    GRBEXECUTE( model.optimize() );
    signal( SIGINT, catch_int );
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
        
    p_out_lp->optimized_obj = 0.0;
    
    repeat( i, p_out_lp->variables.size() ) {
      if( p_out_lp->variables[i].isFixed() )                p_out_lp->variables[i].optimized = p_out_lp->variables[i].fixed_val;
      else if( -9999.0 != p_out_lp->variables[i].init_val ) p_out_lp->variables[i].optimized = p_out_lp->variables[i].init_val;
      else                                                  p_out_lp->variables[i].optimized = p_out_lp->variables[i].lb;
      p_out_lp->optimized_obj += p_out_lp->variables[i].obj_val * p_out_lp->variables[i].optimized;
    }

    return NotAvailable;
  }

  if( !f_got_solution ) {
    repeat( j, p_out_lp->variables.size() )
      p_out_lp->variables[j].optimized = var_map[j].get(GRB_DoubleAttr_X);

    p_out_lp->optimized_obj = model.get(GRB_DoubleAttr_ObjVal);
  }
  
  /* Prohibit to get the optimal solution. */
  // repeat( i, c.k_best ) {
  //   GRBLinExpr expr;
  //   int        num_nonzero = 0;

  //   repeat( j, p_out_lp->variables.size() ) {
  //     //expr += (1.0 == p_out_lp->variables[j].optimized ? -1.0 : 1.0) * var_map[j];
  //     expr += p_out_lp->variables[j].obj_val * var_map[j];
  //     if( 1.0 == p_out_lp->variables[j].optimized ) num_nonzero++;
  //   }

  //   //model.addConstr( expr <= p_out_lp->variables.size() * 1.0 - 1 - num_nonzero );
  //   model.addConstr( expr <= model.get(GRB_DoubleAttr_ObjVal)-0.01 );
  //   model.reset();

  //   repeat( j, p_out_lp->variables.size() ) {
  //     if( !p_out_lp->variables[j].isFixed() )
  //       var_map[j].set( GRB_DoubleAttr_Start, p_out_lp->second_best_solution_stack[j] );
  //   }
  
  //   model.optimize();
  // }
  
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
        cerr << TS() << p_out_lp->variables[i].ub - p_out_lp->variables[i].lb << endl;
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
  p_out_lp->optimized_obj = 0.0;
  
  repeat( i, p_out_lp->variables.size() ) {
    p_out_lp->variables[i].optimized = 0.0;
    
    repeat( j, var_map[i].size() ) {
      if( var_map[i].size() > 1 ) cerr << TS() << var_map[i][j]->getValue() << endl;
      p_out_lp->variables[i].optimized += pow( 2, j ) * var_map[i][j]->getValue();
    }
    
    p_out_lp->optimized_obj += p_out_lp->variables[i].optimized * p_out_lp->variables[i].obj_val;
  }

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
    
