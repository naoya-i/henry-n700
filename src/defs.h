#pragma once

#define USE_GUROBI
#define USE_LOCALSOLVER

#include <sqlite3.h>

#include <vector>
#include <deque>
#include <string>
#include <list>

#include <iostream>
#include <sstream>

#include <tr1/unordered_map>
#include <tr1/unordered_set>

#include <sys/time.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <signal.h>

#include "darts.h"

#include <Python.h>

#define has_key( dict, key ) (dict.end() != dict.find( key ))

#define PrecompiledAxiomLength 1024

#define ImplicationString "=>"
#define AndString "^"
#define OrString "v"
#define NotString "!"
#define IncString "_|_"

#define FnTrainingLabel "label"
#define PrefixFixedWeight "!"
#define PrefixInvisibleElement "$"

#define EqBias            0.0001
#define InvalidCutoff     -9999.0
#define InvalidFixedValue -9999.0

#define MaxBasicProp 4
#define MaxArguments 12

#define PredicateSubstitution "="

#define OutputInfoFactors "factors"

#define _SC(x) g_store.claim(x)
#define _VC(x) g_store.cashier(x)
#define V(x) if( g_verbose_level >= x )
#define E(x) cerr << "\33[0;41m * ERROR * \33[0m" << x << endl;
#define W(x) cerr << "\33[0;41m * WARNING * \33[0m" << x << endl;
#define _N(x) cerr << "\33[1;40m" << x << "\33[0m" << endl;

#define _A(x, m) if(!(x)) { E(m); throw; }

#define foreach(T, i, v) for( T::iterator i = (v).begin(); (v).end() != i; ++i )
#define foreachr(T, i, v) for( T::reverse_iterator i = (v).rbegin(); (v).rend() != i; ++i )
#define foreachc(T, i, v) for( T::const_iterator i = (v).begin(); (v).end() != i; ++i )
#define repeat(X, N) for( uint_t X=0; X<N; X++ )
#define repeatf(X, Y, N) for( uint_t X=Y; X<N; X++ )

using namespace std;
using namespace std::tr1;

extern deque<void(*)(int)> g_exit_callbacks;
extern deque<string>  g_xml_stack;
extern ostream       *g_p_out;
extern int            g_verbose_level;

/* Usage! */
static const char *str_usage = 
  "Usage: \n"
  "  henry -m <command> [options...] <input_file> <input_file> ...]\n"
  "\n"
  "Command: \n"
  " infer       Performs abductive inference on the specified dataset.\n"
  " learn       Learns the parameters of scoring model given the (incomplete) training instances.\n"
  " compile_kb  Builds a hash database for generating candidate hypotheses efficiently.\n"
  "\n"
  "Options:\n"
  "   -e    Extension module.\n"
  ""
  " compile_kb:\n"
  "   -o F   Write a compiled knowledge base into F.\n"
  ""
  " infer:\n"
  "   -b B   Use B as a precompiled background knowledge.\n"
  "   -p P   Perform inference only for the observation P.\n"
  "   -d D   Stop backward chaining up to the depth D.\n"
  "   -T t   Performs abductive inference under the t seconds.\n"
  "   -t T   Use T threads for inference.\n"
  "   -O o   Outputs information about o. (o=proofgraph|ilp|varcluster)\n"
  "   -c C   Limit the number of variable clusters to c. \n"
  "   -i I   Use the inference method i (bnb, ls, rlp, cpi).\n"
  "   -X i   Prohibit i from being hypothesized.\n"
  ""
  "   -A    Lists used axioms.\n"
  "   -B    Lists used axioms in the best interpretation.\n"
  "   -S    Lists substituted variables.\n"
  " learn (EXPERIMENTAL):\n"
  "   -C    Sets a margin parameter (default = 1.0).\n"
  "   -N    Iterates a learning procedure for a specified number of times (default = 10).\n"
  "   -E    Sets a termination criterion (default = 10e-05).\n"
  "   -b    Specifies a background knowledge for learning.\n"
  "   -v X  Set verbose level to X.\n"
  "";

/* Basic double. */
class random_double_t {
 private:
  double m_value;
 public:
  inline random_double_t() { m_value = 0; 0.5 * (rand() % 10000) / 10000.0; }
  inline operator double () const { return m_value; }
  inline double operator += ( double other ) { m_value += other; }
  inline double operator = ( double other ) { m_value = other; }
};


/* Data types. */
typedef unsigned int                           uint_t;
typedef int                                    store_item_t;
typedef int                                    pg_hypernode_t;
typedef unordered_map<int, string>             command_option_t;
typedef unordered_map<int, vector<pg_hypernode_t> > pg_edge_set_t;
typedef unordered_map<int, vector<int> >       pg_node_hypernode_map_t;
typedef unordered_map<string, random_double_t> weight_vector_t;
typedef unordered_map<string, double>          sparse_vector_t;

enum output_type_t { Class, Structure };
enum ilp_solution_type_t { Optimal, SubOptimal, NotAvailable };
enum logical_operator_t { UnderspecifiedOperator, Literal, AndOperator, OrOperator, ImplicationOperator, NotOperator, IncOperator };
enum sampling_method_t { Random, Uniform };
enum sexp_stack_type_t { ListStack, StringStack, TupleStack };
enum inference_method_t { BnB, LocalSearch, RoundLP, CuttingPlaneBnB };
enum objective_function_t { Cost, LossAugmented, LabelGiven };
enum score_function_type_t { WeightedAbduction, UserDefined };
enum learn_method_t { OnlinePassiveAggressive };
enum pg_node_type_t { UnderspecifiedNode, LogicalNetworkNode, ObservableNode, HypothesisNode, LabelNode };
enum lp_constraint_operator_t { UnderspecifiedCopr, Equal, LessEqual, GreaterEqual, Range, SOS1, SOS2 };
enum feature_function_t { NodeFeature, EdgeFeature };
enum inference_result_type_t { Success, GenerationTimeout, ILPTimeout };

template <class K, class V> V mget( const unordered_map<K,V> &dict, K key, V def ) {
  return dict.end() != dict.find(key) ? dict.find(key)->second : def;
}

template <class T> string join( const T &s_begin, const T &s_end, const string& delimiter = "" ) {
  string exp;
  for( T i=s_begin; s_end!=i; ++i ) {
    exp += (i != s_begin ? delimiter : "") + *i;
  }
  return exp;
}

template <class T> string join( const T &s_begin, const T &s_end, const string &fmt, const string &delimiter ) {
  string exp;
  for( T i=s_begin; s_end!=i; ++i ) {
    char buffer[1024]; sprintf( buffer, fmt.c_str(), *i );
    exp += (i != s_begin ? delimiter : "") + buffer;
  }
  return exp;
}

inline string toString( const string &format, ... ) {
  va_list arg;
  char str_ret[1024 * 100];
  va_start( arg, format );
  vsprintf( str_ret, format.c_str(), arg );
  va_end( arg );
  return string( str_ret );
}

inline string toString( const ilp_solution_type_t& t ) {
  switch( t ) {
  case Optimal: return "Optimal";
  case SubOptimal: return "SubOptimal";
  case NotAvailable: return "NotAvailable";
  };
  return "?";
}
  
inline string TS() {
  time_t t; tm *p_ltm;
  static string weekday[] = { "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"};
  time( &t );
  p_ltm = localtime( &t );
  return toString( "\33[0;34m# %02d/%02d/%04d %02d:%02d:%02d\33[0m] ", 1+p_ltm->tm_mon, p_ltm->tm_mday, 1900+p_ltm->tm_year, p_ltm->tm_hour, p_ltm->tm_min, p_ltm->tm_sec );
}

template <class T> bool has_intersection( const T &s1_begin, const T &s1_end, const T &s2_begin, const T &s2_end ) {
  for( T i1=s1_begin; s1_end!=i1; ++i1 )
    for( T i2=s2_begin; s2_end!=i2; ++i2 )
      if( *i1 == *i2 ) return true;
  return false;
}

inline double getTimeofDaySec() {
  timeval tv;
  gettimeofday(&tv, NULL);
  return tv.tv_sec + (double)tv.tv_usec*1e-6;
}

/* Definition of data structures. */
struct store_t {
  unordered_map<string, store_item_t> s2s;
  vector<string>                      items;
  int                                 issued_variable_count;

  inline store_t() : issued_variable_count(0) {}
  
  inline store_item_t cashier( const string &s ) {
    unordered_map<string, store_item_t>::iterator iter_i;
    store_item_t ret;
    iter_i         = s2s.find( s );
    if( s2s.end() != iter_i ) ret = iter_i->second;
    else {
      items.push_back( s );
      s2s[s]       = items.size()-1;
      ret          = items.size()-1;
    }
    return ret;
  }

  inline string toString( const vector<int> &var_set ) const {
    string exp;
    for( vector<store_item_t>::const_iterator iter_v=var_set.begin(); var_set.end()!=iter_v; ++iter_v )
      exp += (iter_v == var_set.begin() ? "" : ", ") + claim( *iter_v );
    return exp;
  }
  
  inline string toString( const unordered_set<store_item_t> &var_set ) const {
    string exp;
    for( unordered_set<store_item_t>::const_iterator iter_v=var_set.begin(); var_set.end()!=iter_v; ++iter_v )
      exp += (iter_v == var_set.begin() ? "" : ", ") + claim( *iter_v );
    return exp;
  }

  inline store_item_t issueUnknown() {
    char buffer[1024]; sprintf( buffer, "_%d", issued_variable_count++ );
    return cashier( buffer );
  }

  inline void cleanupUnknowns() {
    issued_variable_count = 0;
    repeat( i, items.size() )
      if(0 == items[i].find("_") ) s2s.erase( items[i] );
  }
  
  inline string claim( store_item_t i ) const { return 0 <= i && i < items.size() ? items[ i ] : ""; }
  inline bool isConstant( store_item_t i ) const { char c = items[i][0]; return 'A' <= c && c <= 'Z'; }
  inline bool isUnknown( store_item_t i ) const { return '_' == items[i][0]; };
  inline bool isEqual( store_item_t i, const string &val ) { return val == items[ i ]; }
  inline bool isNegative( store_item_t i ) const { return '-' == items[i][0]; }
  
} extern g_store;

struct mypyobject_t {
  static list<list<PyObject*> > trash_cans;
  static inline void buyTrashCan() { trash_cans.push_back( list<PyObject*>() ); }
  static inline void cleanTrashCan() { foreachr( list<PyObject*>, iter_py, trash_cans.back() ) { Py_DECREF(*iter_py); } trash_cans.pop_back(); }
  PyObject *p_pyobj;
  inline mypyobject_t( PyObject *_p_pyobj ) { p_pyobj = _p_pyobj; if( NULL != p_pyobj ) trash_cans.back().push_back( _p_pyobj ); };
};

struct sexp_stack_t {

  sexp_stack_type_t    type;
  deque<sexp_stack_t*> children;
  string               str;
  
  sexp_stack_t() { type = ListStack; }
  sexp_stack_t( sexp_stack_type_t t ) { type = t; }
  sexp_stack_t( sexp_stack_type_t t, const string& e, list<sexp_stack_t> &stack_list ) {
    type = t;
    if( TupleStack == t ) {
      stack_list.push_back( sexp_stack_t( StringStack, e, stack_list ) );
      children.push_back( &(stack_list.back()) );
    } else str = e;
  }

  inline void _print( string *p_out_str ) const {
    switch( type ) {
    case StringStack: { (*p_out_str) += str; break; }
    case TupleStack: { for( int i=0; i<children.size(); i++ ) { children[i]->_print( p_out_str ); } break; }
    case ListStack: { (*p_out_str) += "("; for( int i=0; i<children.size(); i++ ) { children[i]->_print( p_out_str ); if( i < children.size()-1 ) (*p_out_str) += " "; } (*p_out_str) += ")"; break; }
    }
  }

  inline string toString() const { string exp; _print( &exp ); return exp; }

  inline int findFunctorArgument( string func_name ) const {
    for( int i=0; i<children.size(); i++ ) { if( children[i]->isFunctor( func_name ) ) return i; }
    return -1;
  }

  inline bool isFunctor( const string &func_name = "" ) const {
    if( 1 >= children.size() ) return false;
    if( 0 == children[0]->children.size() ) return false;
    return "" == func_name ? true : func_name == children[0]->children[0]->str;
  }

  inline string getString() const { if( StringStack == type ) return str; return children[0]->str; }
  
};

class sexp_reader_t {
 private:
  istream              &m_stream;
  deque<sexp_stack_t*>  m_stack;
  sexp_stack_t          m_damn;
  list<sexp_stack_t>    m_stack_list;

  sexp_stack_t* new_stack( const sexp_stack_t &ss ) {
    m_stack_list.push_back(ss); return &(m_stack_list.back());
  }
  
 public:
  sexp_stack_t &stack;
  int           n_line;
  
  inline sexp_reader_t( istream &_stream ) : n_line(1), m_stream( _stream ), stack( m_damn ) { m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); ++(*this); };
  inline deque<sexp_stack_t*> &getQueue() { return m_stack; }
  
  sexp_reader_t& operator++();
  bool   isEnd() { return !m_stream.good(); }
};

struct literal_t {
  store_item_t         predicate;
  vector<store_item_t> terms;

  double               wa_number;
  string               extra, instantiated_by;

  inline literal_t() : wa_number(1) {};
  inline literal_t( const sexp_stack_t &s ) : wa_number(1) {
    if( s.isFunctor() ) {
      predicate = g_store.cashier( s.children[0]->children[0]->str );
      for( int i=1; i<s.children.size(); i++ ) {
        if( ':' == s.children[i]->getString()[0] ) {
          int num_colon = 0;
          extra     = s.children[i]->getString().substr(1);
          repeat(j, s.children[i]->getString().length()) if(':' ==s.children[i]->getString()[j]) num_colon++;
          if(3 == num_colon)      wa_number = 1;
          else if(1 == num_colon) wa_number = atof(s.children[i]->getString().substr(1).c_str());
          continue;
        }
        
        terms.push_back( g_store.cashier( s.children[i]->children[0]->str ) );
      }
      
    } else
      predicate = g_store.cashier( s.children[0]->str );
  }
  
  inline literal_t( const string &_predicate ) : wa_number(1) {
    predicate = g_store.cashier( _predicate );
  }

  inline literal_t( const string &_predicate, store_item_t term1, store_item_t term2 ) : wa_number(1) {
    predicate = g_store.cashier( _predicate );
    terms.push_back( term1 );
    terms.push_back( term2 );
  }
  
  inline literal_t( const string &_predicate, store_item_t term1, store_item_t term2, store_item_t term3 ) : wa_number(1) {
    predicate = g_store.cashier( _predicate );
    terms.push_back( term1 );
    terms.push_back( term2 );
    terms.push_back( term3 );
  }

  inline literal_t( const string &_predicate, const string &term1, const string &term2 ) : wa_number(1) {
    predicate = g_store.cashier( _predicate );
    terms.push_back( g_store.cashier( term1 ) );
    terms.push_back( g_store.cashier( term2 ) );
  }
  
  inline bool operator==(const literal_t &other) const {
    if( predicate != other.predicate ) return false;
    if( terms.size() != other.terms.size() ) return false;
    for( int i=0; i<terms.size(); i++ ) if( terms[i] != other.terms[i] ) return false;
    return true;
  }

  inline void _print( string *p_out_str, bool f_colored = false ) const {
    static int color[] = {31, 32, 33, 34, 35, 36, 37, 38, 39, 40};
    (*p_out_str) += f_colored ? ::toString("\33[40m%s\33[0m", g_store.claim( predicate ).c_str()) : g_store.claim( predicate );
    for( int i=0; i<terms.size(); i++ ) {
      if( 0 == i ) (*p_out_str) += "(";
      (*p_out_str) += f_colored ? ::toString("\33[0;%dm%s\33[0m", color[(terms[i]) % 8], _SC(terms[i]).c_str()) : g_store.claim( terms[i] );
      if( i == terms.size()-1 ) (*p_out_str) += ")"; else (*p_out_str) += ",";
    }
    if( f_colored ) (*p_out_str) += ::toString(":%s:[%s]", instantiated_by.c_str(), extra.c_str());
  }

  inline string toString( bool f_colored = false ) const { string exp; _print( &exp, f_colored ); return exp; }
  inline string toPredicateArity() const { char buffer[1024]; sprintf( buffer, "%s/%d", g_store.claim( predicate ).c_str(), (int)terms.size() ); return string( buffer ); }
  inline string toSQL() const {
    vector<string> args; repeat( i, terms.size() ) args.push_back( "'"+g_store.claim(terms[i])+"'" );
    repeat( i, MaxArguments - terms.size() ) args.push_back( "''" );
    return "'"+ g_store.claim(predicate) +"',"+::join( args.begin(), args.end(), "," );
  }
};

struct unifier_t {
  vector<literal_t>                substitutions;
  unordered_map<store_item_t, int> shortcuts;
  unordered_map<store_item_t, store_item_t> mapping;

  inline unifier_t() {};
  
  inline unifier_t( store_item_t x, store_item_t y ) {
    add( x, y );
  }
  
  inline bool apply( literal_t *p_out_lit ) const {
    for( int i=0; i<p_out_lit->terms.size(); i++ ) {
      unordered_map<store_item_t, int>::const_iterator iter_sc = shortcuts.find( p_out_lit->terms[i] );
      
      if( shortcuts.end() == iter_sc ) continue;
      
      if( p_out_lit->terms[i] == substitutions[ iter_sc->second ].terms[0] )
        p_out_lit->terms[i] = substitutions[ iter_sc->second ].terms[1];
      
    }
  }

  inline store_item_t map(store_item_t x) { if(mapping.count(x) == 0) return -1; else return mapping[x]; }
  
  inline bool isApplied( store_item_t x ) {
    return shortcuts.end() != shortcuts.find(x);
  }

  inline void add( store_item_t x, store_item_t y ) {
    if(shortcuts.end() != shortcuts.find(x)) return; //|| shortcuts.end() != shortcuts.find(y) ) return;
    substitutions.push_back( literal_t( "/", x, y ) );
    shortcuts[x]        = substitutions.size()-1;
    mapping[x]          = y;
  }

  inline void add( store_item_t x, const string &variable ) {
    store_item_t y = g_store.cashier( variable );
    add( x, y );
  }
  
  inline string toString() const {
    string exp;
    for( int i=0; i<substitutions.size(); i++ ) {
      if( substitutions[i].terms[0] == substitutions[i].terms[1] ) continue;
      exp += (0 < i ? ", " : "") + g_store.claim(substitutions[i].terms[0]) + "/" + g_store.claim(substitutions[i].terms[1]);
    }
    return "{" + exp + "}";
  }
};

struct logical_function_t {
  logical_operator_t         opr;
  literal_t                  lit;
  vector<logical_function_t> branches;

  inline logical_function_t() : opr( UnderspecifiedOperator ) {}
  inline logical_function_t( const sexp_stack_t &s ) : opr( UnderspecifiedOperator ) {
    if( s.isFunctor( ImplicationString ) ) {
      opr = ImplicationOperator;
      branches.push_back( logical_function_t( *s.children[1] ) ); branches.push_back( logical_function_t( *s.children[2] ) );
    } else if( s.isFunctor( IncString ) ) {
      opr = IncOperator;
      branches.push_back( logical_function_t( *s.children[1] ) ); branches.push_back( logical_function_t( *s.children[2] ) );
    } else if( s.isFunctor( AndString ) || s.isFunctor( OrString ) ) {
      opr = s.isFunctor( AndString ) ? AndOperator : OrOperator;
      for( int i=1; i<s.children.size(); i++ )
        branches.push_back( logical_function_t( *s.children[i] ) );
    } else if( s.isFunctor( NotString ) ) {
      opr = NotOperator;
      for( int i=1; i<s.children.size(); i++ )
        branches.push_back( logical_function_t( *s.children[i] ) );
    } else { /* Assuming s is a literal. */
      opr = Literal;
      lit = literal_t( s );
    }
  }
  
  inline logical_function_t( logical_operator_t _opr, const vector<literal_t> &literals ) : opr( _opr ) {
    for( int i=0; i<literals.size(); i++ ) branches.push_back( logical_function_t( literals[i] ) );
  }

  inline logical_function_t( const literal_t& _lit ) : lit( _lit ), opr( Literal ) {};
  
  inline void _print( string *p_out_str, bool f_colored = false ) const {
    switch( opr ) {
    case Literal: { (*p_out_str) += lit.toString( f_colored ); break; }
    case ImplicationOperator: { branches[0]._print( p_out_str, f_colored ); (*p_out_str) += " => "; branches[1]._print( p_out_str, f_colored ); break; }
    case IncOperator: { branches[0]._print( p_out_str, f_colored ); (*p_out_str) += " _|_ "; branches[1]._print( p_out_str, f_colored ); break; }
    case NotOperator: { (*p_out_str) += "!("; branches[0]._print( p_out_str, f_colored ); (*p_out_str) += ")"; break; }
    case OrOperator:
    case AndOperator: {
      for( int i=0; i<branches.size(); i++ ) {
        if( Literal != branches[i].opr && NotOperator != branches[i].opr ) (*p_out_str) += "(";
        branches[i]._print( p_out_str, f_colored );
        if( Literal != branches[i].opr && NotOperator != branches[i].opr ) (*p_out_str) += ")";
        if( i < branches.size()-1 ) {
          (*p_out_str) += AndOperator == opr ? " " AndString " " : " " OrString " ";
          if( f_colored ) (*p_out_str) += "\n";
        }
      }
      break; }
    }
  }

  inline string toString( bool f_colored = false ) const { string exp; _print( &exp, f_colored ); return exp; }

  inline void getAllLiterals( vector<const literal_t*> *p_out_list ) const {
    switch( opr ) {
    case Literal: { p_out_list->push_back( &lit ); break; }
    case ImplicationOperator: { branches[0].getAllLiterals( p_out_list ); branches[1].getAllLiterals( p_out_list ); break; }
    case IncOperator: { branches[0].getAllLiterals( p_out_list ); branches[1].getAllLiterals( p_out_list ); break; }
    case OrOperator:
    case AndOperator: {
      for( int i=0; i<branches.size(); i++ ) branches[i].getAllLiterals( p_out_list );
      break; }
    }
  }

  inline bool includes( const literal_t& lit ) const {
    vector<const literal_t*> my_literals;
    getAllLiterals( &my_literals );
    for( int i=0; i<my_literals.size(); i++ )
      if( *my_literals[i] == lit ) return true;
    return false;
  }
  
};

typedef unordered_map<store_item_t, unordered_map<int, vector<string> > > precompiled_kb_t;

struct training_data_t {
  output_type_t      type_output;
  logical_function_t x, y_lf;
  int                y_cls;
  string             name, x_sexp;

  inline training_data_t() {}
  inline training_data_t( const logical_function_t &_x, const logical_function_t &_y_lf ) : type_output( Structure ), x( _x ), y_lf( _y_lf ), y_cls(-1) {}
  inline training_data_t( const logical_function_t &_x, const logical_function_t &_y_lf, const string &_name ) : type_output( Structure ), x( _x ), y_lf( _y_lf ), y_cls(-1), name( _name ) {}
  inline training_data_t( const logical_function_t &_x, int _y_cls, const string &_name ) : type_output( Class ), x( _x ), y_cls( _y_cls ), name( _name ) {}

  inline string outputToString() const {
    switch( type_output ) {
    case Class:     return toString( "%d", y_cls );
    case Structure: return y_lf.toString();
    };
    return "?";
  }
  
};

typedef unordered_map<int, unordered_map<int, unifier_t> > pg_unifier_edges_t;
typedef unordered_map<store_item_t, unordered_map<int, vector<int> > > pg_node_map_t;
typedef unordered_map<store_item_t, vector<int> > pg_term_map_t;

struct instantiated_by_t {
  string axiom; int where;
  inline instantiated_by_t() : axiom(""), where(-1) {};
};

struct pg_node_t {
  literal_t             lit;
  pg_node_type_t        type;
  int                   n, depth, obs_node;
  instantiated_by_t     instantiated_by;
  unordered_set<string> axiom_used, axiom_name_used;
  unordered_set<int>    nodes_appeared, parent_node, rhs;
  bool                  f_prohibited;
  
  vector<pair<store_item_t, store_item_t> > cond_neqs;
  
  inline pg_node_t( const literal_t &_lit, pg_node_type_t _type, int _n ) : n(_n), depth(0), obs_node(-1), lit( _lit ), type( _type ), f_prohibited(false) {};

  inline string toString() const {
    return lit.toString() + ::toString( ":%d:%.2f", n, lit.wa_number );
  }
  
};

struct lp_variable_t {
  string name;
  int    opt_level;
  double obj_val, init_val, fixed_val, lb, ub;
  bool   f_continuous, is_obj_square;
  inline lp_variable_t( const string &n ) : opt_level(0), is_obj_square(false), f_continuous(false), name(n), lb(0.0), ub(1.0), fixed_val(InvalidFixedValue), init_val(-9999.0), obj_val(0.0) {};
  inline bool isFixed() const { return InvalidFixedValue != fixed_val; };
  inline void fixValue( double val ) { fixed_val = val; };
  inline void setInitialValue( double val ) { init_val = val; };
  inline string toString() { return name + "=?"; };
};

struct lp_constraint_t {
  lp_constraint_operator_t opr;
  vector<int>              vars;
  vector<double>           coes;
  vector<bool>             quad;
  double                   lhs, rhs;
  bool                     is_active, is_lazy;
  string                   name;

  inline lp_constraint_t( const string &_name ) : name(_name), is_lazy(false), is_active(true), opr(LessEqual), lhs(0), rhs(0) {}
  inline lp_constraint_t( const string &_name, lp_constraint_operator_t _opr ) : name(_name), is_lazy(false), is_active(true), opr(_opr), lhs(0), rhs(0) {}
  inline lp_constraint_t( const string &_name, lp_constraint_operator_t _opr, double val ) : name(_name), is_active(true), is_lazy(false), opr(_opr), lhs(val), rhs(val) {}
  inline lp_constraint_t( const string &_name, lp_constraint_operator_t _opr, double val1, double val2 ) : name(_name), is_lazy(false), is_active(true), opr(_opr), lhs(val1), rhs(val2) {}

  inline void push_back( int var, double coe ) {
    vars.push_back( var ); coes.push_back( coe ); quad.push_back( false );
  }
  
  inline bool isSatisfied( double sol ) const {
    switch( opr ) {
    case Equal:        return lhs == sol;
    case LessEqual:    return sol <= rhs;
    case GreaterEqual: return lhs <= sol;
    case Range:        return lhs <= sol && sol <= rhs;
    }
    return false;
  }
  
  inline bool isSatisfied( const vector<double> &lpsol_optimized_values ) const {
    double val = 0.0;
    for( int i=0; i<vars.size(); i++ ) val += lpsol_optimized_values[ vars[i] ] * coes[i];
    return isSatisfied( val );
  }
  
  inline void _print( string *p_out, const vector<lp_variable_t> &var_instances ) const {

    for( int i=0; i<vars.size(); i++ ) {
      char buffer[10240]; sprintf( buffer, "%.2f * %s", coes[i], var_instances[ vars[i] ].name.c_str() );
      (*p_out) += buffer;
      if( i < vars.size()-1 ) (*p_out) += " + ";
    }
    
    switch( opr ) {
    case Equal: {
      char buffer[1024]; sprintf( buffer, " = %.2f", lhs );
      (*p_out) += buffer;
      break; }

    case LessEqual: {
      char buffer[1024]; sprintf( buffer, " <= %.2f", rhs );
      (*p_out) += buffer;
      break; }
      
    case GreaterEqual: {
      char buffer[1024]; sprintf( buffer, " >= %.2f", rhs );
      (*p_out) += buffer;
      break; }

    case Range: {
      char buffer[1024];
      sprintf( buffer, ": %.2f ~ %.2f", lhs, rhs );
      (*p_out) += buffer;
      break; }
      
    }
    
  }

  inline string toString( const vector<lp_variable_t> &var_instances ) const {
    string exp; _print( &exp, var_instances ); return exp;
  }
  
};

struct linear_programming_problem_t {
  vector<lp_variable_t>   variables;
  vector<lp_constraint_t> constraints;
  double                  cutoff;

  inline linear_programming_problem_t() : cutoff(InvalidCutoff) {}
  
  inline int addVariable( const lp_variable_t &var ) { variables.push_back( var ); return variables.size()-1; }
  inline int addConstraint( const lp_constraint_t &con ) { if( 0 == con.vars.size() ) { return -1; } constraints.push_back( con ); return constraints.size()-1; }
  inline void deactivateConstraint( int con ) { if( -1 != con ) constraints[con].is_active = false; }
  inline void activateConstraint( int con ) { if( -1 != con ) constraints[con].is_active = true; }
  
  inline string toString() {
    ostringstream exp;
    exp << "<ilp variables=\"" << variables.size() << "\" constraints=\"" << constraints.size() << "\">" << endl;
    
    for( int i=0; i<variables.size(); i++ )
      exp << "<variable name=\""<< variables[i].name <<"\" coefficient=\""<< variables[i].obj_val <<"\" />" << endl;
    
    for( int i=0; i<constraints.size(); i++ ) {
      string cons_exp;
      constraints[i]._print( &cons_exp, variables );
      exp << "<constraint name=\""<< constraints[i].name <<"\">" << cons_exp << "</constraint>" << endl;
    }
    
    exp << "</ilp>";
    return exp.str();
  }

};

struct lp_solution_t {
  ilp_solution_type_t sol_type;
  double              optimized_obj;
  vector<double>      optimized_values;

  inline lp_solution_t(const linear_programming_problem_t &lp) : sol_type(NotAvailable) { optimized_values.resize(lp.variables.size()); }

  inline string toString(const linear_programming_problem_t &lp) const {
    ostringstream exp;
    exp << "<solution>" << endl;

    for( int i=0; i<lp.variables.size(); i++ )
      exp << "<variable name=\""<< lp.variables[i].name <<"\" coefficient=\""<< lp.variables[i].obj_val <<"\" />"<< optimized_values[i] <<"</variable>" << endl;
    
    exp << "</solution>";
    return exp.str();
  }
};

typedef unordered_map<store_item_t, unordered_map<store_item_t, int> > pairwise_vars_t;

struct lp_problem_mapping_t {
  unordered_map<int, int>          n2v;
  unordered_map<int, unordered_map<int, int> >          nn2uv;
  unordered_map<int, int>          hn2v;
  unordered_map<int, int>          n2lc;
  unordered_map<store_item_t, int> vc2v;
  pairwise_vars_t                  pp2v;
  
  vector<int>                      v_loss;
  vector<string>                   s_loss;

  unordered_map<int, sparse_vector_t> feature_vector;
  sparse_vector_t                     input_vector;
  
  unordered_map<int, sparse_vector_t> fv_node;
  unordered_map<int, unordered_map<pg_hypernode_t, sparse_vector_t> > fv_edge;
  unordered_map<int, unordered_map<int, sparse_vector_t> > fv_unify;
  unordered_map<store_item_t, unordered_map<store_item_t, unordered_map<int, unordered_map<int, sparse_vector_t> > > >
    fv_unify_vars;

  inline lp_problem_mapping_t() {};
  inline int getCorefVar( store_item_t t1, store_item_t t2 ) const { return t1<t2 ? pp2v.find(t1)->second.find(t2)->second : pp2v.find(t2)->second.find(t1)->second; }
  
};

enum factor_trigger_type_t { IdenticalFactorTrigger, OrFactorTrigger, AndFactorTrigger };
  
struct factor_t {

  vector<int>           triggers;
  vector<bool>          triggers_pol;
  factor_trigger_type_t trigger_type;
  int                   num_neg;

  inline factor_t( factor_trigger_type_t _type ) : trigger_type( _type ), num_neg(0) {};
  
  inline void push_back( int var, bool f_pol = true ) {
    if( -1 == var ) return;
    triggers.push_back( var ); triggers_pol.push_back( f_pol );
    if( !f_pol ) num_neg++;
  }

  inline int apply( linear_programming_problem_t *p_out_lp, const string& name, bool f_prohibit = false, bool f_lazy = false ) {
    if( 0 == triggers.size() ) return -1;
    
    int v_factor = -1;

    if( !f_prohibit && IdenticalFactorTrigger != trigger_type ) v_factor = p_out_lp->addVariable( lp_variable_t( name ) );

    switch( trigger_type ) {
    case IdenticalFactorTrigger: {
      v_factor = triggers[0];
      p_out_lp->variables[ v_factor ].name = name;
      break; }
      
    case AndFactorTrigger: {
      if( !f_prohibit && 1 == triggers.size() ) {
        lp_constraint_t con( name, Equal, (double)-num_neg );
        con.is_lazy = f_lazy;
        
        con.push_back( triggers[0], triggers_pol[0] ? 1.0 : -1.0 );
        con.push_back( v_factor,  -1.0 );
        p_out_lp->addConstraint( con );
      } else {
        lp_constraint_t con( name, Range, 0, 1 );
        con.is_lazy = f_lazy;
      
        repeat( i, triggers.size() )
          con.push_back( triggers[i], triggers_pol[i] ? 1.0 : -1.0 );

        con.lhs = -num_neg;
        con.rhs = 1.0 * con.vars.size() - 1 - num_neg;
        if( !f_prohibit ) con.push_back( v_factor, -1.0 * con.vars.size() );
      
        p_out_lp->addConstraint( con );
      }
      break; }

    case OrFactorTrigger: {
      lp_constraint_t con( name, Range, -1, 0 );
      con.is_lazy = f_lazy;

      repeat( i, triggers.size() )
        con.push_back( triggers[i], triggers_pol[i] ? 1.0 : -1.0 );
      
      con.lhs = -1.0 * con.vars.size() + 1 - num_neg;
      con.rhs = -num_neg;
      if( !f_prohibit ) con.push_back(v_factor, -1.0 * con.vars.size());
      
      p_out_lp->addConstraint( con );
      break; }
    };
    
    return v_factor;
  }
  
};

struct explanation_t {
  lp_solution_t      lpsol;
  
  sparse_vector_t    fv;
  logical_function_t lf;

  inline explanation_t(lp_solution_t &_lpsol) : lpsol(_lpsol) {};
  
};

struct proof_graph_t {
  vector<pg_node_t>     nodes;
  vector<pair<pair<int, int>, unifier_t> > mutual_exclusive_nodes;
  vector<vector<int> > hypernodes;
  vector<int>           labelnodes;
  unordered_set<string> instantiated_axioms;
  string                obs;

  unordered_map<int, unordered_map<string, int> > p_x_axiom;
  
  pg_node_map_t               p2n;
  pg_node_hypernode_map_t     n2hn;
  pg_edge_set_t               edges;
  unordered_map<int, string>  edges_name;
  pg_unifier_edges_t          uedges;
  pg_term_map_t               t2n;
  sqlite3                    *p_db;
  sqlite3_stmt               *p_ins_stmt;

  inline void initializeDatabase() {

    string fields = "";
    
    repeat( i, MaxArguments )
      fields += ::toString(", arg%d TEXT COLLATE NOCASE", i+1);
    
    sqlite3_open( ":memory:", &p_db );
    sqlite3_exec( p_db, ("CREATE TABLE pehypothesis(id INTEGER PRIMARY KEY, predicate TEXT COLLATE NOCASE, suffix TEXT COLLATE NOCASE, path TEXT COLLATE NOCASE"+ fields +")").c_str(), NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehid ON pehypothesis(id)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehpred ON pehypothesis(predicate)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehsuf ON pehypothesis(suffix)", NULL, 0, NULL );

    string quotes = "", quests = "";
    
    repeat( i, MaxArguments ) {
      sqlite3_exec( p_db, toString("CREATE INDEX idxpeharg%d ON pehypothesis(arg%d)", i+1, i+1).c_str(), NULL, 0, NULL );
      quests += ",?"; quotes += ",''";
    }
    
    sqlite3_exec( p_db, "CREATE INDEX idxpeharg12 ON pehypothesis(arg1,arg2)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpeharg23 ON pehypothesis(arg2,arg3)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpeharg13 ON pehypothesis(arg1,arg3)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehpredarg1 ON pehypothesis(predicate,arg1)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehpredarg2 ON pehypothesis(predicate,arg1,arg2)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehpredarg3 ON pehypothesis(predicate,arg1,arg2,arg3)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpeesfxarg1 ON pehypothesis(suffix,arg1)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehsfxarg2 ON pehypothesis(suffix,arg1,arg2)", NULL, 0, NULL );
    sqlite3_exec( p_db, "CREATE INDEX idxpehsfxarg3 ON pehypothesis(suffix,arg1,arg2,arg3)", NULL, 0, NULL );
    sqlite3_exec( p_db, ("INSERT INTO pehypothesis VALUES (-1, '=', '', '-1'"+ quotes +")").c_str(), NULL, 0, NULL );
    sqlite3_exec( p_db, ("INSERT INTO pehypothesis VALUES (-2, '!=', '', '-1'"+ quotes +")").c_str(), NULL, 0, NULL );
    if( SQLITE_OK != sqlite3_prepare_v2( p_db, ("INSERT INTO pehypothesis VALUES (?, ?, ?, ?"+ quests +")").c_str(), -1, &p_ins_stmt, 0 ) ) E( "Database error: prepare statement failed." );
  }

  inline void cleanUpDatabase() {
    sqlite3_close( p_db );
  }
  
  inline string getEdgeName( int i, pg_hypernode_t j ) const {
    ostringstream str_edge;
    
    for( int k=0; k<hypernodes[j].size(); k++ )
      str_edge << nodes[ hypernodes[j][k] ].lit.toPredicateArity() << (k<hypernodes[j].size()-1 ? "^" : "");
      
    str_edge << "=>" << nodes[i].lit.toPredicateArity();
      
    return str_edge.str();
  }

  inline bool getAssociatedHyperNode( const vector<int> **p_out_nodes, int node ) const {

    pg_node_hypernode_map_t::const_iterator iter_nhn = n2hn.find( node );
    if( n2hn.end() == iter_nhn ) return false;

    (*p_out_nodes) = &iter_nhn->second;

    return true;
    
  }
  
  inline bool getNode( const vector<int> **p_out_nodes, store_item_t term ) const {
    
    pg_term_map_t::const_iterator iter_tm = t2n.find( term );    
    if( t2n.end() == iter_tm ) return false;

    (*p_out_nodes) = &iter_tm->second;
      
    return true;
    
  }
  
  inline bool getNode( const vector<int> **p_out_nodes, store_item_t predicate, int arity ) const {
    
    pg_node_map_t::const_iterator iter_nm = p2n.find( predicate );
    if( p2n.end() == iter_nm ) return false;

    unordered_map<int, vector<int> >::const_iterator iter_an = iter_nm->second.find( arity );
    if( iter_nm->second.end() == iter_an ) return false;

    (*p_out_nodes) = &iter_an->second;
      
    return true;
    
  }

  inline bool getNode( vector<int> *p_out_nodes, const literal_t &lit ) const {

    const vector<int> *pa_list;
    if( !getNode( &pa_list, lit.predicate, lit.terms.size() ) ) return false;

    for( int i=0; i<pa_list->size(); i++ ) {
      if( nodes[ (*pa_list)[i] ].lit == lit ) p_out_nodes->push_back( (*pa_list)[i] );
    }

    if( 0 == p_out_nodes->size() ) return false;
    
    return true;
    
  }
  
  inline int addNode( const literal_t &lit, pg_node_type_t type, int n_parent = -1 ) {

    nodes.push_back( pg_node_t( lit, type, nodes.size() ) );
    
    int n = nodes.size()-1;
    p2n[ lit.predicate ][ lit.terms.size() ].push_back( n );

    repeat(i, lit.terms.size()) t2n[ lit.terms[i] ].push_back( n );

    if( LabelNode == type ) labelnodes.push_back( n );

    sqlite3_reset( p_ins_stmt );
    sqlite3_bind_int( p_ins_stmt, 1, n );
    
    string instr = g_store.claim(lit.predicate);
    sqlite3_bind_text( p_ins_stmt, 2, instr.c_str(), instr.length(), SQLITE_STATIC );

    string instr3 = g_store.claim(lit.predicate); instr3 = string::npos == instr3.rfind("-") ? "" : instr3.substr( instr3.rfind("-")+1 );
    sqlite3_bind_text( p_ins_stmt, 3, instr3.c_str(), instr3.length(), SQLITE_STATIC );
    
    unordered_set<int> nps; if( -1 != n_parent ) { nps = nodes[n_parent].nodes_appeared; } nps.insert( n_parent );
    string instr2 = ::join( nps.begin(), nps.end(), "%d", " " );
    sqlite3_bind_text( p_ins_stmt, 4, instr2.c_str(), instr2.length(), SQLITE_STATIC );
    
    if( !g_store.isEqual( lit.predicate, "=" ) && LabelNode != type ) {
    
      repeat( i, MaxArguments ) {
        if( i < lit.terms.size() ) {
          string instr4 = g_store.claim(lit.terms[i]);
          sqlite3_bind_text( p_ins_stmt, MaxBasicProp+1+i, instr4.c_str(), instr4.length(), SQLITE_STATIC );
        } else
          sqlite3_bind_text( p_ins_stmt, MaxBasicProp+1+i, "", 0, SQLITE_STATIC );
      }

      if( SQLITE_DONE != sqlite3_step(p_ins_stmt) ) E( "Database error: insert has not been done." );

    }
    
    return n;
    
  }

  inline int addHyperNode( vector<int> &v ) {
    hypernodes.push_back(v);
    for( int i=0; i<v.size(); i++ ) n2hn[v[i]].push_back( hypernodes.size()-1 );
    return hypernodes.size()-1;
  }
  
  inline int addEdge( int v1, pg_hypernode_t hv2, const string &name ) {
    edges_name[hv2] = name;
    edges[v1].push_back(hv2);
  }

  void printGraph( const lp_solution_t &sol, const linear_programming_problem_t& lpp, const lp_problem_mapping_t &lprel, const string &property = "", ostream* p_out = g_p_out ) const;
  
};

typedef double (*sf_node_t)(const proof_graph_t &gp, int i );
typedef double (*sf_edge_t)(const proof_graph_t &gp, int i, const vector<int> &js );

struct score_function_t {

  score_function_type_t tp;
  weight_vector_t       weights;

  inline score_function_t() : tp( WeightedAbduction ) {}
  
  double getScore( const sparse_vector_t &v_feature, bool f_ignore_weight = false ) {
    double s = 0;

    if( f_ignore_weight ) 
      for( sparse_vector_t::const_iterator iter_f = v_feature.begin(); v_feature.end() != iter_f; ++iter_f )
        s += iter_f->second;
    else
      for( sparse_vector_t::const_iterator iter_f = v_feature.begin(); v_feature.end() != iter_f; ++iter_f )
        s += weights[iter_f->first] * iter_f->second;
      
    return s;
  }

  static double getScore( const weight_vector_t &weights, const sparse_vector_t &v_feature ) {
    double ret = 0.0;
    weight_vector_t::const_iterator iter_w;
    for( sparse_vector_t::const_iterator iter_f = v_feature.begin(); v_feature.end() != iter_f; ++iter_f )
      ret += (weights.end() != (iter_w = weights.find(iter_f->first)) ? iter_w->second : 0.0) * iter_f->second;
    return ret;
  }
  
};

struct variable_cluster_t {

  typedef unordered_map<int, unordered_set<store_item_t> > cluster_t;
  typedef unordered_map<store_item_t, int> variable_mapper_t;
  
  cluster_t                   clusters;
  variable_mapper_t           map_v2c;
  unordered_set<store_item_t> variables;

  inline bool isInSameCluster( store_item_t t1, store_item_t t2 ) {
    variable_mapper_t::iterator i_v1 = map_v2c.find(t1);
    if( map_v2c.end() == i_v1 ) return false;
  
    variable_mapper_t::iterator i_v2 = map_v2c.find(t2);
    if( map_v2c.end() == i_v2 ) return false;
    return i_v1->second == i_v2->second;
  }
  
  inline void add( store_item_t t1, store_item_t t2 ) {

    variables.insert(t1); variables.insert(t2);
    
    variable_mapper_t::iterator iter_c1 = map_v2c.find( t1 ), iter_c2 = map_v2c.find( t2 );
    
    if( map_v2c.end() == iter_c1 && map_v2c.end() == iter_c2 ) {
      static int new_cluster = 0; new_cluster++;
      clusters[ new_cluster ].insert( t1 ); clusters[ new_cluster ].insert( t2 );
      map_v2c[ t1 ] = new_cluster;          map_v2c[ t2 ] = new_cluster;
    } else if( map_v2c.end() != iter_c1 && map_v2c.end() != iter_c2 ) {
      if( iter_c1->second != iter_c2->second ) {
                
        int c1 = iter_c1->second, c2 = iter_c2->second;
        
        for( unordered_set<store_item_t>::iterator iter_v=clusters[c2].begin(); clusters[c2].end()!=iter_v; ++iter_v )
          map_v2c[ *iter_v ] = c1;

        clusters[c1].insert( clusters[c2].begin(), clusters[c2].end() );
        clusters[c2].clear();
      }
    } else if( map_v2c.end() != iter_c1 && map_v2c.end() == iter_c2 ) {
      clusters[ iter_c1->second ].insert( t2 );
      map_v2c[ t2 ] = iter_c1->second;
    } else if( map_v2c.end() == iter_c1 && map_v2c.end() != iter_c2 ) {
      clusters[ iter_c2->second ].insert( t1 );
      map_v2c[ t1 ] = iter_c2->second;
    }
    
  }

  inline string toString() const {

    ostringstream ret;
    
    for( cluster_t::const_iterator iter_ec = clusters.begin(); clusters.end() != iter_ec; ++iter_ec ) {

      if( 0 == iter_ec->second.size() ) continue;
      
      ret << iter_ec->first << ": ";
      
      for( unordered_set<store_item_t>::const_iterator iter_vars = iter_ec->second.begin(); iter_ec->second.end() != iter_vars; ++iter_vars )
        ret << *iter_vars << ", "; // ret << g_store.claim(*iter_vars) << ", ";

      ret << endl;
      
    }

    return ret.str();
      
  }
  
};

struct inference_configuration_t {
  uint_t                         initial_label_index;
  double                         loss;
  string                         extension_module, target_name;
  weight_vector_t                weights;
  bool                           f_use_temporal_weights, f_default_weight1;
  score_function_t              *p_sfunc;
  double                         timelimit, nbthreads, timestart;
  uint_t                         depthlimit, max_variable_clusters;
  inference_method_t             method;
  string                         output_info;
  uint_t                         k_best;
  objective_function_t           objfunc;
  training_data_t                training_instance;
  unordered_map<string, double>  sol_cache;
  unordered_set<int>             prohibited_literals;
  bool                           use_cache, ignore_weight, proofgraph, ilp, is_ilp_verbose, show_variable_cluster, show_statistics;

  /* For cutting plane */
  uint_t cpi_max_iteration, cpi_iteration;
  double cpi_timelimit;
  
  inline inference_configuration_t( score_function_t &s ) :
    ilp(false), proofgraph(false), ignore_weight(false), use_cache(false), is_ilp_verbose(false), show_variable_cluster(false),
    show_statistics(true), k_best(1), f_use_temporal_weights(false), f_default_weight1(false),
    loss(1.0), p_sfunc( &s ), initial_label_index(99999), output_info(""),
    method(LocalSearch), objfunc(Cost), nbthreads(8),
    cpi_max_iteration(9999), cpi_timelimit(9999)
  {};

  inline bool isTimeout() const { return getTimeofDaySec() - timestart > timelimit; }
  inline bool isColoring() const { return string::npos != output_info.find("colored"); }
  inline bool isAxiomOutput() const { return string::npos != output_info.find("axioms"); }
};


struct learn_configuration_t {
  double                    C, E;
  uint_t                    N, S;
  learn_method_t            method;
  inference_configuration_t ci;
  
  inline learn_configuration_t( score_function_t &s ) : ci(s), S(10), C(0.5), N(10), method(OnlinePassiveAggressive) {};
};

struct knowledge_base_t {
  Darts::DoubleArray          da;
  vector<string>              keys;
  vector<string>              axioms;
  unordered_set<store_item_t> constants;
};


typedef unordered_map<store_item_t, vector<string> > si2s_t;
typedef unordered_map<string, unordered_set<string> > y_alignment_t;

struct external_module_context_t {
  const proof_graph_t             *p_proof_graph;
  const lp_problem_mapping_t      *p_lprel;
  const inference_configuration_t *p_c;
};

struct external_module_t {

  string                            filename, args;
  PyObject                         *p_pyglobal;
  unordered_map<string, PyObject*>  f2py;

  inline external_module_t() : p_pyglobal(NULL) {}

  static inline PyObject *getPotentialElementalHypotheses( PyObject *self, PyObject *args ) {
    char *p_query;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "Os", &p_pycon, &p_query);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);

    if( NULL == context.p_proof_graph->p_db ) E( "In-memory database is not available." );
    
    sqlite3_stmt *p_stmt;
    PyObject *p_pylist = PyList_New(0);

    if( SQLITE_OK != sqlite3_prepare_v2(context.p_proof_graph->p_db, p_query, -1, &p_stmt, 0) ) { E( "Invalid query: " << p_query ); }
    else {
      int num_cols = sqlite3_column_count(p_stmt);
      
      if( num_cols ) {
        while( SQLITE_ROW == sqlite3_step(p_stmt) ) {
          PyObject *p_pytuple = PyTuple_New(num_cols);
          
          repeat( i, num_cols ) {
            char *ptr = (char *)sqlite3_column_text(p_stmt, i);
            
            if( 0 != ptr ) PyTuple_SetItem( p_pytuple, i, PyString_FromString(ptr) );
            else           PyTuple_SetItem( p_pytuple, i, PyString_FromString("") );
          }
          
          PyList_Append( p_pylist, p_pytuple );
        }
      }
    }
    
    sqlite3_finalize(p_stmt);

    return p_pylist;
    
  }

  static inline PyObject *asTuple(const proof_graph_t &pg, const pg_node_t &n) {
    PyObject *p_pytuple = PyTuple_New(10), *p_pylist = PyList_New(0);
    PyTuple_SetItem(p_pytuple, 0, PyString_FromString(g_store.claim(n.lit.predicate).c_str()));
    PyTuple_SetItem(p_pytuple, 1, p_pylist);
    PyTuple_SetItem(p_pytuple, 2, PyInt_FromLong(n.n));
    PyTuple_SetItem(p_pytuple, 3, PyString_FromString(n.instantiated_by.axiom.c_str()));
    PyTuple_SetItem(p_pytuple, 4, PyString_FromString(join(n.nodes_appeared.begin(), n.nodes_appeared.end(), "%d", ",").c_str()));
    PyTuple_SetItem(p_pytuple, 5, PyFloat_FromDouble(n.lit.wa_number));
    PyTuple_SetItem(p_pytuple, 6, PyInt_FromLong(n.type));
    PyTuple_SetItem(p_pytuple, 7, PyInt_FromLong(pg.n2hn.count(n.n) > 0 ? pg.n2hn.find(n.n)->second[0] : -1));
    PyTuple_SetItem(p_pytuple, 8, PyInt_FromLong(n.f_prohibited ? 1 : 0));
    PyTuple_SetItem(p_pytuple, 9, PyString_FromString(n.lit.extra.c_str()));
    repeat(i, n.lit.terms.size()) PyList_Append(p_pylist, PyString_FromString(g_store.claim(n.lit.terms[i]).c_str()));
    return p_pytuple;
  }

  static inline PyObject *asListOfTuples(const proof_graph_t &pg) {
    PyObject *p_pyenum = PyList_New(0);
    repeat( i, pg.nodes.size() ) {
      PyObject *p_pytuple = PyTuple_New(5), *p_pylist = PyList_New(0);
      PyTuple_SetItem( p_pytuple, 0, PyString_FromString(g_store.claim(pg.nodes[i].lit.predicate).c_str()) );
      PyTuple_SetItem( p_pytuple, 1, p_pylist );
      PyTuple_SetItem( p_pytuple, 2, PyInt_FromLong(pg.nodes[i].n));
      PyTuple_SetItem( p_pytuple, 3, PyString_FromString(pg.nodes[i].lit.extra.c_str()) );
      PyTuple_SetItem( p_pytuple, 4, PyFloat_FromDouble(pg.nodes[i].lit.wa_number));
      repeat( j, pg.nodes[i].lit.terms.size() ) PyList_Append( p_pylist, PyString_FromString(g_store.claim(pg.nodes[i].lit.terms[j]).c_str()) );
      PyList_Append( p_pyenum, p_pytuple );
    }
    return p_pyenum;
  }
  
  static inline PyObject *getLiterals( PyObject *self, PyObject *args ) {
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "O", &p_pycon);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    PyObject *p_pylist = PyList_New(0);
    
    repeat( i, context.p_proof_graph->nodes.size() )
      PyList_Append(p_pylist, asTuple(*context.p_proof_graph, context.p_proof_graph->nodes[i]));
    
    return p_pylist;
  }
  
  static inline PyObject *getLiteralsFromTerm( PyObject *self, PyObject *args ) {
    char *p_query;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "Os", &p_pycon, &p_query);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    PyObject *p_pylist = PyList_New(0);
    
    const vector<int> *p_t2n;
    if( context.p_proof_graph->getNode( &p_t2n, g_store.cashier(p_query) ) ) {
      repeat( i, p_t2n->size() )
        PyList_Append( p_pylist, asTuple(*context.p_proof_graph, context.p_proof_graph->nodes[ (*p_t2n)[i] ]) );
    }
    
    return p_pylist;
  }

  static inline PyObject *getFactorOfUnification( PyObject *self, PyObject *args ) {
    char *p_v1, *p_v2;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "Oss", &p_pycon, &p_v1, &p_v2);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);

    store_item_t t1 = _VC(p_v1), t2 = _VC(p_v2); if(t1>t2) swap(t1, t2);
    return PyInt_FromLong( context.p_lprel->pp2v.find(t1) != context.p_lprel->pp2v.end() ?
                           (context.p_lprel->pp2v.find(t1)->second.find(t2) != context.p_lprel->pp2v.find(t1)->second.end() ?
                            context.p_lprel->pp2v.find(t1)->second.find(t2)->second : -1) : -1 );
  }

  static inline PyObject *isTimeout( PyObject *self, PyObject *args ) {
    char *p_v1, *p_v2;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "O", &p_pycon);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    return PyBool_FromLong(context.p_c->isTimeout() ? 1 : 0);
  }

  static inline PyObject *getTargetName( PyObject *self, PyObject *args ) {
    char *p_v1, *p_v2;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "O", &p_pycon);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    return PyString_FromString(context.p_c->target_name.c_str());
  }
  
  inline bool initialize() {
    static PyMethodDef p_pyhenryext[] = {
      {"getPotentialElementalHypotheses", getPotentialElementalHypotheses, METH_VARARGS, "How are you?\n"},
      {"getLiteralsFromTerm", getLiteralsFromTerm, METH_VARARGS, "Fine.\n"},
      {"getLiterals", getLiterals, METH_VARARGS, "Really?\n"},
      {"getFactorOfUnification", getFactorOfUnification, METH_VARARGS, "But, ... I'm working in the weekend.\n"},
      {"isTimeout", isTimeout, METH_VARARGS, "Woops."},
      {"getTargetName", getTargetName, METH_VARARGS, "Wao!"},
      {NULL, NULL, 0, NULL}
    };
  
    Py_Initialize();
    Py_InitModule( "henryext", p_pyhenryext );
    
    PyObject *p_pyname = PyFile_FromString( (char *)filename.c_str(), "r" );
    if( NULL == p_pyname ) {
      E( "External module " << filename << " cannot be found." );
      throw;
      return false;
    }

    PyRun_SimpleString( ("_args = '" + args + "'").c_str() );
    PyRun_SimpleString( ("MaxBasicProp = " + toString("%d", MaxBasicProp) ).c_str() );
    PyRun_SimpleString( ("MaxArguments = " + toString("%d", MaxArguments) ).c_str() );
    PyRun_SimpleFile( PyFile_AsFile( p_pyname ), (char *)filename.c_str() );
    Py_DECREF( p_pyname );

    p_pyname   = PyString_FromString("__main__");
    p_pyglobal = PyImport_Import( p_pyname );
    
    if( PyErr_Occurred() ) {
      E( "An error occurred in the external module!" );      
      PyErr_Print();
    }
    
    Py_DECREF( p_pyname );

    return true;
  }

  inline void finalize() {
    for( unordered_map<string,PyObject*>::iterator iter_f2py=f2py.begin(); f2py.end()!=iter_f2py; ++iter_f2py )
      Py_DECREF( iter_f2py->second );
    
    if( NULL != p_pyglobal ) Py_DECREF( p_pyglobal );
    Py_Finalize();
  }

  inline bool isFunctionDefined( const string& function_name ) {
    bool f_ret;

    if( NULL == p_pyglobal ) this->initialize();
    if( NULL == p_pyglobal ) return NULL;
    
    mypyobject_t::buyTrashCan();
    mypyobject_t pyfunc( PyObject_GetAttrString( p_pyglobal, function_name.c_str() ) );
    f_ret = NULL != pyfunc.p_pyobj;
    mypyobject_t::cleanTrashCan();
    PyErr_Clear();
      
    return f_ret;
  }
  
  inline PyObject *call( const string& function_name, PyObject *p_args ) {
    
    if( NULL == p_pyglobal ) this->initialize();
    if( NULL == p_pyglobal ) return NULL;
    
    PyObject *p_pyret, *p_pyfunc;

    if( f2py.end() != f2py.find(function_name) ) p_pyfunc = f2py[function_name];
    else {
      p_pyfunc = PyObject_GetAttrString( p_pyglobal, function_name.c_str() );
      f2py[ function_name ] = p_pyfunc;
    }
    
    mypyobject_t::buyTrashCan();
    
    if( NULL != p_pyfunc && 1 == PyCallable_Check(p_pyfunc) ) {
      p_pyret = PyObject_CallObject(p_pyfunc, p_args);

      if( NULL == p_pyret ) {
        E( "An error occurred in the external module!" );
        if( PyErr_Occurred() ) PyErr_Print();
      }
    } else {
      E( "Function is not callable: " << function_name );
      if( PyErr_Occurred() ) PyErr_Print();
    }

    mypyobject_t::cleanTrashCan();
    
    return p_pyret;
  }
  
} extern g_ext;

struct loss_t {
  double                           loss, maximum_loss, minimum_loss;
  unordered_map<int, double>       weighting;
  si2s_t                           v2l;
  y_alignment_t                    im_not_here;
  const inference_configuration_t &ci;

  inline void setLoss( const training_data_t& td, const logical_function_t& current_y, const lp_problem_mapping_t& lprel, double score ) {

    PyObject *p_pyret = NULL;
    mypyobject_t::buyTrashCan();
      
    external_module_context_t emc = {NULL, &lprel, &ci};
    mypyobject_t pycon( PyCapsule_New( (void*)&emc, NULL, NULL) );
    p_pyret = g_ext.call( "cbGetLoss", Py_BuildValue( "Oss", pycon.p_pyobj, current_y.toString().c_str(), td.y_lf.toString().c_str() ) );
      
    this->loss = PyFloat_AsDouble( PyTuple_GetItem( p_pyret, 0) );

    PyObject *p_pylist_weighting = PyTuple_GetItem(p_pyret, 1);
    repeat( i, PyList_Size( p_pylist_weighting ) ) {
      weighting[ PyInt_AsLong( PyTuple_GetItem( PyList_GetItem( p_pylist_weighting, i ), 0 ) ) ] = PyFloat_AsDouble( PyTuple_GetItem( PyList_GetItem( p_pylist_weighting, i ), 1 ) );
    }
        
    Py_DECREF( p_pyret );
      
    mypyobject_t::cleanTrashCan();
  
  }

  inline loss_t(const inference_configuration_t &_ci): ci(_ci), loss(0), maximum_loss(0), minimum_loss(0) {};

  inline string printVW() {
    string ret;
    foreach( si2s_t, iter_v2l, v2l )
      ret += g_store.claim( iter_v2l->first ) + "={" + ::join( iter_v2l->second.begin(), iter_v2l->second.end() ) + "} " + "\n";

    foreach( y_alignment_t, iter_yl, im_not_here )
      ret += iter_yl->first + ": " + join( iter_yl->second.begin(), iter_yl->second.end(), " ^ " ) + "\n";
    
    return ret;
  }
  
};

struct lp_inference_cache_t {
  int                          num_variable_clusters;
  proof_graph_t                pg;
  linear_programming_problem_t lp;
  lp_problem_mapping_t         lprel;
  loss_t                       loss;
  double                       elapsed_prepare, elapsed_ilp;
  int                          cpi_iteration;
  variable_cluster_t           evc;
  unordered_set<store_item_t>  logical_atomic_terms;

  inline lp_inference_cache_t( const inference_configuration_t &ci ) : loss(ci) {};
  
  inline void printStatistics( const lp_solution_t& lpsol, ostream *p_out = g_p_out ) const {
    (*p_out) << "<statistics>" << endl
             << "<time total=\""<< (elapsed_prepare+elapsed_ilp) <<"\" prepare=\"" << elapsed_prepare << "\" ilp=\"" << elapsed_ilp << "\" />"<< endl
             << "<ilp solution=\""<< toString(lpsol.sol_type) <<"\" variables=\"" << lp.variables.size() << "\" constraints=\"" << lp.constraints.size() << "\" />"<< endl
             << "<search-space literals=\""<< pg.nodes.size() <<"\" axiom=\""<< pg.instantiated_axioms.size() <<"\" />"<< endl
             << "</statistics>" << endl;
  }
  
};

/* Algorithms. */
namespace algorithm {
  inference_result_type_t infer(vector<explanation_t> *p_out_expls, lp_inference_cache_t *p_out_cache, lp_inference_cache_t *p_old_cache, inference_configuration_t& c, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t& kb, bool f_learning, const weight_vector_t &w, ostream *p_out = g_p_out );
  void learn( score_function_t *p_out_sfunc, const learn_configuration_t &c, vector<training_data_t>& t, const knowledge_base_t& kb );
}

/* Functions. */
namespace function {

  bool instantiateBackwardChainings( proof_graph_t *p_out_gp, variable_cluster_t *p_out_evc, int n_obs, const knowledge_base_t &kb, const inference_configuration_t &c );
  bool enumeratePotentialElementalHypotheses( proof_graph_t *p_out_gp, variable_cluster_t *p_out_evc, const logical_function_t &obs, const string &sexp_obs, const knowledge_base_t &kb, const inference_configuration_t &c );
  
  bool convertToLP( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &gp, const variable_cluster_t &evc, inference_configuration_t &c );
  void adjustLP( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &gp, const variable_cluster_t &evc, inference_configuration_t &c );
  ilp_solution_type_t solveLP_BnB( vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache = NULL );
  ilp_solution_type_t solveLP_LS( vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache = NULL );
  void roundUpLP( linear_programming_problem_t *p_out_lp );
  void convertLPToHypothesis(logical_function_t *p_out_h, sparse_vector_t *p_out_fv, const lp_solution_t &sol, const lp_inference_cache_t &cache);
  
  void sample( vector<double> *p_out_array, const sampling_method_t m );

  bool compileKB( knowledge_base_t *p_out_kb, const precompiled_kb_t &pckb );
  bool writePrecompiledKB( precompiled_kb_t &pckb, const string &filename );
  bool readPrecompiledKB( knowledge_base_t *p_out_kb, const string &filename );
  void getParsedOption( command_option_t *p_out_opt, vector<string> *p_out_args, const string &acceptable, int argc, char **argv );

  inline bool isSexpSep( char c ) { return '(' == c || ')' == c || '"' == c || '\'' == c || ' ' == c || '\t' == c || '\n' == c || '\r' == c; };

  inline void beginXMLtag( const string &tag, const string &parameters = "", ostream *p_out = g_p_out ) {
    (*p_out) << "<" << tag << ("" != parameters ? (" " + parameters) : "") << ">" << endl;
    g_xml_stack.push_front( tag );
  }
  
  inline void endXMLtag( const string &tag, ostream *p_out = g_p_out ) {
    (*p_out) << "</" << tag << ">" << endl;
    g_xml_stack.pop_front();
  }
  
  inline void enumerateConstatns( unordered_set<store_item_t> *p_out_cons, const logical_function_t &lf ) {
    vector<const literal_t*> literals;
    lf.getAllLiterals( &literals );
    p_out_cons->clear();
    for( int i=0; i<literals.size(); i++ )
      for( int j=0; j<literals[i]->terms.size(); j++ ) {
        if( g_store.isConstant( literals[i]->terms[j] ) ) p_out_cons->insert( literals[i]->terms[j] );
      }
  }

  inline void enumerateTerms( unordered_set<store_item_t> *p_out_cons, const logical_function_t &lf ) {
    vector<const literal_t*> literals;
    lf.getAllLiterals( &literals );
    for( int i=0; i<literals.size(); i++ )
      for( int j=0; j<literals[i]->terms.size(); j++ )
        p_out_cons->insert( literals[i]->terms[j] );
  }
  
  inline void mulVector( sparse_vector_t *p_out, double coe ) {
    for( sparse_vector_t::const_iterator iter_sv = p_out->begin(); p_out->end() != iter_sv; ++iter_sv )
      (*p_out)[ iter_sv->first ] *= coe;
  }

  inline void mulVector( weight_vector_t *p_out, double coe ) {
    for( weight_vector_t::const_iterator iter_sv = p_out->begin(); p_out->end() != iter_sv; ++iter_sv )
      (*p_out)[ iter_sv->first ] = (*p_out)[ iter_sv->first ] * coe;
  }
  
  inline void addVector( sparse_vector_t *p_out, const sparse_vector_t &sv ) {
    for( sparse_vector_t::const_iterator iter_sv = sv.begin(); sv.end() != iter_sv; ++iter_sv )
      (*p_out)[ iter_sv->first ] += iter_sv->second;
  }

  inline void addVector( weight_vector_t *p_out, const weight_vector_t &sv ) {
    for( weight_vector_t::const_iterator iter_sv = sv.begin(); sv.end() != iter_sv; ++iter_sv )
      (*p_out)[ iter_sv->first ] += iter_sv->second;
  }
  
  inline void dumpVector( const sparse_vector_t &sv ) {
    for( sparse_vector_t::const_iterator iter_sv = sv.begin(); sv.end() != iter_sv; ++iter_sv )
      cerr << iter_sv->first << ":" << iter_sv->second << ", ";
    cerr << endl;
  }
  
  inline string toString( const sparse_vector_t &sv, bool f_colored=false ) {
    ostringstream exp;
    for( sparse_vector_t::const_iterator iter_sv = sv.begin(); sv.end() != iter_sv; ++iter_sv ) {
      exp << "\"" << ::toString(f_colored ? "\33[0;34m%s\33[0m" : "%s", iter_sv->first.c_str()) << "\":" << iter_sv->second << " ";
      if( f_colored ) exp << endl;
    }
    return exp.str();
  }

  inline void getVectorIndices( unordered_set<string> *p_out_indices, const sparse_vector_t &s ) {
    for( sparse_vector_t::const_iterator iter_f = s.begin(); s.end() != iter_f; ++iter_f )
      p_out_indices->insert( iter_f->first );
  }

  inline bool getMGU( unifier_t *p_out_u, const literal_t &p1, const literal_t &p2 ) {
    if( p1.predicate != p2.predicate ) return false;
    if( p1.terms.size() != p2.terms.size() ) return false;
    for( int i=0; i<p1.terms.size(); i++ ) {
      if( p1.terms[i] == p2.terms[i] ) { p_out_u->add( p1.terms[i], p2.terms[i] ); continue; }
      if( g_store.isConstant( p1.terms[i] ) && g_store.isConstant( p2.terms[i] ) ) return false;
      p_out_u->add( p1.terms[i], p2.terms[i] );
    }
    return true;
  }
  
  inline void catch_int( int sig_num ) {
  
    cerr << "Ctrl-C pressed." << endl;

    /* Call clean up codes. */
    for( int i=0; i<g_exit_callbacks.size(); i++ )
      g_exit_callbacks[i]( sig_num );

    /* Close the XML tag. */
    for( int i=0; i<g_xml_stack.size(); i++ )
      (*g_p_out) << "</" << g_xml_stack[i] << ">" << endl;
  
    signal( SIGINT, catch_int );
    exit(0);
  
  }
  
};


