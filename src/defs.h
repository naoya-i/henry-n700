#pragma once

#define USE_OMP
#define USE_GUROBI
//#define USE_LOCALSOLVER
//#define USE_LPSOLVE

#include <sqlite3.h>
#include <cdb.h>

#include <vector>
#include <string>
#include <list>
#include <deque>
#include <algorithm>

#ifdef USE_OMP
#include <omp.h>
#endif

#include <iostream>
#include <sstream>

#include <tr1/unordered_map>
#include <tr1/unordered_set>

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include <sys/resource.h>
#include <sys/time.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <signal.h>

#include <pcrecpp.h>

#include <python2.7/Python.h>

#define mymax(x, y) (x > y ? x : y)
#define mymin(x, y) (x < y ? x : y)
#define has_key( dict, key ) ((dict).end() != (dict).find( key ))
#define get_value( dict, key, def ) (has_key(dict, key) ? (dict).find(key)->second : (def))

#define ImplicationString "=>"
#define AndString         "^"
#define OrString          "v"
#define NotString         "!"
#define IncString         "_|_"

#define FnSearchWithConst       "SEARCH-WITH-CONST"
#define FnDoNotUnify            "DO-NOT-UNIFY"
#define FnDoNotCare             "DO-NOT-CARE"
#define FnExplainedFeatureGroup "EXPLAINED-FEATURE-GROUP"

#define FnInclude             "include"
#define FnTrainingLabel       "label"
#define FnModel               "model"
#define FnWeight              "weight"
#define FnScoreFunc           "S"
#define FnBackgroundKnowledge "B"
#define FnObservation         "O"
#define FnName                "name"
#define FnAxiomDisjoint       "D"

#define PrefixFixedWeight      "!"
#define PrefixFixedValue       "@"
#define PrefixInvisibleElement "$"

#define EqBias            0.0001
#define InvalidCutoff     -9999.0
#define InvalidFixedValue -9999.0

#define MaxBasicProp 4
#define MaxArguments 12

#define PredicateSubstitution "="

#define OutputInfoFactors    "factors"
#define OutputInfoColored    "colored"
#define OutputInfoWeights    "weights"
#define OutputInfoWithNumbers "costs"
#define OutputInfoAxioms     "axioms"
#define OutputInfoILP        "ilp"
#define OutputInfoILPlog     "lpsolverlog"
#define OutputInfoProofgraph "proofgraph"

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
  "   -O o   Outputs information about o. (o=proofgraph|ilp|varcluster)\n"
  "";

class store_item_t;
namespace std { namespace tr1 { template<> struct hash<store_item_t>; }}

class store_item_t {
 private:
  static unordered_map<size_t, string> m_items;
  static int                           m_issued_variable_count;
  static hash<string>                  m_hashier;
  
  size_t m_hash;
  
 public:
  inline operator const string& () const { return m_items[m_hash]; }

  inline store_item_t& operator =(const string &s) {
    m_hash = m_hashier(s);
    #pragma omp critical
    m_items[m_hash] = s;
    return *this;
  };

  inline store_item_t& operator =(const store_item_t &s) { m_hash = s.m_hash; return *this; }
  inline bool operator >(const store_item_t &x) const { return m_hash > x.m_hash; }
  inline bool operator <(const store_item_t &x) const { return m_hash < x.m_hash; }

  inline bool operator ==(const char *s) const { return m_hash == m_hashier(s); }
  inline bool operator !=(const char *s) const { return !(*this == s); }
  inline bool operator ==(const store_item_t &s) const { return m_hash == s.m_hash; }
  inline bool operator !=(const store_item_t &s) const { return m_hash != s.m_hash; }

  inline bool isConstant() const { char c = m_items[m_hash][0]; return 'A' <= c && c <= 'Z'; }
  inline bool isUnknown() const { return '_' == m_items[m_hash][0]; };
  inline bool isEqual(const string &val ) const { return val == m_items[m_hash]; }
  inline bool isNegative() const { return '-' == m_items[m_hash][0]; }
  
  inline const char* c_str() const { return m_items[m_hash].c_str(); }
  inline string toString() const { return m_items[m_hash]; }

  inline size_t getHash() const { return m_hash; }
  
  inline store_item_t(const store_item_t &s) : m_hash(s.m_hash) {};
  inline store_item_t(const string &s) { *this = s; }
  inline store_item_t() {};
  
  static inline string toString(const vector<store_item_t> &var_set) {
    string exp;
    for( vector<store_item_t>::const_iterator iter_v=var_set.begin(); var_set.end()!=iter_v; ++iter_v )
      exp += (iter_v == var_set.begin() ? "" : ", ") + (const string &)*iter_v;
    return exp;
  }

  static inline store_item_t issueUnknown() {
//    return store_item_t("A");
    char buffer[1024];

#pragma omp critical
    sprintf( buffer, "_%d", m_issued_variable_count++ );

    return store_item_t(buffer);
  }

  static inline void cleanupUnknowns() {
    m_issued_variable_count = 0;
  }
  
};

inline std::ostream &operator<<(std::ostream &os, const store_item_t &s) {
  return (os << (const string &)s);
}

namespace std { namespace tr1 {
    template<> struct hash<store_item_t> { size_t operator()(const store_item_t &s) const { return s.getHash(); }; };
  } }

/* Data types. */
typedef unsigned int                        uint_t;
typedef int                                 pg_hypernode_t;
typedef unordered_map<int, string>          command_option_t;
typedef unordered_map<store_item_t, double> sparse_vector_t;

typedef unordered_map<int, vector<pg_hypernode_t> >  pg_edge_set_t;
typedef unordered_map<int, vector<int> >             pg_node_hypernode_map_t;
typedef unordered_map<store_item_t, unordered_map<int, vector<int> > > pg_node_map_t;
typedef unordered_map<store_item_t, vector<int> >    pg_term_map_t;
typedef unordered_map<size_t, unordered_set<int> >   axiom_disjoint_set_t;

enum output_type_t { Class, Structure };
enum ilp_solution_type_t { Optimal, SubOptimal, NotAvailable };
enum logical_operator_t { UnderspecifiedOperator, Literal, AndOperator, OrOperator, ImplicationOperator, NotOperator, IncOperator };
enum sampling_method_t { Random, Uniform };
enum sexp_stack_type_t { ListStack, StringStack, TupleStack };
enum inference_method_t { BnB, LocalSearch, RoundLP, CuttingPlaneBnB, LazyBnB, NoTransitivity };
enum objective_function_t { Cost, LossAugmented, LabelGiven };
enum score_function_type_t { WeightedAbduction, UserDefined };
enum learn_method_t { OnlinePassiveAggressive };
enum pg_node_type_t { UnderspecifiedNode, LogicalNetworkNode, ObservableNode, HypothesisNode, LabelNode };
enum lp_constraint_operator_t { UnderspecifiedCopr, Equal, LessEqual, GreaterEqual, Range, SOS1, SOS2 };
enum feature_function_t { NodeFeature, EdgeFeature };
enum inference_result_type_t { Success, GenerationTimeout, ILPTimeoutAvailable, ILPTimeoutNotAvailable };

/* UTILITIES. */
inline string replace(const string &tInput, const string &tFind, const string &tReplace) {
  size_t uPos = 0, uFindLen = tFind.length(), uReplaceLen = tReplace.length();
  string ret = tInput;

  if( uFindLen == 0 ) return ret;

  for( ;(uPos = ret.find(tFind, uPos)) != string::npos; ) {
    ret.replace(uPos, uFindLen, tReplace);
    uPos += uReplaceLen;
  }

  return ret;
}

inline string _sanitize(const string &s) { return replace(replace(replace(s, "&", "&amp;"), "<", "&lt;"), ">", "&gt;"); }
inline string _desanitize(const string &s) { return replace(replace(replace(s, "&amp;", "&"), "&lt;", "<"), "&gt;", ">"); }

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

namespace function {
  inline string getWord(const string &l) {
    size_t loc_h = l.find("-");
    if(string::npos != l.substr(loc_h+1).find("in")) return l;
    if(string::npos == loc_h) return l;
    return l.substr(0, loc_h);
  }
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
  
  inline sexp_stack_t() { type = ListStack; }
  inline sexp_stack_t( sexp_stack_type_t t ) { type = t; }
  inline sexp_stack_t( sexp_stack_type_t t, const string& e, list<sexp_stack_t> &stack_list ) {
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
  istream              *m_stream;
  string               *m_string_stream;

  int                   m_string_stream_counter;

  list<sexp_stack_t*>  m_stack;
  sexp_stack_t          m_damn;
  list<sexp_stack_t>    m_stack_list;

  sexp_stack_t* new_stack( const sexp_stack_t &ss ) {
    m_stack_list.push_back(ss); return &(m_stack_list.back());
  }
  
 public:
  sexp_stack_t &stack;
  int           n_line;
  size_t        read_bytes;

  inline ~sexp_reader_t() { clearStack(); }
  inline sexp_reader_t() : stack(m_damn) {};
  inline sexp_reader_t(istream &_stream) : n_line(1), read_bytes(0), m_string_stream_counter(-1), m_stream( &_stream ), stack( m_damn ) { m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); ++(*this); };
  inline sexp_reader_t(string &_stream) : n_line(1), read_bytes(0), m_string_stream_counter(0), m_string_stream( &_stream ), stack( m_damn ) { m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); ++(*this); };
  inline list<sexp_stack_t*> &getQueue() { return m_stack; }
  inline list<sexp_stack_t>   &getList() { return m_stack_list; }

  inline void setStream(istream &_stream) { m_stack.clear(); m_stack_list.clear(); n_line = 1; read_bytes = 0; m_string_stream_counter = -1; m_stream = &_stream; stack = m_damn; m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); ++(*this); };
  inline void setStream(string &_stream) { m_stack.clear(); m_stack_list.clear(); n_line = 1; read_bytes = 0; m_string_stream_counter = 0; m_string_stream = &_stream; stack = m_damn; m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); ++(*this); };
  
  sexp_reader_t& operator++();
  inline bool isEnd() { return -1 == m_string_stream_counter ? !m_stream->good() : m_string_stream_counter >= m_string_stream->length()+1; }
  inline bool isRoot() { return 1 == m_stack.size(); }
  inline void clearStack() { m_stack_list.clear(); m_stack.clear(); m_stack.push_back( new_stack( sexp_stack_t(ListStack) ) ); stack = m_damn; }
  inline void clearLatestStack(int n) { repeat(i, n) {m_stack_list.pop_back();} }

  static string escape(const string &str) {
    return replace(str, "'", "\\'");
  }
};

struct literal_t {
  store_item_t         predicate;
  vector<store_item_t> terms;

  double               wa_number;
  string               extra, instantiated_by, theta, instantiated_by_all;
  int                  id, backchained_on, i_am_from;

  inline literal_t() : wa_number(0), id(-1), backchained_on(-1) {};
  inline literal_t( const sexp_stack_t &s ) : wa_number(0), id(-1), backchained_on(-1) {
    if( s.isFunctor() ) {
      predicate = s.children[0]->children[0]->str;
      for( int i=1; i<s.children.size(); i++ ) {
        if( ':' == s.children[i]->getString()[0] ) {
          int num_colon = 0;
          extra     = s.children[i]->getString().substr(1);
          repeat(j, s.children[i]->getString().length()) if(':' ==s.children[i]->getString()[j]) num_colon++;
          
          if(2 <= s.children.size()) {
            if(3 == num_colon)      { string str = s.children[i]->getString(); wa_number = atof(str.substr(1, str.find(":", 1)).c_str()); }
            else if(1 == num_colon) { wa_number = atof(s.children[i]->getString().substr(1).c_str()); }
          }
          continue;
        }

        terms.push_back(store_item_t(StringStack == s.children[i]->type ? s.children[i]->str : s.children[i]->children[0]->str));
      }
      
    } else
      predicate = s.children[0]->str;
  }
  
  inline literal_t( const string &_predicate ) : wa_number(0) {
    predicate = _predicate;
  }

  inline literal_t(store_item_t _predicate, const vector<store_item_t> &_terms) : wa_number(0) {
    predicate = _predicate;
    terms     = _terms;
  }
  
  inline literal_t(const string &_predicate, const vector<store_item_t> &_terms) : wa_number(0) {
    predicate = _predicate;
    terms     = _terms;
  }
  
  inline literal_t(const string &_predicate, const store_item_t& term1, const store_item_t& term2) : wa_number(0) {
    predicate = _predicate;
    terms.push_back(term1);
    terms.push_back(term2);
  }
  
  inline literal_t(const string &_predicate, const string &term1, const string &term2) : wa_number(0) {
    predicate = _predicate;
    terms.push_back(store_item_t(term1));
    terms.push_back(store_item_t(term2));
  }
  
  inline bool operator==(const literal_t &other) const {
    if( predicate != other.predicate ) return false;
    if( terms.size() != other.terms.size() ) return false;
    for( int i=0; i<terms.size(); i++ ) if( terms[i] != other.terms[i] ) return false;
    return true;
  }

  inline void _print( string *p_out_str, bool f_colored = false, bool f_with_number = false ) const {
    static int color[] = {31, 32, 33, 34, 35, 36, 37, 38, 39, 40};
    (*p_out_str) += f_colored ? ::toString("\33[40m%s\33[0m", predicate.c_str()) : (const string&)predicate;
    for( int i=0; i<terms.size(); i++ ) {
      if( 0 == i ) (*p_out_str) += "(";
      (*p_out_str) += f_colored ? ::toString("\33[0;%dm%s\33[0m", color[(terms[i].getHash()) % 8], terms[i].c_str()) : (const string&)terms[i];
      if( i == terms.size()-1 ) (*p_out_str) += ")"; else (*p_out_str) += ",";
    }
    if( f_colored ) (*p_out_str) += ::toString(":%s:[%s]", instantiated_by.c_str(), extra.c_str());
    if( f_with_number  ) (*p_out_str) += ::toString(":%.2f:%s:%d->%d", wa_number, instantiated_by.c_str(), id, backchained_on);
  }

  inline string toString( bool f_colored = false, bool f_with_number = false ) const { string exp; _print( &exp, f_colored, f_with_number ); return exp; }
  inline string toPredicateArity() const { char buffer[1024]; sprintf( buffer, "%s/%d", predicate.c_str(), (int)terms.size() ); return string( buffer ); }
  inline string toSQL() const {
    vector<string> args; repeat( i, terms.size() ) args.push_back( "'"+(const string&)terms[i]+"'" );
    repeat( i, MaxArguments - terms.size() ) args.push_back( "''" );
    return "'"+ (const string&)predicate +"',"+::join( args.begin(), args.end(), "," );
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
  
  inline void _print( string *p_out_str, bool f_colored = false, bool f_with_numbers = false ) const {
    switch( opr ) {
    case Literal: { (*p_out_str) += lit.toString( f_colored, f_with_numbers ); break; }
    case ImplicationOperator: { branches[0]._print( p_out_str, f_colored, f_with_numbers ); (*p_out_str) += " => "; branches[1]._print( p_out_str, f_colored, f_with_numbers ); break; }
    case IncOperator: { branches[0]._print( p_out_str, f_colored, f_with_numbers ); (*p_out_str) += " _|_ "; branches[1]._print( p_out_str, f_colored, f_with_numbers ); break; }
    case NotOperator: { (*p_out_str) += "!("; branches[0]._print( p_out_str, f_colored, f_with_numbers ); (*p_out_str) += ")"; break; }
    case OrOperator:
    case AndOperator: {
      for( int i=0; i<branches.size(); i++ ) {
        if( Literal != branches[i].opr && NotOperator != branches[i].opr ) (*p_out_str) += "(";
        branches[i]._print( p_out_str, f_colored, f_with_numbers );
        if( Literal != branches[i].opr && NotOperator != branches[i].opr ) (*p_out_str) += ")";
        if( i < branches.size()-1 ) {
          (*p_out_str) += AndOperator == opr ? " " AndString " " : " " OrString " ";
          if( f_colored ) (*p_out_str) += "\n";
        }
      }
      break; }
    }
  }

  inline string toString( bool f_colored = false, bool f_with_numbers = false ) const { string exp; _print( &exp, f_colored, f_with_numbers ); return exp; }

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

struct unifier_t {
  vector<literal_t>                substitutions;
  unordered_map<store_item_t, int> shortcuts;
  unordered_map<store_item_t, store_item_t> mapping;

  inline unifier_t() {};
  
  inline unifier_t(const store_item_t& x, const store_item_t& y) {
    add(x, y);
  }

  inline const store_item_t& map(const store_item_t &x) { static store_item_t si_emp(""); if(mapping.count(x) == 0) return si_emp; else return mapping[x]; }
  
  inline void apply(logical_function_t *p_out_lf) const {
    if(AndOperator == p_out_lf->opr || OrOperator == p_out_lf->opr) {
      repeat(i, p_out_lf->branches.size())
        apply(&p_out_lf->branches[i]);
    } else if(Literal == p_out_lf->opr)
      apply(&p_out_lf->lit);
  }
  
  inline void apply( literal_t *p_out_lit ) const {
    for( int i=0; i<p_out_lit->terms.size(); i++ ) {
      unordered_map<store_item_t, int>::const_iterator iter_sc = shortcuts.find( p_out_lit->terms[i] );
      
      if( shortcuts.end() == iter_sc ) continue;
      
      if( p_out_lit->terms[i] == substitutions[ iter_sc->second ].terms[0] )
        p_out_lit->terms[i] = substitutions[ iter_sc->second ].terms[1];
      
    }
  }

  inline bool isApplied(const store_item_t &x) {
    return shortcuts.end() != shortcuts.find(x);
  }

  inline void add(const store_item_t &x, const store_item_t &y) {
    if(0 < shortcuts.count(x)) return; //|| shortcuts.end() != shortcuts.find(y) ) return;
    substitutions.push_back( literal_t( "=", x, y ) );
    shortcuts[x]        = substitutions.size()-1;
    mapping[x]          = y;
  }

  inline void add(const store_item_t &x, const string &variable) {
    store_item_t y = variable;
    add( x, y );
  }
  
  inline string toString() const {
    string exp;
    for( int i=0; i<substitutions.size(); i++ ) {
      if( substitutions[i].terms[0] == substitutions[i].terms[1] ) continue;
      exp += (0 < i ? ", " : "") + (const string&)substitutions[i].terms[0] + "/" + (const string&)substitutions[i].terms[1];
    }
    return "{" + exp + "}";
  }
};

struct training_data_t {
  output_type_t      type_output;
  logical_function_t x, y_lf;
  int                y_cls;
  string             name;

  inline training_data_t() {}
  inline training_data_t( const logical_function_t &_x, const logical_function_t &_y_lf ) : type_output( Structure ), x( _x ), y_lf( _y_lf ), y_cls(-1) {}
  inline training_data_t( const logical_function_t &_x, const logical_function_t &_y_lf, const string &_name ) : type_output( Structure ), x( _x ), y_lf( _y_lf ), y_cls(-1), name( _name ) {}
  inline training_data_t( const logical_function_t &_x, int _y_cls, const string &_name ) : type_output( Class ), x( _x ), y_cls( _y_cls ), name( _name ) {}

  inline bool isLabel(const literal_t &lit) const {
    vector<const literal_t*>  y_literals;
    y_lf.getAllLiterals(&y_literals);
    repeat(i, y_literals.size())
      if(*(y_literals[i]) == lit) return true;
    return false;
  }
  
  inline string outputToString() const {
    switch( type_output ) {
    case Class:     return toString( "%d", y_cls );
    case Structure: return y_lf.toString();
    };
    return "?";
  }
  
};

struct instantiated_by_t {
  string axiom; int where;
  inline instantiated_by_t() : axiom(""), where(-1) {};
};

struct pg_node_t {
  literal_t             lit;
  pg_node_type_t        type;
  int                   n, depth, connected, num_instantiated;
  instantiated_by_t     instantiated_by;
  unordered_set<string> axiom_used, axiom_name_used;
  string                axiom_disj;
  unordered_set<int>    nodes_appeared, rhs;
  bool                  f_prohibited, f_removed;
  
  vector<pair<store_item_t, store_item_t> > cond_neqs;
  
  inline pg_node_t( const literal_t &_lit, pg_node_type_t _type, int _n ) :
    connected(0), n(_n), depth(0), lit( _lit ), type( _type ), f_prohibited(false), f_removed(false),
    num_instantiated(0) {};

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
    
    for( int i=0; i<variables.size(); i++ ) {
      exp << "<variable name=\""<< variables[i].name <<"\" coefficient=\""<< variables[i].obj_val <<"\"";
      if(variables[i].isFixed()) exp << " fixed=\"" << variables[i].fixed_val << "\"";
      if(-9999.0 != variables[i].init_val) exp << " init=\"" << variables[i].init_val << "\"";
      exp << " />" << endl;
    }
    
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

  inline lp_solution_t(const linear_programming_problem_t &lp) : sol_type(NotAvailable), optimized_obj(-999999) { optimized_values.resize(lp.variables.size()); }

  inline string toString(const linear_programming_problem_t &lp) const {
    ostringstream exp;
    exp << "<solution>" << endl;

    for( int i=0; i<lp.variables.size(); i++ ) {
      exp << "<variable name=\""<< lp.variables[i].name <<"\" coefficient=\""<< lp.variables[i].obj_val <<"\"";
      if(lp.variables[i].isFixed()) exp << " fixed=\"" << lp.variables[i].fixed_val << "\"";
      exp << ">" << optimized_values[i] <<"</variable>" << endl;
    }
    
    exp << "</solution>";
    return exp.str();
  }
};

typedef unordered_map<store_item_t, unordered_map<store_item_t, int> > pairwise_vars_t;

struct lp_problem_mapping_t {
  unordered_map<int, int>          n2v, n2ev;
  unordered_map<int, unordered_map<int, int> >          nn2uv, cf2v;
  unordered_map<int, int>          hn2v;
  unordered_map<int, int>          n2lc;
  unordered_map<store_item_t, int> vc2v;
  pairwise_vars_t                  pp2v, eq2v;

  vector<int>    v_loss;
  vector<string> s_loss;

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

  inline factor_t() : trigger_type(OrFactorTrigger), num_neg(0) {};
  inline factor_t( factor_trigger_type_t _type ) : trigger_type( _type ), num_neg(0) {};
  
  inline void push_back( int var, bool f_pol = true ) {
    if( -1 == var ) return;
    triggers.push_back( var ); triggers_pol.push_back( f_pol );
    if( !f_pol ) num_neg++;
  }

  inline int apply( linear_programming_problem_t *p_out_lp, const string& name, bool f_prohibit = false, bool f_lazy = false, bool f_uni_directional = false ) {
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
      if(f_uni_directional) {
        lp_constraint_t con( name, LessEqual, 0 );
        con.is_lazy = f_lazy;

        repeat( i, triggers.size() )
          con.push_back(triggers[i], -1);

        con.push_back(v_factor, 1);

        p_out_lp->addConstraint( con );
      } else {
        lp_constraint_t con( name, Range, -1, 0 );
        con.is_lazy = f_lazy;

        repeat( i, triggers.size() )
          con.push_back( triggers[i], triggers_pol[i] ? 1.0 : -1.0 );

        con.lhs = -1.0 * con.vars.size() + 1 - num_neg;
        con.rhs = -num_neg;
        if( !f_prohibit ) con.push_back(v_factor, -1.0 * con.vars.size());

        p_out_lp->addConstraint( con );
      }
      break; }
    };
    
    return v_factor;
  }
  
};

struct explanation_t {
  lp_solution_t      lpsol;
  
  sparse_vector_t    fv;
  logical_function_t lf, lf_obs;
  double             loss;

  inline explanation_t(lp_solution_t &_lpsol) : lpsol(_lpsol), loss(0.0) {};
  
};

struct knowledge_base_t {
  int context_pruning_cdb;
  vector<unordered_set<int> >   word_docs;
  vector<pair<literal_t,literal_t> > mxpairs;
  
  sqlite3               *p_db;
  sqlite3_stmt          *p_ins_stmt;
  string                 filename;
  bool                   f_writable, f_in_transaction;
  int                    num_axioms;
  int                    num_branches;
  
  unordered_map<string, unordered_map<string, unordered_set<int> > > bc_matrix;
  vector<logical_function_t> inconsistents;

  unordered_set<string> do_not_unifies, do_not_cares, search_constant;
  vector<pcrecpp::RE>   do_not_unifies_regex, do_not_cares_regex, search_constant_regex;

  unordered_map<string, string> explained_map;
  vector<pair<pcrecpp::RE, string> > explained_map_regex;
  
  inline knowledge_base_t(bool f_writable, const string &filename) :
    num_branches(10),
      num_axioms(0), p_db(NULL), p_ins_stmt(NULL), f_in_transaction(false), context_pruning_cdb(-1) {
    open(f_writable, filename);
  }
  
  inline knowledge_base_t(const knowledge_base_t &kb) : p_db(NULL), p_ins_stmt(NULL), f_in_transaction(false) {
    open(kb.f_writable, kb.filename);
    
    if(":memory:" == kb.filename)
      kb.copy(this);
    
    context_pruning_cdb = kb.context_pruning_cdb;

    num_branches    = kb.num_branches;
    num_axioms      = kb.num_axioms;
    do_not_unifies  = kb.do_not_unifies;
    do_not_cares    = kb.do_not_cares;
    search_constant = kb.search_constant;
    explained_map   = kb.explained_map;
    
    do_not_unifies_regex  = kb.do_not_unifies_regex;
    do_not_cares_regex    = kb.do_not_cares_regex;
    search_constant_regex = kb.search_constant_regex;
    explained_map_regex   = kb.explained_map_regex;
  }

  inline knowledge_base_t(bool f_writable, const knowledge_base_t &kb) : p_db(NULL), p_ins_stmt(NULL), f_in_transaction(false) {
    open(f_writable, kb.filename);

    if(":memory:" == kb.filename)
      kb.copy(this);
    
    context_pruning_cdb = kb.context_pruning_cdb;

    num_branches    = kb.num_branches;
    num_axioms      = kb.num_axioms;
    do_not_unifies  = kb.do_not_unifies;
    do_not_cares    = kb.do_not_cares;
    search_constant = kb.search_constant;
    explained_map   = kb.explained_map;
    
    do_not_unifies_regex  = kb.do_not_unifies_regex;
    do_not_cares_regex    = kb.do_not_cares_regex;
    search_constant_regex = kb.search_constant_regex;
    explained_map_regex   = kb.explained_map_regex;
  }
  
  ~knowledge_base_t() {
    V(5) cerr << TS() << "Database closed." << endl;
    sqlite3_finalize(p_ins_stmt); p_ins_stmt = NULL;
    sqlite3_close(p_db);          p_db = NULL;
    ::close(context_pruning_cdb);
  }

  bool copy(knowledge_base_t *p_dest) const;
  bool setContextDatabase(const string &fn);

  inline void registerSearchWithConstant(const string &s) {
    if(0 == s.find("/"))      search_constant_regex.push_back(pcrecpp::RE(s.substr(1)));
    else                      search_constant.insert(s);
  }
  
  inline void registerDoNotUnify(const string &s) {
    if(0 == s.find("/"))      do_not_unifies_regex.push_back(pcrecpp::RE(s.substr(1)));
    else                      do_not_unifies.insert(s);
  }

  inline void registerDoNotCare(const string &s) {
    if(0 == s.find("/"))      do_not_cares_regex.push_back(pcrecpp::RE(s.substr(1)));
    else                      do_not_cares.insert(s);
  }

  inline void registerExplainedFeatureGroup(const string &s, const string &g) {
    if(0 == s.find("/"))      explained_map_regex.push_back(make_pair(pcrecpp::RE(s.substr(1)), g));
    else                      explained_map[s] = g;
  }
  
  int getContextVectorIndex(const string &w) const;
  double calcContextualSimilarity(const string &w1, const string &w2) const;

  inline bool isUnifiable(const string &p, int a) const {
    string s = ::toString("%s/%d", p.c_str(), a);
    if(0 < do_not_unifies.count(s)) return false;

    repeat(i, do_not_unifies_regex.size())
      if(do_not_unifies_regex[i].FullMatch(s)) return false;
    
    return true;
  }

  inline bool isSearchWithConstant(const string &s) const {
    if(0 < search_constant.count(s)) return true;

    repeat(i, search_constant_regex.size())
      if(search_constant_regex[i].FullMatch(s)) return true;

    return false;
  }
  
  inline bool isUnifiable(const string &p, int a, int t) const {
    string s = ::toString("%s/%d/%d", p.c_str(), a, t+1);
    if(0 < do_not_cares.count(s)) return false;

    repeat(i, do_not_cares_regex.size())
      if(do_not_cares_regex[i].FullMatch(s)) return false;
    
    return true;
  }
  
  inline string getExplainedFeatureGroup(const string &s) const {
    if(0 < explained_map.count(s)) return explained_map.find(s)->second;

    repeat(i, explained_map_regex.size())
      if(explained_map_regex[i].first.FullMatch(s)) return explained_map_regex[i].second;
    
    return s;
  }
  
  bool open(bool _f_writable, const string &_filename);
  void newTable();
  
  void beginTransaction();
  void commit();
  void vacuum();
  
  void pruneAxioms(unordered_map<string, unordered_set<int> > *p_out_axiom_set, const vector<const literal_t*> &literals_obs) const;
  bool getAbductiveHypotheses(unordered_map<string, unordered_set<int> > *p_out, const string &key_pa) const;
  bool registerIncAxiom(const sexp_stack_t &srline, const sexp_stack_t &sr);
  bool registerAxiom(const sexp_stack_t &srline, const sexp_stack_t &sr, int _n = 2);

  bool writeBcMatrix();

  struct axiom_t {
    string axiom, rhs_ot;

    inline axiom_t(const string &a, const string &ro) : axiom(a), rhs_ot(ro) {};
  };

  bool search(vector<axiom_t> *p_out_axioms, const string &key_pa, const unordered_set<int> &prominent_axioms,
      int *p_out_filtered_out = NULL, bool f_pruning = false) const;

};

struct variable_cluster_t {

  typedef unordered_map<int, unordered_set<store_item_t> > cluster_t;
  typedef unordered_map<store_item_t, int> variable_mapper_t;
  
  cluster_t                   clusters;
  variable_mapper_t           map_v2c;
  unordered_set<store_item_t> variables;

  inline bool isInSameCluster(const store_item_t& t1, const store_item_t& t2) {
    variable_mapper_t::iterator i_v1 = map_v2c.find(t1);
    if( map_v2c.end() == i_v1 ) return false;
  
    variable_mapper_t::iterator i_v2 = map_v2c.find(t2);
    if( map_v2c.end() == i_v2 ) return false;
    return i_v1->second == i_v2->second;
  }
  
  inline void add(const store_item_t& t1, const store_item_t& t2 ) {

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
      if(0 == iter_ec->second.size()) continue;
      if(clusters.begin() != iter_ec) ret << endl;
      
      ret << iter_ec->first << ": ";
      
      for( unordered_set<store_item_t>::const_iterator iter_vars = iter_ec->second.begin(); iter_ec->second.end() != iter_vars; ++iter_vars )
        ret << *iter_vars << ", ";
    }

    return ret.str();
      
  }
  
};

struct score_function_t {
  struct function_unit_t {
    string             name;
    logical_function_t lf;
    double             weight;

    inline function_unit_t() : weight(0.0) {}
    inline function_unit_t(const logical_function_t &_lf) : weight(0.0) { lf = _lf; }
    inline function_unit_t(const string &_name, const logical_function_t &_lf, double _weight) :
      name(_name), lf(_lf), weight(_weight) {}
  };
    
  vector<function_unit_t> units;
  score_function_type_t   tp;
  sparse_vector_t         weights;

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

  static double getScore( const sparse_vector_t &weights, const sparse_vector_t &v_feature, bool f_ignore_weight = false ) {
    double ret = 0.0;
    sparse_vector_t::const_iterator iter_w;
    for( sparse_vector_t::const_iterator iter_f = v_feature.begin(); v_feature.end() != iter_f; ++iter_f )
      ret += (f_ignore_weight ? 1.0 : (weights.end() != (iter_w = weights.find(iter_f->first)) ? iter_w->second : 0.0)) * iter_f->second;
    return ret;
  }
  
};

struct inference_configuration_t {
  uint_t                         initial_label_index;
  double                         loss;
  string                         extension_module, target_name;
  score_function_t              *p_sfunc;
  double                         timelimit, nbthreads, timestart;
  uint_t                         depthlimit, max_variable_clusters, i_initializer;
  inference_method_t             method;
  string                         output_info;
  uint_t                         k_best;
  objective_function_t           objfunc;
  training_data_t                training_instance;
  unordered_map<string, double>  sol_cache;
  unordered_set<int>             prohibited_literals, hypothesized_literals;
  bool                           no_pruning, use_cache, ignore_weight, explanation_disjoint, use_only_user_score, fix_user_weight, scaling_score_func,
    no_prior, no_explained, implybreak, no_apc4rhs;
  uint_t                         n_start;

  /* For cutting plane */
  uint_t cpi_max_iteration, cpi_iteration;
  double cpi_timelimit;
  
  inline inference_configuration_t( score_function_t &s ) :
    ignore_weight(false), use_cache(false), k_best(1), i_initializer(0),
    loss(1.0), p_sfunc( &s ), initial_label_index(99999), output_info(""), scaling_score_func(false),
    method(LocalSearch), objfunc(Cost), nbthreads(8), explanation_disjoint(false),
    cpi_max_iteration(9999), cpi_timelimit(9999), n_start(0), use_only_user_score(false), fix_user_weight(false),
    no_prior(false), no_explained(false), no_pruning(false), no_apc4rhs(false)
  {};

  inline bool isMemoryGood() const {
    /* struct rusage usage; */
    /* getrusage(RUSAGE_SELF, &usage); */
    return true;
  }
  
  inline bool isTimeout() const { return !isMemoryGood() || (getTimeofDaySec() - timestart > timelimit); }
  inline bool isOutput(const string &option) const { return string::npos != output_info.find(option); }
};

struct proof_graph_t {
  typedef unordered_map<size_t, vector<int> > eqhash_t;
  typedef unordered_map<store_item_t, int>        var2node_t;
  typedef unordered_map<store_item_t, var2node_t> var2var2node_t;
  typedef unordered_map<store_item_t, string> var_type_t;
  typedef unordered_map<store_item_t, unordered_map<store_item_t, vector<int> > > eq2hnu_t;

  eqhash_t              eqhash;
  vector<pg_node_t>     nodes;
  vector<pair<pair<int, int>, unifier_t> > mutual_exclusive_nodes;
  vector<vector<int> > hypernodes;
  vector<int>           labelnodes;
  unordered_set<string> used_axiom_tokens, used_axiom_types;
  unordered_set<string> observed_variables, backchained_on;
  unordered_set<string> already_ua_produced;
    
  axiom_disjoint_set_t  axiom_disjoint_set;
  string                obs;
  int                   n_start;
  bool                  f_obs_processed, f_lbl_processed, f_label_not_found;
  var2var2node_t        nodes_sub, nodes_negsub;
  
  eq2hnu_t              eq2hnu;

  unordered_map<store_item_t, unordered_set<store_item_t> > constants_sub;
  unordered_set<int> unification_hns;

  unordered_map<int, int> type_restriction;
  
  unordered_map<int, unordered_map<string, int> > p_x_axiom;
  
  var_type_t                 var_type, var_type_var;
  variable_cluster_t         vc_unifiable, vc_neg_unifiable, vc_observed;
  pg_node_map_t              p2n;
  pg_node_hypernode_map_t    n2hn;
  pg_edge_set_t              edges;
  unordered_map<int, string> edges_name;
  unordered_map<int, string> edges_axiom;
  unordered_map<int, int>    edges_rhs;
  unordered_map<int, unordered_map<int, pg_hypernode_t> > u2hn;
  pg_term_map_t              t2n;

  inline proof_graph_t() : f_obs_processed(false), f_lbl_processed(false), f_label_not_found(false) {}

  inline pg_hypernode_t getUnifierHyperNode(int ni, int nj) {
    if(ni > nj) swap(ni, nj);

    unordered_map<int, unordered_map<int, pg_hypernode_t> >::const_iterator i = u2hn.find(ni);
    if(u2hn.end() == i) return -1;

    unordered_map<int, pg_hypernode_t>::const_iterator j = i->second.find(nj);
    if(i->second.end() == j) return -1;

    return j->second;
  }

  inline double getNormalizer() const {
    if(0 == vc_unifiable.variables.size()) return 1.0;
    return 1.0 / (vc_unifiable.variables.size() * vc_unifiable.variables.size());
  }
  
  inline string getEdgeName( int i, pg_hypernode_t j ) const {
    ostringstream str_edge;
    
    for( int k=0; k<hypernodes[j].size(); k++ )
      str_edge << nodes[ hypernodes[j][k] ].lit.toPredicateArity() << (k<hypernodes[j].size()-1 ? "^" : "");
      
    str_edge << "=>" << nodes[i].lit.toPredicateArity();
      
    return str_edge.str();
  }

  inline string hypernodeToString(pg_hypernode_t j) const {
    ostringstream str_edge;
    
    for( int k=0; k<hypernodes[j].size(); k++ )
      str_edge << nodes[ hypernodes[j][k] ].toString() << (k<hypernodes[j].size()-1 ? "^" : "");
      
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

    if(NULL != p_out_nodes) (*p_out_nodes) = &iter_an->second;

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

  inline void removeNode(pg_node_t &n) {
    n.f_removed = true;
  }

  inline int getSubNode(const store_item_t &t1, const store_item_t &t2) const {
    if(t1 < t2) {
      unordered_map<store_item_t, unordered_map<store_item_t, int> >::const_iterator i = nodes_sub.find(t1);
      if(nodes_sub.end() == i) return -1;

      unordered_map<store_item_t, int>::const_iterator j = i->second.find(t2);
      if(i->second.end() == j) return -1;

      return j->second;
      
    } else {
      unordered_map<store_item_t, unordered_map<store_item_t, int> >::const_iterator i = nodes_sub.find(t2);
      if(nodes_sub.end() == i) return -1;

      unordered_map<store_item_t, int>::const_iterator j = i->second.find(t1);
      if(i->second.end() == j) return -1;

      return j->second;
      
    }
    return -1;
  }
  
  inline int getNegSubNode(const store_item_t &t1, const store_item_t &t2) const {
    if(t1 < t2) {
      unordered_map<store_item_t, unordered_map<store_item_t, int> >::const_iterator i = nodes_negsub.find(t1);
      if(nodes_negsub.end() == i) return -1;

      unordered_map<store_item_t, int>::const_iterator j = i->second.find(t2);
      if(i->second.end() == j) return -1;
      
      return j->second;
      
    } else {
      unordered_map<store_item_t, unordered_map<store_item_t, int> >::const_iterator i = nodes_negsub.find(t2);
      if(nodes_negsub.end() == i) return -1;

      unordered_map<store_item_t, int>::const_iterator j = i->second.find(t1);
      if(i->second.end() == j) return -1;
      
      return j->second;
      
    }
    return -1;
  }

  inline bool isCompatibleType(const store_item_t &t1, const store_item_t &t2) const {
    var_type_t::const_iterator i1 = var_type.find(t1), i2 = var_type.find(t2);
    if(var_type.end() == i1 || var_type.end() == i2) return true;
    return i1->second == i2->second;
  }

  inline int addNode( const literal_t &lit, pg_node_type_t type, int n_parent = -1 ) {
    nodes.push_back(pg_node_t( lit, type, nodes.size()));
    
    int n = nodes.size()-1;
    p2n[ lit.predicate ][ lit.terms.size() ].push_back( n );
    
    if(lit.predicate == PredicateSubstitution) {
      store_item_t t1=lit.terms[0], t2=lit.terms[1]; if(t1 > t2) swap(t1, t2);
      vc_unifiable.add(t1, t2);
      nodes_sub[t1][t2] = n;
      if(t1.isConstant() && !t2.isConstant()) constants_sub[t2].insert(t1);
      else if(t2.isConstant() && !t1.isConstant()) constants_sub[t1].insert(t2);
    }

    if(lit.predicate == "!=") {
      store_item_t t1=lit.terms[0], t2=lit.terms[1]; if(t1 > t2) swap(t1, t2);
      nodes_negsub[t1][t2] = n;
      vc_neg_unifiable.add(t1, t2);
    }

    if(string::npos != lit.predicate.toString().find("-vb") ||
        string::npos != lit.predicate.toString().find("-nn") ||
        string::npos != lit.predicate.toString().find("-adj"))
      var_type[lit.terms[0]] = lit.predicate;

    if(string::npos != lit.predicate.toString().find("event"))
      var_type_var[lit.terms[0]] = lit.terms[1];
    
    static hash<string> hashier;
    
    repeat(i, lit.terms.size()) {
      t2n[ lit.terms[i] ].push_back( n );
      eqhash[hashier(::toString("%s:%d:%s", lit.toPredicateArity().c_str(), i, lit.terms[i].c_str()))].push_back(n);
    }

    if(LabelNode == type) labelnodes.push_back( n );
    return n;
  }

  inline bool isHyperNodeForUnification(pg_hypernode_t hn) const {
    return 0 < unification_hns.count(hn);
  }
  
  inline int addHyperNode(vector<int> &v, bool f_for_unification = false) {
    hypernodes.push_back(v);
    repeat(i, v.size()) n2hn[v[i]].push_back(hypernodes.size()-1);
    if(f_for_unification) unification_hns.insert(hypernodes.size()-1);
    return hypernodes.size()-1;
  }

  inline bool isAllObserved(int hn) const {
    repeat(i, hypernodes[hn].size())
      if(HypothesisNode == nodes[hypernodes[hn][i]].type) return false;
    
    return true;
  }
  
  inline int addEdge( int v1, pg_hypernode_t hv2, const string &name, int num_rhs, const string &axiom = "" ) {
    edges_name[hv2] = name;
    edges_axiom[hv2] = axiom;
    edges_rhs[hv2]   = num_rhs;
    edges[v1].push_back(hv2);
  }

  bool produceEqualityAssumptions(const knowledge_base_t &kb, const inference_configuration_t &c);
  void printGraph( const lp_solution_t &sol, const linear_programming_problem_t& lpp, const lp_problem_mapping_t &lprel, const string &property = "", ostream* p_out = g_p_out, logical_function_t *p_hypothesis = NULL ) const;
  bool produceUnificationAssumptions(const knowledge_base_t &kb, const inference_configuration_t &c);
  void detectInconsistentNodes(int n_obs, const logical_function_t&);
  
};

typedef double (*sf_node_t)(const proof_graph_t &gp, int i );
typedef double (*sf_edge_t)(const proof_graph_t &gp, int i, const vector<int> &js );

struct learn_configuration_t {
  double                    C, E;
  uint_t                    N, S;
  learn_method_t            method;
  inference_configuration_t ci;
  
  inline learn_configuration_t( score_function_t &s ) : ci(s), S(10), C(0.5), N(10), method(OnlinePassiveAggressive) {};
};

struct external_module_context_t {
  const proof_graph_t             *p_proof_graph;
  const lp_problem_mapping_t      *p_lprel;
  const inference_configuration_t *p_c;
  const float                      score;
  string                           loss_msg;
};

struct external_module_t {

  string                            filename, args;
  PyObject                         *p_pyglobal;
  unordered_map<string, PyObject*>  f2py;

  inline external_module_t() : p_pyglobal(NULL) {}

  static inline PyObject *asDict(const proof_graph_t &pg, const pg_node_t &n) {
    PyObject *p_pydict = PyDict_New(), *p_pylist = PyList_New(0);
    PyDict_SetItemString(p_pydict, "predicate", PyString_FromString(n.lit.predicate.c_str()));
    PyDict_SetItemString(p_pydict, "terms", p_pylist);
    PyDict_SetItemString(p_pydict, "node_id", PyInt_FromLong(n.n));
    PyDict_SetItemString(p_pydict, "node_parents", PyString_FromString(join(n.nodes_appeared.begin(), n.nodes_appeared.end(), "%d", ",").c_str()));
    PyDict_SetItemString(p_pydict, "node_type", PyInt_FromLong(n.type));
    PyDict_SetItemString(p_pydict, "axiom", PyString_FromString(n.instantiated_by.axiom.c_str()));
    PyDict_SetItemString(p_pydict, "axiom_all", PyString_FromString(n.lit.instantiated_by_all.c_str()));
    PyDict_SetItemString(p_pydict, "axiom_theta", PyString_FromString(n.lit.theta.c_str()));
    PyDict_SetItemString(p_pydict, "extra", PyString_FromString(n.lit.extra.c_str()));
    repeat(i, n.lit.terms.size()) PyList_Append(p_pylist, PyString_FromString(n.lit.terms[i].c_str()));
    return p_pydict;
  }
  
  static inline PyObject *asTuple(const proof_graph_t &pg, const pg_node_t &n) {
    PyObject *p_pytuple = PyTuple_New(12), *p_pylist = PyList_New(0);
    PyTuple_SetItem(p_pytuple, 0, PyString_FromString(n.lit.predicate.c_str()));
    PyTuple_SetItem(p_pytuple, 1, p_pylist);
    PyTuple_SetItem(p_pytuple, 2, PyInt_FromLong(n.n));
    PyTuple_SetItem(p_pytuple, 3, PyString_FromString(n.instantiated_by.axiom.c_str()));
    PyTuple_SetItem(p_pytuple, 4, PyString_FromString(join(n.nodes_appeared.begin(), n.nodes_appeared.end(), "%d", ",").c_str()));
    PyTuple_SetItem(p_pytuple, 5, PyFloat_FromDouble(n.lit.wa_number));
    PyTuple_SetItem(p_pytuple, 6, PyInt_FromLong(n.type));
    PyTuple_SetItem(p_pytuple, 7, PyInt_FromLong(pg.n2hn.count(n.n) > 0 ? pg.n2hn.find(n.n)->second[0] : -1));
    PyTuple_SetItem(p_pytuple, 8, PyInt_FromLong(n.f_prohibited ? 1 : 0));
    PyTuple_SetItem(p_pytuple, 9, PyString_FromString(n.lit.extra.c_str()));
    PyTuple_SetItem(p_pytuple, 10, PyString_FromString(n.lit.instantiated_by_all.c_str()));
    PyTuple_SetItem(p_pytuple, 11, PyString_FromString(n.lit.theta.c_str()));
    repeat(i, n.lit.terms.size()) PyList_Append(p_pylist, PyString_FromString(n.lit.terms[i].c_str()));
    return p_pytuple;
  }

  static inline PyObject *asListOfDicts(const proof_graph_t &pg) {
    PyObject *p_pyenum = PyList_New(0);
    
    repeat(i, pg.nodes.size())
      PyList_Append(p_pyenum, asDict(pg, pg.nodes[i]));
    
    return p_pyenum;
  }
  
  static inline PyObject *asListOfTuples(const proof_graph_t &pg) {
    PyObject *p_pyenum = PyList_New(0);
    repeat( i, pg.nodes.size() ) {
      PyObject *p_pytuple = PyTuple_New(5), *p_pylist = PyList_New(0);
      PyTuple_SetItem( p_pytuple, 0, PyString_FromString(pg.nodes[i].lit.predicate.c_str()) );
      PyTuple_SetItem( p_pytuple, 1, p_pylist );
      PyTuple_SetItem( p_pytuple, 2, PyInt_FromLong(pg.nodes[i].n));
      PyTuple_SetItem( p_pytuple, 3, PyString_FromString(pg.nodes[i].lit.extra.c_str()) );
      PyTuple_SetItem( p_pytuple, 4, PyFloat_FromDouble(pg.nodes[i].lit.wa_number));
      repeat( j, pg.nodes[i].lit.terms.size() ) PyList_Append( p_pylist, PyString_FromString(pg.nodes[i].lit.terms[j].c_str()) );
      PyList_Append( p_pyenum, p_pytuple );
    }
    return p_pyenum;
  }
  
  static inline PyObject *setLossMsg( PyObject *self, PyObject *args ) {
    PyObject *p_pycon;
    char *p_msg;
    PyArg_ParseTuple(args, "Os", &p_pycon, &p_msg);
    
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    context.loss_msg = p_msg;
    
    return Py_None;
  }

  static inline PyObject *getScore( PyObject *self, PyObject *args ) {
    PyObject *p_pycon;
    char *p_msg;
    PyArg_ParseTuple(args, "O", &p_pycon, &p_msg);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    return PyFloat_FromDouble(context.score);
  }
  
  static inline PyObject *getLiterals( PyObject *self, PyObject *args ) {
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "O", &p_pycon);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    PyObject *p_pylist = PyList_New(0);
    
    repeat( i, context.p_proof_graph->nodes.size() ) {
      if(context.p_proof_graph->nodes[i].f_removed) continue;
      PyList_Append(p_pylist, asTuple(*context.p_proof_graph, context.p_proof_graph->nodes[i]));
    }
    
    return p_pylist;
  }

  static inline PyObject *getObservedVariables(PyObject *self, PyObject *args) {
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "O", &p_pycon);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    PyObject *p_pylist = PyList_New(0);
    
    foreachc(unordered_set<string>, i, context.p_proof_graph->observed_variables)
      PyList_Append(p_pylist, PyString_FromString(i->c_str()));
    
    return p_pylist;
  }
  
  static inline PyObject *getLiteralsFromTerm( PyObject *self, PyObject *args ) {
    char *p_query;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "Os", &p_pycon, &p_query);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);
    
    PyObject *p_pylist = PyList_New(0);
    
    const vector<int> *p_t2n;
    if(context.p_proof_graph->getNode(&p_t2n, store_item_t(p_query))) {
      repeat( i, p_t2n->size() )
        PyList_Append( p_pylist, asDict(*context.p_proof_graph, context.p_proof_graph->nodes[ (*p_t2n)[i] ]) );
    }
    
    return p_pylist;
  }

  static inline PyObject *getFactorOfUnification( PyObject *self, PyObject *args ) {
    char *p_v1, *p_v2;
    PyObject *p_pycon;
    PyArg_ParseTuple(args, "Oss", &p_pycon, &p_v1, &p_v2);
    external_module_context_t &context = *(external_module_context_t*)PyCapsule_GetPointer(p_pycon, NULL);

    store_item_t t1(p_v1), t2(p_v2); if(t1>t2) swap(t1, t2);
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
    if("" == filename) return true;
    
    static PyMethodDef p_pyhenryext[] = {
      {"getLiteralsFromTerm", getLiteralsFromTerm, METH_VARARGS, "Fine.\n"},
      {"getLiterals", getLiterals, METH_VARARGS, "Really?\n"},
      {"getFactorOfUnification", getFactorOfUnification, METH_VARARGS, "But, ... I'm working in the weekend.\n"},
      {"isTimeout", isTimeout, METH_VARARGS, "Woops."},
      {"getTargetName", getTargetName, METH_VARARGS, "Wao!"},
      {"getObservedVariables", getObservedVariables, METH_VARARGS, "Who's next?"},
      {"setLossMsg", setLossMsg, METH_VARARGS, "It's me!\n"},
      {"getScore", getScore, METH_VARARGS, "Why?\n"},
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
  string                           loss_msg;
  const inference_configuration_t &ci;

  inline void setLoss(const training_data_t& td, const logical_function_t& current_y, const lp_problem_mapping_t& lprel, double score) {

    if(!g_ext.isFunctionDefined("cbGetLoss")) {
      
      /* DEFAULT LOSS FUNCTION. */
      vector<const literal_t*> cy_literals, y_literals;
      td.y_lf.getAllLiterals(&y_literals); current_y.getAllLiterals(&cy_literals);
      repeat(i, y_literals.size()) {
        bool f_found = false;
        
        repeat(j, cy_literals.size()) {
          if(*y_literals[i] == *cy_literals[j]) { f_found = true; break; }
        }
        
        if(!f_found) { this->loss = 1.0; return; }
      }
      
      this->loss = 0.0;
      return;
    }
    
    PyObject *p_pyret = NULL;
    mypyobject_t::buyTrashCan();
      
    external_module_context_t emc = {NULL, &lprel, &ci, score, ""};
    mypyobject_t pycon( PyCapsule_New( (void*)&emc, NULL, NULL) );
    p_pyret = g_ext.call("cbGetLoss", Py_BuildValue( "Oss", pycon.p_pyobj, current_y.toString().c_str(), td.y_lf.toString().c_str() ));
      
    this->loss = PyFloat_AsDouble(p_pyret);
    this->loss_msg = emc.loss_msg;

    Py_DECREF( p_pyret );
      
    mypyobject_t::cleanTrashCan();
  
  }

  inline loss_t(const inference_configuration_t &_ci): ci(_ci), loss(0), maximum_loss(0), minimum_loss(0) {};
  
};

struct lp_inference_cache_t {
  const knowledge_base_t          &kb;
  const inference_configuration_t &ci;
  int                              num_variable_clusters;
  proof_graph_t                    pg;
  linear_programming_problem_t     lp;
  lp_problem_mapping_t             lprel;
  loss_t                           loss;
  double                           elapsed_prepare, elapsed_ilp;
  int                              cpi_iteration;
  unordered_set<store_item_t>      logical_atomic_terms;
  unordered_set<string>            user_defined_features;
  unordered_set<size_t>            tc_produced;
  unordered_set<size_t>            mx_produced;

  inline lp_inference_cache_t(const lp_inference_cache_t &_ic) :
    kb(_ic.kb), ci(_ic.ci), num_variable_clusters(_ic.num_variable_clusters),
    pg(_ic.pg), lp(_ic.lp), lprel(_ic.lprel), loss(_ic.loss),
    elapsed_prepare(_ic.elapsed_prepare), elapsed_ilp(_ic.elapsed_ilp),
    cpi_iteration(_ic.cpi_iteration) {};
  inline lp_inference_cache_t(const inference_configuration_t &_ci, const knowledge_base_t &_kb) : loss(ci), ci(_ci), kb(_kb) {};

  int createNodeVar(int n, bool f_brand_new = true);
  int createConjVar(int hn);
  int createTransitivityConstraint(const store_item_t &ti, const store_item_t &tj, const store_item_t &tk);
  int createConsistencyConstraint(int n1, int n2, const unifier_t &theta);
  
  void fixGoldClustering();
  
  inline void printStatistics(const lp_solution_t& lpsol, ostream *p_out = g_p_out) const {
    (*p_out) << "<statistics>" << endl
             << "<time total=\""<< (elapsed_prepare+elapsed_ilp) <<"\" prepare=\"" << elapsed_prepare << "\" ilp=\"" << elapsed_ilp << "\" />"<< endl
             << "<ilp solution=\""<< toString(lpsol.sol_type) <<"\" variables=\"" << lp.variables.size() << "\" constraints=\"" << lp.constraints.size() << "\" />"<< endl
             << "<search-space literals=\""<< pg.nodes.size() <<"\" axiom=\""<< pg.used_axiom_types.size() <<"\" />"<< endl
             << "</statistics>" << endl;
  }
  
  inline void printStatistics(ostream *p_out = g_p_out) const {
    (*p_out) << "<statistics>" << endl
             << "<time total=\""<< (elapsed_prepare+elapsed_ilp) <<"\" prepare=\"" << elapsed_prepare << "\" ilp=\"" << elapsed_ilp << "\" />"<< endl
             << "<ilp solution=\""<< toString(NotAvailable) <<"\" variables=\"" << lp.variables.size() << "\" constraints=\"" << lp.constraints.size() << "\" />"<< endl
             << "<search-space literals=\""<< pg.nodes.size() <<"\" axiom=\""<< pg.used_axiom_types.size() <<"\" />"<< endl
             << "</statistics>" << endl;
  }
  
};

/* Algorithms. */
namespace algorithm {
  inference_result_type_t infer(vector<explanation_t> *p_out_expls, lp_inference_cache_t *p_out_cache, lp_inference_cache_t *p_old_cache, inference_configuration_t& c, const logical_function_t &obs, const knowledge_base_t& kb, ostream *p_out = g_p_out );
  void learn( score_function_t *p_out_sfunc, const learn_configuration_t &c, vector<training_data_t>& t, const knowledge_base_t& kb );
  void kbestMIRA(sparse_vector_t *p_out_new, sparse_vector_t *p_out_diff, unordered_set<store_item_t> *p_out_fi, const sparse_vector_t &fv_current, const vector<pair<sparse_vector_t*, double> > &fv_wrong_best, const learn_configuration_t &c, double normer_gold, double normer_wrong);
}

/* Functions. */
namespace function {
  void initializeWeight(sparse_vector_t *p_w, const string &name, const inference_configuration_t &ic);
    
  bool instantiateBackwardChainings( proof_graph_t *p_out_gp, int n_current_pg_size, int n_obs, const knowledge_base_t &kb, const unordered_set<int> &prominent_axioms, const inference_configuration_t &c, int *p_num_filtered_out );
  bool enumeratePotentialElementalHypotheses(proof_graph_t *p_out_gp, const logical_function_t &obs, const knowledge_base_t &kb, const inference_configuration_t &c);
  
  bool convertToFeatureVector( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &gp, inference_configuration_t &c );
  bool convertToLP( linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &gp, inference_configuration_t &c );  
  bool augmentTheLoss(linear_programming_problem_t *p_out_lp, lp_problem_mapping_t *p_out_lprel, lp_inference_cache_t *p_out_cache, const knowledge_base_t &kb, const proof_graph_t &gp, inference_configuration_t &c);
  ilp_solution_type_t solveLP_BnB( vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache = NULL );
  ilp_solution_type_t solveLP_LS( vector<lp_solution_t> *p_out_sols, const linear_programming_problem_t &lp, const lp_problem_mapping_t &lprel, const inference_configuration_t &c, lp_inference_cache_t *p_out_cache = NULL );
  void roundUpLP( linear_programming_problem_t *p_out_lp );
  void convertLPToHypothesis(logical_function_t *p_out_h, logical_function_t *p_out_obs, sparse_vector_t *p_out_fv, const lp_solution_t &sol, const lp_inference_cache_t &cache);
  
  void sample( vector<double> *p_out_array, const sampling_method_t m );

  void getParsedOption( command_option_t *p_out_opt, vector<string> *p_out_args, const string &acceptable, int argc, char **argv );

  inline bool isSexpSep( char c ) { return '(' == c || ')' == c || '"' == c || ' ' == c || '\t' == c || '\n' == c || '\r' == c; };

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
        if(literals[i]->terms[j].isConstant()) p_out_cons->insert(store_item_t(literals[i]->terms[j]));
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

  inline void addVector( sparse_vector_t *p_out, const sparse_vector_t &sv ) {
    for( sparse_vector_t::const_iterator iter_sv = sv.begin(); sv.end() != iter_sv; ++iter_sv )
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

  inline void getVectorIndices(unordered_set<store_item_t> *p_out_indices, const sparse_vector_t &s ) {
    for( sparse_vector_t::const_iterator iter_f = s.begin(); s.end() != iter_f; ++iter_f )
      p_out_indices->insert(iter_f->first);
  }

  inline bool doesMGUimply(const unifier_t &uni, store_item_t &x, store_item_t &y) {
    for(int i=0; i<uni.substitutions.size(); i++) {
      if((uni.substitutions[i].terms[0] == x && uni.substitutions[i].terms[1] == y) ||
         (uni.substitutions[i].terms[0] == y && uni.substitutions[i].terms[1] == x)) return true;
    }
    return false;
  }
  
  inline bool getMGU( unifier_t *p_out_u, const literal_t &p1, const literal_t &p2, bool f_skip = false, bool f_check_only = false ) {
    if(p1.predicate != p2.predicate) return false;
    if(p1.terms.size() != p2.terms.size()) return false;
    for(int i=0; i<p1.terms.size(); i++) {
      if(p1.terms[i] == p2.terms[i]) { p_out_u->add(p1.terms[i], p2.terms[i]); continue; }
      if(p1.terms[i].isConstant() && p2.terms[i].isConstant()) return false;
      if(f_skip) {
        if(p1.terms[i].isConstant() && !p2.terms[i].isConstant()) return false;
        if('!' != ((const string&)(p1.terms[i]))[0]) continue;
      }
      if(!f_check_only) 
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

  inline size_t getFileSize(const string &filename) {
    struct stat filestatus;
    stat(filename.c_str(), &filestatus);
    return filestatus.st_size;
  }

  
  inline size_t getFileSize(istream &ifs) {
    size_t file_size = (size_t)ifs.seekg(0, std::ios::end).tellg();
    ifs.seekg(0, std::ios::beg);
    return file_size;
  }
  
};



