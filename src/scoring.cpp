
#include "defs.h"

#include <fstream>

#define _SS(x) g_store.claim(x)

/* */
void score_function_t::featureFunctionLiteral( sparse_vector_t *p_out_v, const proof_graph_t &pg, int i ) {

  /* Traverse the path, and multiply the weights. */
  double cost = 1.0;
  int p = i;

  while( -1 != p ) {
    cost *= pg.nodes[p].lit.wa_number;
    p     = pg.nodes[p].parent_node;
  }

  (*p_out_v)[ "OBS" + g_store.claim(pg.nodes[i].lit.predicate) ] = cost;
  //(*p_out_v)[ "OBS" + g_store.claim(pg.nodes[i].lit.predicate) ] = pg.nodes[i].lit.wa_number;
  
}

void score_function_t::featureFunctionAxiom( sparse_vector_t *p_out_v, const proof_graph_t &pg, int i, pg_hypernode_t j ) {

  // for( int k=0; k<pg.hypernodes[j].size(); k++ ) {
  //   (*p_out_v)[ pg.getEdgeName( i, j ) + _SS(pg.nodes[ pg.hypernodes[j][k] ].lit.predicate) ] = 1;
  // }
  
  // for( uint_t k=0; k<pg.hypernodes[j].size(); k++ ) {
  //   (*p_out_v)[ "AX_" + toString(pg.nodes[i].depth, "%d") + pg.getEdgeName( i, j ) + _SS(pg.nodes[ pg.hypernodes[j][k] ].lit.predicate) ] = 1;
  // }
  
  //(*p_out_v)[ "AX_" + toString(pg.nodes[i].depth, "%d") + pg.getEdgeName( i, j ) ] = 1;
  //(*p_out_v)[ "AX_" ] = 1;
  
  //(*p_out_v)[ "AX_" + toString(pg.nodes[i].depth, "%d") + pg.getEdgeName( i, j ) ] = 0.1;
  
}

bool score_function_t::featureFunctionUnify( sparse_vector_t *p_out_v, const proof_graph_t &pg, const knowledge_base_t &kb, int i, int j, int p_t1, int p_t2 ) {

  const literal_t &l_i = pg.nodes[i].lit, &l_j = pg.nodes[j].lit;
  
  if( p_t1 != p_t2 ) return false;

  if( l_i.toPredicateArity() == l_j.toPredicateArity() ) {
    //(*p_out_v)[ toString(pg.nodes[i].depth, "%d") + "UNIFY_" + toString(p_t1, "%d") + g_store.claim( pg.nodes[i].lit.predicate )] = 1;
    (*p_out_v)[ toString(pg.nodes[i].depth, "%d") + "UNIFY_" + toString(p_t1, "%d") + g_store.claim( pg.nodes[i].lit.predicate )] = -1; //max(pg.nodes[i].wa_weight, pg.nodes[j].wa_weight);
    return true;
  }

  if( 1 == l_i.terms.size() && 1 == l_j.terms.size() ) {
    static unordered_set<string> disjoint_set;
    static bool f_disjoint_loaded = false;

    if( !f_disjoint_loaded ) {
      f_disjoint_loaded = true;
      ifstream ifs_disj( "/home/naoya-i/work/unkconf2012/plan-disj.tsv" );
      string   pa1, pa2;
      while( !ifs_disj.eof() ) {
        ifs_disj >> pa1 >> pa2;
        if( pa1 > pa2 ) swap( pa1, pa2 );
        disjoint_set.insert( pa1+pa2 );
      }
      ifs_disj.close();
    }

    string pa1 = l_i.toPredicateArity(), pa2 = l_j.toPredicateArity();
    if( pa1 > pa2 ) swap( pa1, pa2 );
  
    if( disjoint_set.end() != disjoint_set.find( pa1+pa2 ) ) {
      (*p_out_v)[ "INF" ] = -99999;
      //(*p_out_v)[ "UNIFY_DISJ_" + g_store.claim( pg.nodes[i].lit.predicate ) + g_store.claim( pg.nodes[j].lit.predicate ) ] = -100;
      return true;
    }
  }
  
  return false;
  
  /* YAKKETSUKE */
  typedef unordered_map<string, unordered_set<string> > synset_mapping_t;
  
  static bool f_loaded = false;
  static synset_mapping_t synset_mapping, synset_rels;

  if( !f_loaded ) {
    f_loaded = true;
    
    ifstream ifs_sm( "/home/naoya-i/work/unkconf2012/wn-synset-mapping.tsv" ), ifs_sr( "/home/naoya-i/work/unkconf2012/wn-eish.tsv" );
    string line;
        
    while( getline( ifs_sm, line ) )
      synset_mapping[ line.substr( 0, line.find( "\t" ) ) ].insert( line.substr( line.find( "\t" )+1 ) );
    
    while( getline( ifs_sr, line ) )
      synset_rels[ line.substr( 0, line.find( "\t" ) ) ].insert( line.substr( line.find( "\t" )+1 ) );

    ifs_sm.close();
    ifs_sr.close();
  }

  bool f_rel_found = false;
  
  foreach( unordered_set<string>, iter_si, synset_mapping[ g_store.claim(pg.nodes[i].lit.predicate) ] ) {
    foreach( unordered_set<string>, iter_sj, synset_mapping[ g_store.claim(pg.nodes[j].lit.predicate) ] ) {
      string sj = *iter_sj, si = *iter_si;
      if( atoi(sj.c_str()) < atoi(si.c_str()) ) { string st = sj; sj = si; si = st; }

         foreach( unordered_set<string>, iter_rel, synset_rels[ si+sj ] ) {
        (*p_out_v)[ "UNIFY" + *iter_rel ] = -1;
        f_rel_found = true;
      }
      
    }
  }

  if( has_intersection( synset_mapping[ g_store.claim(pg.nodes[i].lit.predicate) ].begin(), synset_mapping[ g_store.claim(pg.nodes[i].lit.predicate) ].end(),
                        synset_mapping[ g_store.claim(pg.nodes[j].lit.predicate) ].begin(), synset_mapping[ g_store.claim(pg.nodes[j].lit.predicate) ].end() ) ) {
    (*p_out_v)[ "UNIFY_SAME_SYNSET" ] = -1;
    f_rel_found = true;
  }
  
  //(*p_out_v)[ "UNIFY_" + g_store.claim(pg.nodes[i].lit.predicate) + toString( pg.nodes[i].depth, "%d" ) + toString(pg.nodes[j].depth, "%d") ] = 1;
  //(*p_out_v)[ "UNIFY_" ] = -1;
  //(*p_out_v)[ "UNIFY_" ] = 1;

  return f_rel_found;
  
}

// void score_function_t::featureFunctionUnifyVariables( sparse_vector_t *p_out_v, const proof_graph_t &pg, store_item_t t1, store_item_t t2 ) {

//   (*p_out_v)[ "UV_" ] = 1;
//   return;
  
//   // (*p_out_v)[ "UV_" ] = 0.1;
  
//   // return;
  
//   const vector<int> *p_literals1, *p_literals2;
  
//   pg.getNode( &p_literals1, t1 );
//   pg.getNode( &p_literals2, t2 );

//   for( uint_t i=0; i<p_literals1->size(); i++ ) {
//     for( uint_t j=0; j<p_literals2->size(); j++ ) {
//       //if( ObservableNode != pg.nodes[ (*p_literals1)[i] ].type && ObservableNode != pg.nodes[ (*p_literals2)[j] ].type ) continue;
//       if( g_store.claim(pg.nodes[ (*p_literals1)[i] ].lit.predicate) != g_store.claim(pg.nodes[ (*p_literals2)[j] ].lit.predicate) ) continue;

//       /* Where is it? */
//       int pos_t1, pos_t2;
      
//       repeat( k, pg.nodes[ (*p_literals1)[i] ].lit.terms.size() )
//         if( pg.nodes[ (*p_literals1)[i] ].lit.terms[k] == t1 ) pos_t1 = k;
      
//       repeat( k, pg.nodes[ (*p_literals2)[j] ].lit.terms.size() )
//         if( pg.nodes[ (*p_literals2)[j] ].lit.terms[k] == t2 ) pos_t2 = k;

//       (*p_out_v)[ "UV_" + g_store.claim(pg.nodes[ (*p_literals1)[i] ].lit.predicate) + toString(pos_t1, "%d") +
//                   g_store.claim(pg.nodes[ (*p_literals2)[j] ].lit.predicate) + toString(pos_t2, "%d") ] = 1;
//     } }
  
//   // for( int i=0; i<p_literals1->size(); i++ ) {
//   //   if( ObservableNode == pg.nodes[ (*p_literals1)[i] ].type )
//   //     (*p_out_v)[ "UV_" + g_store.claim(pg.nodes[ (*p_literals1)[i] ].lit.predicate) ] = 1;
//   // }
  
//   // for( int j=0; j<p_literals2->size(); j++ ) {
//   //   if( ObservableNode == pg.nodes[ (*p_literals2)[j] ].type )
//   //     (*p_out_v)[ "UV_" + g_store.claim(pg.nodes[ (*p_literals2)[j] ].lit.predicate) ] = 1;
//   // }
  
// }
