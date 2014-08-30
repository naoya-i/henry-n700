
#include "defs.h"

bool knowledge_base_t::copy(knowledge_base_t *p_dest) const {
  /* DUMP THE CURRENT DATABASE. */
  sqlite3_stmt *p_stmt   = NULL;
  char         *p_axiom  = NULL, *p_rhs = NULL, *p_rhs_ot = NULL, *p_id = NULL;
  uint_t        num_cols = 0;

  if(SQLITE_OK != sqlite3_prepare_v2(p_db, "SELECT id, axiom, rhs, rhs_others FROM kb", -1, &p_stmt, 0)) {
    E("SQL dump failed."); return false;
  }

  p_dest->beginTransaction();

  if(0 < (num_cols = sqlite3_column_count(p_stmt))) {
    while(SQLITE_ROW == sqlite3_step(p_stmt)) {
      if(NULL != (p_id = (char *)sqlite3_column_text(p_stmt, 0)) &&
          NULL != (p_axiom = (char *)sqlite3_column_text(p_stmt, 1)) &&
         NULL != (p_rhs = (char *)sqlite3_column_text(p_stmt, 2)) &&
         NULL != (p_rhs_ot = (char *)sqlite3_column_text(p_stmt, 3)) )
        if(SQLITE_OK != sqlite3_exec(p_dest->p_db, ::toString("INSERT INTO kb VALUES(%d, '%s', '%s', '%s')", p_id, p_axiom, p_rhs, p_rhs_ot).c_str(), NULL, 0, NULL)) {
          E("SQL copy failed."); return false;
        }
    }
  }

  p_dest->commit();

  sqlite3_finalize(p_stmt);

  return true;
}

bool knowledge_base_t::setContextDatabase(const string &fn) {
  context_pruning_cdb = ::open(fn.c_str(), O_RDONLY);

  FILE *fpt = fopen((fn+".bin").c_str(), "rb");

  while(!feof(fpt)) {
    size_t num_docs;
    unordered_set<int> docs;
    fread(&num_docs, sizeof(size_t), 1, fpt);

    int *p_docs = new int[num_docs];
    fread(p_docs, sizeof(int), num_docs, fpt);
    docs.insert(p_docs, p_docs+num_docs);
    word_docs.push_back(docs);

    delete[] p_docs;
  }

  fclose(fpt);
  return true;
}

int knowledge_base_t::getContextVectorIndex(const string &w) const {
  if(-1 == context_pruning_cdb) return -1;

  cdbi_t vlen;
  double f_w1, f_w2;

  if (cdb_seek(context_pruning_cdb, w.c_str(), w.length(), &vlen) <= 0) return -1;

  /* RETRIEVE THE VALUE. */
  char *p_val = new char[1+vlen];
  int   ret;
  cdb_bread(context_pruning_cdb, p_val, vlen);

  ret = atoi(p_val);

  delete[] p_val;

  return ret;
}

double knowledge_base_t::calcContextualSimilarity(const string &w1, const string &w2) const {
  if(-1 == context_pruning_cdb) return 0.0;

  int    v1_freq = 0, v2_freq = 0, joint_freq = 0;
  double t = getTimeofDaySec();
  int    i1, i2;
  static unordered_map<string, double> cache_dice;
  string cdk = w1 < w2 ? w1+w2 : w2+w1;

  if(0 < cache_dice.count(cdk)) return cache_dice[cdk];

#pragma omp critical
  {
    static unordered_map<string, int> cache;


    if(0 < cache.count(w1)) i1 = cache[w1];
    else {
      i1 = getContextVectorIndex(w1);
      cache[w1] = i1;
    }

    if(0 < cache.count(w2)) i2 = cache[w2];
    else {
      i2 = getContextVectorIndex(w2);
      cache[w2] = i2;
    }
  }

  if(-1 == i1 || -1 == i2) return 0.0;

  v1_freq = word_docs[i1].size();
  v2_freq = word_docs[i2].size();

  if(0 == v1_freq || 0 == v2_freq) return 0.0;

  if(v1_freq < v2_freq) {
    for(unordered_set<int>::const_iterator i=word_docs[i1].begin(); word_docs[i1].end()!=i; ++i) {
      if(0 < word_docs[i2].count(*i)) joint_freq++;
    }
  } else {
    for(unordered_set<int>::const_iterator i=word_docs[i2].begin(); word_docs[i2].end()!=i; ++i) {
      if(0 < word_docs[i1].count(*i)) joint_freq++;
    }
  }

  cache_dice[cdk] = 2.0 * joint_freq / (v1_freq + v2_freq);

  V(6) cerr << "ELP:" << w1 << " " << w2 << (getTimeofDaySec() - t) << endl;

  return 2.0 * joint_freq / (v1_freq + v2_freq);
}

bool knowledge_base_t::open(bool _f_writable, const string &_filename) {
  if(NULL != p_ins_stmt) { sqlite3_finalize(p_ins_stmt); p_ins_stmt = NULL; }
  if(NULL != p_db) { sqlite3_close(p_db); p_db = NULL; }

  bool f_open_success = true;

  /* IN-MEMORY DB MUST BE WRITABLE. */
  if(":memory:" == _filename) _f_writable = true;

  if(SQLITE_OK != sqlite3_open_v2(_filename.c_str(), &p_db, _f_writable ? (SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE) : SQLITE_OPEN_READONLY, NULL)) {
    f_open_success = false;
    E( "Database error: open() failed." );
  }

  if(_f_writable) {
    newTable();

    if(SQLITE_OK != sqlite3_prepare_v2(p_db, "INSERT INTO kb VALUES (?, ?, ?, ?)", -1, &p_ins_stmt, 0 ) )
      E("Database error: prepare_v2() failed.");
  }

  f_writable = _f_writable;
  filename   = _filename;

  V(5) cerr << TS() << "Database " << (f_open_success ? "opened." : "failed to open.") << endl;

  return f_open_success;
}

void knowledge_base_t::newTable() {
  if(NULL != p_ins_stmt) sqlite3_finalize(p_ins_stmt);

  sqlite3_exec(p_db, "DROP TABLE kb", NULL, 0, NULL);
  sqlite3_exec(p_db, "CREATE TABLE kb(id INTEGER, axiom TEXT, rhs TEXT, rhs_others TEXT)", NULL, 0, NULL);
  sqlite3_exec(p_db, "CREATE INDEX rhsindex on kb(rhs)", NULL, 0, NULL);
  sqlite3_exec(p_db, "CREATE TABLE bcmatrix(rhs TEXT, lhs TEXT, axiom TEXT)", NULL, 0, NULL);
  sqlite3_exec(p_db, "CREATE INDEX bcm_index on bcmatrix(rhs)", NULL, 0, NULL);

  if(SQLITE_OK != sqlite3_prepare_v2(p_db, "INSERT INTO kb VALUES (?, ?, ?, ?)", -1, &p_ins_stmt, 0 ) )
    E("Database error: prepare_v2() failed.");
}

void knowledge_base_t::beginTransaction() {
  if(f_in_transaction) return;
  sqlite3_exec( p_db, "BEGIN TRANSACTION", NULL, 0, NULL );
  f_in_transaction = true;
}

void knowledge_base_t::commit() {
  if(!f_in_transaction) return;
  sqlite3_exec( p_db, "COMMIT", NULL, 0, NULL );
  f_in_transaction = false;
}

void knowledge_base_t::vacuum() {
  sqlite3_exec( p_db, "VACUUM", NULL, 0, NULL );
}

bool knowledge_base_t::getAbductiveHypotheses(unordered_map<string, unordered_set<int> > *p_out, const string &key_pa) const {
  sqlite3_stmt      *p_stmt    = NULL;
  char              *p_val_lhs = NULL, *p_val_axiom = NULL;
  uint_t             num_cols  = 0;
  uint_t             num_retrieved = 0;

  if(SQLITE_OK != sqlite3_prepare_v2(p_db, ::toString("SELECT lhs, axiom FROM bcmatrix WHERE rhs=\"%s\"", key_pa.c_str()).c_str(), -1, &p_stmt, 0)) {
    E("SQL search query failed."); return false;
  }

  if(0 < (num_cols = sqlite3_column_count(p_stmt))) {
    while(SQLITE_ROW == sqlite3_step(p_stmt)) {
      if(NULL != (p_val_lhs = (char *)sqlite3_column_text(p_stmt, 0)) &&
         NULL != (p_val_axiom = (char *)sqlite3_column_text(p_stmt, 1)) ) {
        num_retrieved++;
        //if(400 == num_retrieved) break;

        char *pch = strtok(p_val_axiom, " ");
        while(NULL != pch) {
          (*p_out)[p_val_lhs].insert(atoi(pch));
          pch = strtok(NULL, " ");
        }
      }
    }
  }

  sqlite3_finalize(p_stmt);

  return true;
}

void knowledge_base_t::pruneAxioms(unordered_map<string, unordered_set<int> > *p_out_axiom_set, const vector<const literal_t*> &literals_obs) const {
  if(-1 == context_pruning_cdb) return;

  unordered_map<string, double> axiom_score;
  unordered_map<int, int>    axiom_score_numsum;
  vector<pair<string, double> > ranked_axioms;

  for(unordered_map<string, unordered_set<int> >::const_iterator j=p_out_axiom_set->begin(); p_out_axiom_set->end()!=j; ++j) {
    double local_score = 0.0;

    repeat(k, literals_obs.size()) {
      local_score += calcContextualSimilarity(function::getWord(j->first), function::getWord(literals_obs[k]->predicate));
    }

    ranked_axioms.push_back(make_pair(j->first, local_score / (double)literals_obs.size()));
  }

  /* PRUNE! */
  struct {
    static bool comparator(const pair<string, double> &i, const pair<string, double> &j) { return (i.second > j.second);}
  } mysorter;

  sort(ranked_axioms.begin(), ranked_axioms.end(), mysorter.comparator );

  unordered_map<string, unordered_set<int> > new_axiom_set;

  repeat(j, ranked_axioms.size()) {
    V(5) cerr << j << ". " << ranked_axioms[j].first << ":" << ranked_axioms[j].second << endl;
    if(j < num_branches) {
      V(4) cerr << ranked_axioms[j].first << ": ACCEPTED." << endl;
      new_axiom_set[ranked_axioms[j].first] = (*p_out_axiom_set)[ranked_axioms[j].first];
    }
  }

  *p_out_axiom_set = new_axiom_set;
}

bool knowledge_base_t::writeBcMatrix() {
  sqlite3_stmt *p_ins_stmt   = NULL;

  if(SQLITE_OK != sqlite3_prepare_v2(p_db, "INSERT INTO bcmatrix VALUES (?, ?, ?)", -1, &p_ins_stmt, 0 ) ) {
    E("Database error: prepare_v2() failed."); return false;
  }

  for(unordered_map<string, unordered_map<string, unordered_set<int> > >::iterator i = bc_matrix.begin(); bc_matrix.end() != i; ++i) {
    for(unordered_map<string, unordered_set<int> >::iterator j = i->second.begin(); i->second.end() != j; ++j) {
      string s3 = ::join(j->second.begin(), j->second.end(), "%d", " ");

      sqlite3_reset(p_ins_stmt);
      sqlite3_bind_text(p_ins_stmt, 1, i->first.c_str(), i->first.length(), SQLITE_STATIC);
      sqlite3_bind_text(p_ins_stmt, 2, j->first.c_str(), j->first.length(), SQLITE_STATIC);
      sqlite3_bind_text(p_ins_stmt, 3, s3.c_str(), s3.length(), SQLITE_STATIC);

      if( SQLITE_DONE != sqlite3_step(p_ins_stmt) )
        E( "Database error: insert() failed." );

    }
  }

  bc_matrix.clear();
}

bool knowledge_base_t::registerIncAxiom(const sexp_stack_t &srline, const sexp_stack_t &sr) {
  mxpairs.push_back(make_pair(literal_t(*sr.children[1]), literal_t(*sr.children[2])));
  return registerAxiom(srline, sr, 1) && registerAxiom(srline, sr, 2);
}

bool knowledge_base_t::registerAxiom(const sexp_stack_t &srline, const sexp_stack_t &sr, int _n) {
  string key_pa, rhs_ot, str_sr = srline.toString();

  vector<string> str_rhs;

  if(StringStack == sr.children[_n]->children[0]->type)
    str_rhs.push_back(sr.children[_n]->children[0]->toString() + "/0");
  else if(sr.children[_n]->isFunctor(AndString)) {
    if(StringStack == sr.children[_n]->children[1]->type)
      str_rhs.push_back(sr.children[_n]->children[1]->toString() + "/0");
    else {
      repeatf(i, 1, sr.children[_n]->children.size()) {
        key_pa = ::toString("%s/%d", sr.children[_n]->children[i]->children[0]->toString().c_str(), sr.children[_n]->children[i]->children.size()-1);

        /* FOR CONSTANTS. */
        string o_key_pa = key_pa;

        if(isSearchWithConstant(key_pa)) {
          repeatf(j, 1, sr.children[_n]->children[i]->children.size()) {
            if("event/4" == o_key_pa && 2 != j) continue;

            string var = sr.children[_n]->children[i]->children[j]->toString();
            if(store_item_t(var).isConstant()) key_pa += "/" + var;
          }
        }

        str_rhs.push_back(key_pa);
      }
    }
  } else {
    key_pa = ::toString("%s/%d", sr.children[_n]->children[0]->children[0]->toString().c_str(), sr.children[_n]->children.size()-1);

    /* FOR CONSTANTS. */
    string o_key_pa = key_pa;

    if(isSearchWithConstant(key_pa)) {
      repeatf(j, 1, sr.children[_n]->children.size()) {
        if("event/4" == o_key_pa && 2 != j) continue;

        string var = sr.children[_n]->children[j]->toString();
        if(store_item_t(var).isConstant()) key_pa += "/" + var;
      }
    }

    str_rhs.push_back(key_pa);
  }

  //cerr << "RHS" << join(str_rhs.begin(), str_rhs.end()) << endl;

  int id = num_axioms++;
  string id_str = ::toString("%d", id);

  repeat(i, str_rhs.size()) {
    key_pa = str_rhs[i];
    rhs_ot = str_rhs[i+1 == str_rhs.size() ? 0 : i+1];

    /* INSERT INTO kb VALUES ('(B %s)', '%s') */
    sqlite3_reset(p_ins_stmt);
    sqlite3_bind_text(p_ins_stmt, 1, id_str.c_str(), id_str.length(), SQLITE_STATIC);
    sqlite3_bind_text(p_ins_stmt, 2, str_sr.c_str(), str_sr.length(), SQLITE_STATIC);
    sqlite3_bind_text(p_ins_stmt, 3, key_pa.c_str(), key_pa.length(), SQLITE_STATIC);
    sqlite3_bind_text(p_ins_stmt, 4, rhs_ot.c_str(), rhs_ot.length(), SQLITE_STATIC);

    if( SQLITE_DONE != sqlite3_step(p_ins_stmt) ) {
      E( "Database error: insert() failed." );
      return false;
    }
  }

  /* MAKE BACKCHAIN MATRIX. */
  vector<string> str_lhs;

  if(StringStack == sr.children[1]->children[0]->type) /* PROPOSITIONAL */
    str_lhs.push_back(sr.children[1]->children[0]->toString());
  else if(sr.children[1]->isFunctor(AndString)) { /* AND */
    for(int i=1; i<sr.children[1]->children.size(); i++) {
      if(StringStack == sr.children[_n]->children[1]->type)
        str_lhs.push_back(sr.children[1]->children[i]->toString()); /* PROPOSITIONAL */
      else /* FIRST-ORDER */
        str_lhs.push_back(::toString("%s/%d", sr.children[1]->children[i]->children[0]->toString().c_str(), sr.children[1]->children[i]->children.size()-2));
    }
  } else /* FIRST-ORDER */
    str_lhs.push_back(::toString("%s/%d", sr.children[1]->children[0]->children[0]->toString().c_str(), sr.children[1]->children[0]->children.size()-2));

  key_pa = str_rhs[0];
  
  for(int i=0; i<str_lhs.size(); i++) {
    bc_matrix[key_pa][str_lhs[i]].insert(id);
    //bc_matrix[str_lhs[i]].insert(::toString("%d:%s", id, key_pa.c_str()));
  }

  return true;
}

bool knowledge_base_t::search(vector<axiom_t> *p_out_axioms, const string &key_pa, const unordered_set<int> &prominent_axioms,
    int *p_out_filtered_out, bool f_pruning) const {
  sqlite3_stmt      *p_stmt   = NULL;
  char              *p_val    = NULL, *p_id = NULL, *p_rhs_ot = NULL;
  uint_t             num_cols = 0;

  if(SQLITE_OK != sqlite3_prepare_v2(p_db, ::toString("SELECT axiom, id, rhs_others FROM kb WHERE rhs=\"%s\"", key_pa.c_str()).c_str(), -1, &p_stmt, 0)) {
    E("SQL search query failed."); return false;
  }

  if(0 < (num_cols = sqlite3_column_count(p_stmt))) {
    while(SQLITE_ROW == sqlite3_step(p_stmt)) {
      if( NULL != (p_val = (char *)sqlite3_column_text(p_stmt, 0)) &&
          NULL != (p_id  = (char *)sqlite3_column_text(p_stmt, 1)) &&
          NULL != (p_rhs_ot  = (char *)sqlite3_column_text(p_stmt, 2)) ) {

        if(f_pruning) {
          if(0 == prominent_axioms.count(atoi(p_id))) {
            if(NULL != p_out_filtered_out) (*p_out_filtered_out)++; continue;
          }
        }

        p_out_axioms->push_back(axiom_t(p_val, p_rhs_ot));
      }
    }
  }

  sqlite3_finalize(p_stmt);

  return p_out_axioms->size()>0;
}
