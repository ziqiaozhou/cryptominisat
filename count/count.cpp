#include "count.h"
#include "src/dimacsparser.h"
#include <boost/lexical_cast.hpp>
#include <ctime>
#include <iostream>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_map>
using boost::lexical_cast;
using std::cout;
using std::exit;
using std::map;
using std::ofstream;
using std::unordered_map;
using std::unordered_set;
void Count::readInAFileToCache(SATSolver *solver2, const string &filename) {
  vector<vector<Lit>> trans_clauses;
  vector<std::pair<vector<unsigned>, bool>> trans_xor_clauses;
  trans_xor_clauses.clear();
  trans_clauses.clear();
  if (conf.verbosity) {
    cout << "c Reading file '" << filename << "'" << endl;
  }
#ifndef USE_ZLIB
  FILE *in = fopen(filename.c_str(), "rb");
  DimacsParser<StreamBuffer<FILE *, FN>> parser(
      solver2, &debugLib, conf.verbosity, &trans_clauses, &trans_xor_clauses);
#else
  gzFile in = gzopen(filename.c_str(), "rb");

  DimacsParser<StreamBuffer<gzFile, GZ>> parser(
      solver2, &debugLib, conf.verbosity, &trans_clauses, &trans_xor_clauses);
#endif

  if (in == NULL) {
    std::cerr << "ERROR! Could not open file '" << filename
              << "' for reading: " << strerror(errno) << endl;

    std::exit(1);
  }

  bool strict_header = conf.preprocess;
  if (!parser.parse_DIMACS(in, strict_header)) {
    exit(-1);
  }

  if (!sampling_vars_str.empty() && !parser.sampling_vars.empty()) {
    std::cerr << "ERROR! Independent vars set in console but also in CNF."
              << endl;
    exit(-1);
  }

  if (!sampling_vars_str.empty()) {
    assert(sampling_vars.empty());
    std::stringstream ss(sampling_vars_str);
    uint32_t i;
    while (ss >> i) {
      const uint32_t var = i - 1;
      sampling_vars.push_back(var);

      if (ss.peek() == ',' || ss.peek() == ' ')
        ss.ignore();
    }
  } else {
    sampling_vars.insert(sampling_vars.end(), parser.sampling_vars.begin(),
                         parser.sampling_vars.end());
  }
  symbol_vars.insert(parser.symbol_vars.begin(), parser.symbol_vars.end());
  if (conf.keep_symbol) {
    for (auto one_symbol_vars : symbol_vars) {
      for (auto lit : one_symbol_vars.second)
        sampling_vars.push_back(lit.var());
    }
  }
  jaccard_vars.swap(parser.jaccard_vars);
  jaccard_vars2.swap(parser.jaccard_vars2);
  ob_vars.swap(parser.ob_vars);
  attack_vars.swap(parser.attack_vars);
  if (sampling_vars.empty()) {
    if (only_sampling_solution) {
      std::cout << "ERROR: only independent vars are requested in the "
                   "solution, but no independent vars have been set!"
                << endl;
      exit(-1);
    }
  } else {
    solver2->set_sampling_vars(&sampling_vars);
  }
  solver2->set_symbol_vars(&symbol_vars);

  call_after_parse();

#ifndef USE_ZLIB
  fclose(in);
#else
  gzclose(in);
#endif
  cout << "parse finish and close\n";
  cout << "parse trans_clauses" << trans_clauses.size() << std::endl;
  for (auto cl : trans_clauses) {
    for (auto lit : cl) {
      used_vars.insert(lit.var());
    }
  }
  for (auto cl : trans_xor_clauses) {
    for (auto var : cl.first) {
      used_vars.insert(var);
    }
  }
}
bool shuffle(vector<bool> &secret_rhs) {
  if (secret_rhs.size() == 0)
    return false;
  vector<bool> old_secret_rhs = secret_rhs;
  bool success = false;
  while (!success) {
    for (int i = 0; i < secret_rhs.size(); ++i) {
      secret_rhs[i] = (rand() % 2) ? true : false;
      if (secret_rhs[i] != old_secret_rhs[i]) {
        cout << "secret_rhs[i]=" << secret_rhs[i]
             << ",old_secret_rhs[i]=" << old_secret_rhs[i] << std::endl;
        success = true;
      }
    }
  }
  return true;
}
vector<string> Count::getCIISSModel(SATSolver *solver) {
  string ret = "";
  std::stringstream ret2;
  vector<string> labels = {CONTROLLED_, OTHER_ + "_0", OTHER_ + "_1",
                           SECRET_ + "_0", SECRET_ + "_1"};
  vector<string> complete_labels = {
      CONTROLLED_,    OTHER_ + "_0",      OTHER_ + "_1",     SECRET_ + "_0",
      SECRET_ + "_1", OBSERVABLE_ + "_0", OBSERVABLE_ + "_1"};
  auto &model = solver->get_model();
  for (auto label : complete_labels) {
    if (symbol_vars.count(label) == 0)
      continue;
    for (auto l : symbol_vars[label]) {
      ret2 << Lit(l.var(), model[l.var()] == l_False) << ", ";
    }
    ret2 << ", ";
  }
  for (auto label : labels) {
    if (symbol_vars.count(label) == 0) {
      ret += ", ";
      continue;
    }
    ret += "";
    for (auto l : symbol_vars[label]) {
      if (model[l.var()] == l_Undef)
        ret += "x";
      if (model[l.var()] == l_True)
        ret += l.sign() ? "0" : "1";
      if (model[l.var()] == l_False)
        ret += l.sign() ? "1" : "0";
      ret += ", ";
    }
    ret += ", ";
  }
  return {ret2.str(), ret};
}
vector<unsigned> Lits2Vars(vector<Lit> &lits) {
  vector<unsigned> vars;
  for (auto l : lits) {
    vars.push_back(l.var());
  }
  return vars;
}
void replace_vars(vector<vector<unsigned>> &added_count_lits,
                  vector<unsigned> &old_count_vars,
                  vector<unsigned> &new_count_vars) {
  unordered_map<unsigned, unsigned> old_to_new;
  for (int i = 0; i < old_count_vars.size(); ++i) {
    old_to_new[old_count_vars[i]] = new_count_vars[i];
  }
  int i = 0;
  for (auto &vars : added_count_lits) {
    for (auto &var : vars) {
      var = old_to_new[var];
    }
    i++;
  }
}
void Count::AddVariableDiff(SATSolver *solver,
                            map<string, vector<Lit>> all_vars) {
  int len = -1;
  vector<Lit> watches;
  assert(all_vars.size() > 0);
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    if (len > 0) {
      assert(len == lits.size());
    }
    len = lits.size();
  }
  string diff_file = out_dir_ + "//" + out_file_ + ".addVarDiffhash";
  std::ofstream finalout(diff_file);
  auto newWatch = solver->nVars() - 1;
  solver->new_vars(len);
  for (int i = 0; i < len; ++i) {
    vector<unsigned> clause;
    newWatch++;
    clause.push_back(newWatch);
    watches.push_back(Lit(newWatch, true));
    bool xor_bool = true;
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign())
        xor_bool = !xor_bool;
    }
    solver->add_xor_clause(clause, xor_bool);
    finalout << "x" << (xor_bool ? "" : "-");
    for (auto v : clause)
      finalout << v + 1 << " ";
    finalout << std::endl;
  }
  cout << "add watches" << watches;
  solver->add_clause(watches);
  finalout << watches << " 0\n";
  finalout.close();
}
void Count::setSecretVars() {
  if (secret_vars.size())
    return;
  for (auto name_lits : symbol_vars) {
    int name_len = SECRET_.length();
    if (!name_lits.first.compare(0, SECRET_.length(), SECRET_)) {
      auto id = name_lits.first.substr(name_len);
      for (auto lit : name_lits.second) {
        secret_vars.push_back(lit.var());
        all_secret_lits[id].push_back(lit);
      }
    }
    name_len = DECLASS_.length();
    if (!name_lits.first.compare(0, DECLASS_.length(), DECLASS_)) {
      auto id = name_lits.first.substr(name_len);
      for (auto lit : name_lits.second) {
        all_declass_lits[id].push_back(lit);
      }
    }
  }
}
void Count::setCountVars() {
  if (count_vars.size())
    return;
  cout << "setCountVars\n";
  all_observe_lits.clear();
  control_lits.clear();
  all_other_lits.clear();
  all_count_vars.clear();
  vector<unsigned> other_control_vars;
  for (auto name_lits : symbol_vars) {
    if (!name_lits.first.compare(0, CONTROLLED_.length(), CONTROLLED_)) {
      for (auto lit : name_lits.second) {
        control_lits.push_back(lit);
      }
    } else if (!name_lits.first.compare(0, OBSERVABLE_.length(), OBSERVABLE_)) {
      auto id = name_lits.first.substr(OBSERVABLE_.length());
      for (auto lit : name_lits.second) {
        // count_vars.push_back(lit.var());
        all_observe_lits[id].push_back(lit);
      }
    } else if (!name_lits.first.compare(0, OTHER_.length(), OTHER_)) {
      auto id = name_lits.first.substr(OTHER_.length());
      for (auto lit : name_lits.second) {
        all_other_lits[id].push_back(lit);
      }
    }
  }
  cout << "control_lits size=" << control_lits.size() << std::endl;
  for (auto id_lits : all_observe_lits) {
    auto id = id_lits.first;
    for (auto lit : control_lits) {
      all_count_vars[id_lits.first].push_back(lit.var());
    }
    for (auto lit : all_observe_lits[id]) {
      all_count_vars[id_lits.first].push_back(lit.var());
    }
    for (auto lit : all_other_lits[id]) {
      all_count_vars[id_lits.first].push_back(lit.var());
    }
    if (declassification_mode_ == 1 && (all_declass_lits.size() > 0)) {
      for (auto lit : all_declass_lits[id]) {
        all_count_vars[id_lits.first].push_back(lit.var());
      }
    }
    cout << "all_count_vars[id_lits] size="
         << all_count_vars[id_lits.first].size() << std::endl;
  }
}
void Count::AddVariableSame(SATSolver *solver,
                            map<string, vector<Lit>> all_vars) {
  int len = -1;
  vector<Lit> watches;
  if (all_vars.size() == 0) {
    return;
  }
  assert(all_vars.size() > 0);
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    if (len > 0) {
      assert(len == lits.size());
    }
    len = lits.size();
  }
  string diff_file = out_dir_ + "//" + out_file_ + ".testsamehash";
  std::ofstream finalout(diff_file);
  for (int i = 0; i < len; ++i) {
    vector<unsigned> clause;
    bool xor_bool = false;
    cout << "add same ";
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign()) {
        cout << "reverse" << xor_bool << " to ";
        xor_bool = !xor_bool;
        cout << xor_bool << " ";
      }
      cout << lits[i] << " " << lits[i].sign() << " " << xor_bool << "\t";
    }
    cout << "\n";
    solver->add_xor_clause(clause, xor_bool);
    finalout << "x" << (xor_bool ? "" : "-");
    cout << "x" << (xor_bool ? "" : "-");
    for (auto v : clause) {
      cout << v << "\t";
      finalout << (v + 1) << " ";
    }
    cout << "0\n";
    finalout << "0\n";
  }
  finalout.close();
}

string Count::trimVar(SATSolver *solver2, vector<unsigned> &vars) {
  string ret = "";
  std::unordered_map<unsigned, string> fixed_var_set;
  set<unsigned> new_vars;
  for (auto lit : solver2->get_zero_assigned_lits()) {
    fixed_var_set[lit.var()] = lit.sign() ? "0" : "1";
  }
  for (auto var : vars) {
    if (used_vars.count(var) == 0) {
      if (find(secret_vars.begin(), secret_vars.end(), var) ==
          secret_vars.end()) {
        std::cout << "unused vars" << var << std::endl;
        ret += "u";
        continue;
      }
    }
    if (unused_sampling_vars.count(var)) {
      if (find(secret_vars.begin(), secret_vars.end(), var) ==
          secret_vars.end()) {
        std::cout << "unused_sampling_vars vars" << var << std::endl;
        ret += "u";
        continue;
      }
    }
    if (fixed_var_set.count(var) > 0) {
      ret += fixed_var_set[var];
      std::cout << "fixed_var_set vars" << var << " =" << fixed_var_set[var]
                << std::endl;
      continue;
    }
    new_vars.insert(var);
    ret += "x";
  }
  cout << "new trimed vars size=" << new_vars.size();
  vars.clear();
  vars.insert(vars.begin(), new_vars.begin(), new_vars.end());
  // std::swap(new_secret_vars, secret_vars);
  return ret;
}

static string GenerateRandomBits_prob(unsigned size, double prob) {
  string randomBits = "";
  unsigned base = 100000;
  for (int i = 0; i < size; ++i) {
    randomBits += ((rand() % base) < prob * base) ? "1" : "0";
  }
  return randomBits;
}
static string GenerateRandomBits(unsigned size) {
  return GenerateRandomBits_prob(size, 0.5);
}

template <class T> void print_map(std::map<std::string, vector<T>> &map) {
  for (auto var : map) {
    cout << var.first << " ";
    for (auto i : var.second)
      cout << i << " ";
    cout << std::endl;
  }
}
static string getSSignature(vector<vector<unsigned>> &added_secret_vars) {
  string sxor = "";
  for (auto x : added_secret_vars) {
    sxor += "xor(";
    for (auto l : x) {
      if (sxor[sxor.length() - 1] != ',' && sxor[sxor.length() - 1] != '(')
        sxor += ",";
      sxor += std::to_string(l);
    }
    sxor += ");";
  }
  return sxor;
}
void Count::RecordCount(map<int, unsigned> &sols, int hash_count, string rnd) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sols[hash_count] << "\t" << hash_count + unrelated_number_countvars
          << "\t%" << rnd << std::endl;
  count_f.close();
}

void Count::RecordCountInter(map<int, unsigned> &sols, int hash_count,
                             vector<map<int, unsigned>> b_sols,
                             vector<int> b_hash_counts, string rnd) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".inter.count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sols[hash_count] << "\t" << hash_count + unrelated_number_countvars
          << "\t";
  int norm_sum_sols = 0;
  for (int id = 0; id < b_sols.size(); ++id) {
    int hash = b_hash_counts[id];
    count_f << b_sols[id][hash] << "\t" << hash + unrelated_number_countvars
            << "\t";
    norm_sum_sols += b_sols[id][hash] * pow(2, hash - hash_count);
  }
  double j =
      1 - 1.0 * sols[hash_count] / double(norm_sum_sols - sols[hash_count]);
  count_f << std::setprecision(4) << j << "\t%" << rnd << std::endl;
  count_f.close();
}
void Count::calculateDiffSolution(vector<vector<Lit>> &sol1,
                                  vector<vector<Lit>> &sol2,
                                  vector<string> &sol_str1,
                                  vector<string> &sol_str2, string rnd) {
  if (conf.verbosity == 0) {
    return;
  }
  set<string> str1;
  //(sol_str1.begin(), sol_str1.end()),
  set<string> str2;
  map<string, int> strmap;
  //(sol_str2.begin(), sol_str2.end());
  std::ofstream solution_f(out_dir_ + "//" + out_file_ + ".sol.diff",
                           std::ofstream::out | std::ofstream::app);

  for (auto lit : sol1) {
    std::stringstream ss("");
    ss << lit;
    cout << ss.str() << std::endl;
    str1.insert(ss.str());
  }
  int i = 0;
  for (auto lit : sol2) {
    std::stringstream ss("");
    ss << lit;
    strmap[ss.str()] = i;
    ++i;
    str2.insert(ss.str());
  }

  for (auto s : str1) {
    cout << s << std::endl;
  }
  for (auto s : str2) {
    cout << s << std::endl;
  }
  cout << "====calculateDiffSolution\n";
  cout << str1.size() << "\t" << str2.size() << std::endl;
  for (auto s : str2) {
    if (!str1.count(s)) {
      cout << s << std::endl << strmap[s] << std::endl;
      solution_f << s << " %" << rnd << std::endl;
    }
  }
  cout << "====calculateSameSolution\n";
  for (auto s : str2) {
    if (str1.count(s)) {
      cout << s << std::endl;
    }
  }
  solution_f.close();
}
void Count::RecordSolution(string rnd, string subfix = "") {

  if (!record_solution_)
    return;
  std::cout << "start record solution\n";
  std::ofstream solution_f(out_dir_ + "//" + out_file_ + ".sol" + subfix,
                           std::ofstream::out | std::ofstream::app);
  for (int i = 0; i < solution_lits.size(); ++i)
    solution_f << solution_lits[i] << "; " << solution_strs[i] << " % " << rnd
               << std::endl;
  solution_f.close();
}

void Count::add_count_options() {
  countOptions_.add_options()("cycles", po::value(&cycles_)->default_value(1),
                              "Number of composition cycles.");
  countOptions_.add_options()(
      "victim", po::value(&victim_model_config_)->default_value(""),
      "Victim model config: secret  sym_name offset size\n observe: "
      "(sym_name,offset,size)\n control: (sym_name,offset,size) ");
  countOptions_.add_options()("debug", po::value(&debug)->default_value(false),
                              "Debug");
  countOptions_.add_options()(
      "declassification_mode",
      po::value(&declassification_mode_)->default_value(1),
      "declassification_mode: 0: additional leakage, 1: additional leakage "
      "when declassified is known");
  countOptions_.add_options()(
      "caching_solution", po::value(&caching_solution_)->default_value(true),
      "Caching solution when counting ");
  countOptions_.add_options()("symmap",
                              po::value(&symmap_file_)->default_value(""),
                              "Initilization constraint file.");
  countOptions_.add_options()("initfile",
                              po::value(&init_file_)->default_value(""),
                              "Initilization constraint file.");
  countOptions_.add_options()("count_out",
                              po::value(&out_file_)->default_value("out"),
                              "Countd filename.");
  countOptions_.add_options()("out",
                              po::value(&out_dir_)->default_value("tmp"));
  countOptions_.add_options()("xor_ratio",
                              po::value(&xor_ratio_)->default_value(0.5));
  countOptions_.add_options()("num_xor_cls",
                              po::value(&num_xor_cls_)->default_value(0));
  countOptions_.add_options()("max_sol",
                              po::value(&max_sol_)->default_value(64));
  countOptions_.add_options()("max_count_times",
                              po::value(&max_count_times_)->default_value(10));
  countOptions_.add_options()("nsample", po::value(&nsample)->default_value(5));
  countOptions_.add_options()("min_log_size",
                              po::value(&min_log_size_)->default_value(-1));
  countOptions_.add_options()("max_log_size",
                              po::value(&max_log_size_)->default_value(-1));
  countOptions_.add_options()("max_xor_per_var",
                              po::value(&max_xor_per_var_)->default_value(32));
  countOptions_.add_options()("xor_decay",
                              po::value(&xor_decay_)->default_value(1.0));
  countOptions_.add_options()("count_mode",
                              po::value(&mode_)->default_value("block"),
                              "mode: nonblock-> backtrack, block -> block");
  countOptions_.add_options()(
      "use_overlap_coefficient",
      po::value(&use_overlap_coefficient_)->default_value(true),
      "Valid when inter_mode=2, False: use Y1 V Y2 as denominator, True: use "
      "Y1 as denominator");
  countOptions_.add_options()(
      "inter_mode", po::value(&inter_mode_)->default_value(0),
      "1-> secret_1 and secret_2, observe_1 and observe_2, 0: single,  2: "
      "JaccardHat if use_overlap_coefficient=false, Overlap Coef if "
      "use_overlap_coefficient=true, 3: JaccardHat with Same Other");
  countOptions_.add_options()(
      "pick_sample_first",
      po::value(&conf.pickSampleFirst)->default_value(false),
      "Initilization constraint file.");
  countOptions_.add_options()(
      "record_solution", po::value(&record_solution_)->default_value(true),
      "True: write solutions; false: do not write solutions");
  countOptions_.add_options()(
      "search_all", po::value(&search_all)->default_value(false),
      "True: write solutions; false: do not write solutions");
  help_options_simple.add(countOptions_);
  help_options_complicated.add(countOptions_);
}

void Count::add_supported_options() {
  Main::add_supported_options();
  add_count_options();
}

bool Count::readVictimModel(SATSolver *&solver) {
  std::ifstream vconfig_f;
  if (victim_model_config_.length() == 0)
    return false;
  vconfig_f.open(victim_model_config_);
  map<string, vector<Lit>> new_symbol_vars;
  string line;
  while (std::getline(vconfig_f, line)) {
    std::stringstream ss(line);
    std::string token;
    vector<std::string> tokens;
    while (std::getline(ss, token, ' ')) {
      tokens.push_back(token);
    }
    if (tokens.size() != 4) {
      cout << "error victim model: " << line;
      exit(1);
    }
    string name = tokens[1];
    int offset = std::stoi(tokens[2]);
    int size = std::stoi(tokens[3]);
    if (symbol_vars.count(name) == 0) {
      cout << "not found symbol: " << name;
      exit(1);
    }
    if (!IsValidVictimLabel(tokens[0])) {
      cout << "Error Victim Label " << tokens[0];
      exit(1);
    }
    if (symbol_vars[name].size() < size) {
      cout << "Error symbol " << name << " " << symbol_vars[name].size() << " "
           << size << std::endl;
      exit(1);
    }
    for (int i = offset; i < offset + size; ++i) {
      victim_model_[tokens[0]].push_back(symbol_vars[name][i].var());
      new_symbol_vars[tokens[0]].push_back(symbol_vars[name][i]);
    }
  }
  solver->set_symbol_vars(&new_symbol_vars);
  string symbol_tmpfile = out_dir_ + "//" + out_file_ + ".symbol";
  std::ofstream symbol_tmpf(symbol_tmpfile);

  /*  for (auto &vars : new_symbol_vars) {
      string values = trimVar(solver, vars.second);
      symbol_tmpf << vars.first << "\t" << values << std::endl;
    }*/
  symbol_tmpf.close();
  sampling_vars.clear();
  for (auto lits : new_symbol_vars)
    for (auto lit : lits.second)
      sampling_vars.push_back(lit.var());
  solver->set_sampling_vars(&sampling_vars);
  solver->simplify();
  string victim_cnf_file = out_dir_ + "//" + out_file_ + ".simp";
  std::ofstream finalout(victim_cnf_file);
  solver->dump_irred_clauses_ind_only(&finalout);
  finalout.close();
  // delete solver;
  auto newconf = conf;
  SATSolver s(&newconf);
  solver = newCounterSolver(&s, (void *)&newconf);
  symbol_vars.clear();
  sampling_vars.clear();
  readInAFile(solver, victim_cnf_file);
  return true;
  /*
  vector<unsigned> secret_vars(victim_model_[SECRET_].begin(),
                               victim_model_[SECRET_].end());
  count_vars.insert(count_vars.end(), victim_model_[CONTROLLED_].begin(),
                    victim_model_[CONTROLLED_].end());
  count_vars.insert(count_vars.end(), victim_model_[OBSERVABLE_].begin(),
                    victim_model_[OBSERVABLE_].end());
  count_vars.insert(count_vars.end(), victim_model_[OTHER_].begin(),
                    victim_model_[OTHER_].end());*/
}
string Count::SampleSmallXor(SATSolver *solver2, std::vector<unsigned> vars,
                             int num_xor_cls, vector<Lit> &watch,
                             vector<vector<unsigned>> &alllits,
                             vector<bool> &rhs, Lit addInner,
                             bool is_restarted) {

  num_xor_cls = num_xor_cls * amplifier_factor_;
  vector<Lit> addInners;
  addInners.push_back(addInner);
  set<vector<bool>> rhs_sets;
  string ret = "";
  for (int i = 0; i < amplifier_factor_; ++i) {
    auto sub_addInner = new_watch(solver2);
    watch.clear();
    ret = Sample(solver2, vars, num_xor_cls, watch, alllits, rhs, sub_addInner,
                 is_restarted);
    addInners.push_back(sub_addInner);
    rhs_sets.insert(rhs);
    while (rhs_sets.count(rhs)) {
      shuffle(rhs);
    }
  }
  solver2->add_clause(addInners);
  return ret;
}
int myrandom(int i) { return std::rand() % i; }

string Count::Sample(SATSolver *solver2, std::vector<unsigned> vars,
                     int num_xor_cls, vector<Lit> &watch,
                     vector<vector<unsigned>> &alllits, vector<bool> &rhs,
                     Lit addInner, bool is_restarted) {
  /*if (num_xor_cls < 2) {
    return SampleSmallXor(solver2, vars, num_xor_cls, watch, alllits, rhs,
                          addInner, is_restarted);
  }*/
  double ratio = xor_ratio_;
  double xor_decay = xor_decay_;
  srand(unsigned(time(NULL)));
  if (num_xor_cls * ratio > max_xor_per_var_) {
    ratio = max_xor_per_var_ * 1.0 / num_xor_cls;
    cout << "too many xor... we hope to use at most" << max_xor_per_var_
         << " xor per var, thus change ratio to" << ratio << std::endl;
  }
  string randomBits = "";
  std::set<string> randomBitsSet;
  if (num_xor_cls == vars.size()) {
    // only pick one value
    ratio = 1.0 / num_xor_cls;
    xor_decay = 1.0;
    randomBits = string(vars.size() * num_xor_cls, '0');
    for (int i = 0; i < num_xor_cls; ++i) {
      randomBits[i + i * vars.size()] = '1';
    }
    // only pick one value
    ratio = 1.0 / num_xor_cls;
    xor_decay = 1.0;
    randomBits = string(vars.size() * num_xor_cls, '0');
    for (int i = 0; i < num_xor_cls; ++i) {
      randomBits[i + i * vars.size()] = '1';
    }
  } else {
    for (int i = 0; i < num_xor_cls; ++i) {
      int max_xor_per_var = ratio * vars.size();
      string tmp(max_xor_per_var, '1');
      tmp = tmp + string(vars.size() - max_xor_per_var, '0');
      max_xor_per_var = max_xor_per_var * xor_decay;
      xor_decay = 1.0 / xor_decay;
      while (true) {
        // tmp = GenerateRandomBits_prob(vars.size(), ratio);
        std::random_shuffle(tmp.begin(), tmp.end(), myrandom);
        if (tmp.find("1") == std::string::npos) {
          // no var is chosen in the hash
          continue;
        }
        if (randomBitsSet.count(tmp) == 0)
          break;
      }
      randomBitsSet.insert(tmp);
      randomBits += tmp;
    }
  }
  string randomBits_rhs = GenerateRandomBits(num_xor_cls);
  vector<unsigned> lits;
  // assert watch=0;?
  if (watch.size() < num_xor_cls) {
    int diff = num_xor_cls - watch.size();
    int base = watch.size();
    watch.resize(num_xor_cls);
    for (int i = 0; i < diff; ++i) {
      watch[base + i] = Lit(solver2->nVars() + i, false);
    }
    solver2->new_vars(diff);
  }
  for (int i = 0; i < num_xor_cls; ++i) {
    lits.clear();
    if (alllits.size() > i) {
      // reuse generated xor lits;
      // lits = alllits[i];
      if (is_restarted) {
        lits = alllits[i];
      }
    } else {
      while (lits.size() < 1) {
        for (unsigned j = 0; j < vars.size(); j++) {
          if (randomBits[i * vars.size() + j] == '1')
            lits.push_back(vars[j]);
          if (hashf)
            *hashf << vars[j] + 1 << " ";
        }
        assert(lits.size() >= 1);
      }
      alllits.push_back(lits);
      rhs.push_back(randomBits_rhs[i] == '1');
    }
    // 0 xor 1 = 1, 0 xor 0= 0, thus,we add watch=0 => xor(1,2,4) = r
    if (watch[i].var() >= solver2->nVars()) {
      solver2->new_vars(watch[i].var() - solver2->nVars() + 1);
    }
    lits.push_back(watch[i].var());

    if (addInner != lit_Undef) {
      solver2->add_clause({addInner, watch[i]});
      cout << "secret hash xor:\n";
      cout << "watch:" << addInner << watch[i];
      for (auto l : lits) {
        cout << l + 1 << "\t";
      }
      cout << rhs[i] << std::endl;
    }
    // e.g., xor watch 1 2 4 ..
    solver2->add_xor_clause(lits, rhs[i]);
  }
  return randomBits + randomBits_rhs;
}
int64_t Count::bounded_sol_count_cached(SATSolver *solver,
                                        const vector<unsigned> &count_vars,
                                        unsigned maxSolutions,
                                        const vector<Lit> &assumps,
                                        Lit act_lit) {
  int64_t nsol = 0;
  vector<Lit> blocked_lits;
  for (auto solution : cached_inter_solution) {
    auto begin = cpuTimeTotal();
    solution.insert(solution.end(), assumps.begin(), assumps.end());
    auto ret = solver->solve(&solution, true);
    if (ret == l_True) {
      nsol++;
      blocked_lits.clear();
      blocked_lits.push_back(act_lit);
      for (auto l : solution) {
        blocked_lits.push_back(~l);
      }
      solver->add_clause(blocked_lits);
    }

    std::cout << "check cached sol once" << cpuTimeTotal() - begin
              << "nsol=" << nsol << std::endl;
    if (nsol >= maxSolutions) {
      break;
    }
  }
  cout << "cached solution =" << nsol;
  return nsol;
}
int64_t Count::bounded_sol_count(SATSolver *solver,
                                 const vector<unsigned> &target_count_vars,
                                 unsigned maxSolutions,
                                 const vector<Lit> &assumps, bool only_ind) {
  unsigned solutions = 0;
  vector<Lit> solution;
  lbool ret;
  // solver->load_state(conf.saved_state_file);
  // setCountVars();
  auto s_vars = target_count_vars;
  solver->set_sampling_vars(&s_vars);

  if (mode_ == "nonblock") {
    ret = solver->solve(&assumps, only_ind);
    for (auto sol_str : solver->get_solutions()) {
      std::stringstream ss(sol_str);
      string token;
      solution.clear();
      while (ss >> token) {
        int int_lit = std::stoi(token);
        unsigned var = abs(int_lit) - 1;
        solution.push_back(Lit(var, int_lit < 0));
      }
      solution_strs.push_back(getCIISSModel(solver)[0]);
      solution_lits.push_back(solution);
    }
    // delete solver;
    return solver->n_seareched_solutions();
  }
  // Set up things for adding clauses that can later be removed
  vector<lbool> model;
  vector<Lit> new_assumps(assumps);
  solver->new_var();
  unsigned act_var = solver->nVars() - 1;
  new_assumps.push_back(Lit(act_var, true));
  long begin = cpuTimeTotal();
  if (new_assumps.size() > 1)
    solver->simplify(&new_assumps);
  if (debug) {
    std::ofstream finalout("debug.cnf");
    for (auto l : new_assumps) {
      solver->add_clause({l});
      symbol_vars["assump"].push_back(l);
    }
    solver->dump_irred_clauses_ind_only(&finalout);
    finalout.close();
    exit(0);
  }

  std::cout << "after simp, time=" << cpuTimeTotal() - begin << std::endl;
  solutions = bounded_sol_count_cached(solver, target_count_vars, maxSolutions,
                                       new_assumps, Lit(act_var, false));
  while (solutions < maxSolutions) {
    begin = cpuTimeTotal();
    ret = solver->solve(&new_assumps, only_ind);
    std::cout << "max_sol=" << maxSolutions << ",solve once"
              << cpuTimeTotal() - begin << std::endl;
    assert(ret == l_False || ret == l_True);
    if (conf.verbosity >= 2) {
      cout << "[appmc] bounded_sol_count ret: " << std::setw(7) << ret;
      if (ret == l_True) {
        cout << " sol no.  " << std::setw(3) << solutions;
      } else {
        cout << " No more. " << std::setw(3) << "";
      }
    }

    if (ret != l_True) {
      break;
    }
    solutions++;
    model = solver->get_model();
    if (solutions < maxSolutions) {
      vector<Lit> lits;
      lits.push_back(Lit(act_var, false));
      solution.clear();
      for (const unsigned var : target_count_vars) {
        solution.push_back(Lit(var, model[var] == l_False));
        if (model[var] != l_Undef) {
          lits.push_back(Lit(var, model[var] == l_True));
        } else {
          assert(false);
        }
      }
      assert(solution.size() == target_count_vars.size());
      if (conf.verbosity > 1) {
        cout << "====result===" << std::endl;
        cout << std::setbase(16);

        for (int k = 0; k < 8; ++k) {
          long long val = 0, base = 1;
          for (int i = 0; i < 100; ++i) {
            if (i % 32 == 0) {
              val = 0;
            }
            val = (val << 1) + (lits[1 + i + k * 100].sign() ? 1 : 0);
            if (i % 32 == 31) {
              cout << val << " ";
            }
          }
          cout << std::setbase(16);
          cout << val << " ";
          cout << std::endl;
        }
        cout << std::setbase(10);
        cout << std::setbase(10);
        cout << "[appmc] Adding banning clause: " << lits << endl;
      }
      solver->add_clause(lits);
      if (record_solution_ || caching_solution_) {
        solution_lits.push_back(solution);
        solution_strs.push_back(getCIISSModel(solver)[0]);
      }
    }
  }
  // Remove clauses added
  vector<Lit> cl_that_removes;
  cl_that_removes.push_back(Lit(act_var, false));
  solver->add_clause(cl_that_removes);

  assert(ret != l_Undef);
  return solutions;
}
map<int, unsigned> Count::count_once(SATSolver *solver,
                                     vector<unsigned> &target_count_vars,
                                     const vector<Lit> &secret_watch, int &left,
                                     int &right, int &hash_count,
                                     bool reserve_xor) {
  if (left > right) {
    left = right - 30;
  }
  long total_start = cpuTimeTotal();
  int nsol = 0, nice_hash_count = 0;
  if (!reserve_xor) {
    added_count_lits.clear();
    count_rhs.clear();
    count_watch.clear();
  } else {
    count_watch.clear();
    Sample(solver, target_count_vars, added_count_lits.size(), count_watch,
           added_count_lits, count_rhs, lit_Undef, true);
  }
  map<int, unsigned> solution_counts;
  map<int, vector<vector<Lit>>> hash_solutions;
  map<int, vector<string>> hash_solution_strs;
  vector<Lit> assump;
  solution_lits.clear();
  solution_strs.clear();
  cout << "target count size" << target_count_vars.size() << std::endl;
  if (left < 1) {
    nsol = bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    hash_solutions[0] = solution_lits;
    hash_solution_strs[0] = solution_strs;
    if (nsol < max_sol_) {
      left = right = hash_count = 0;
      solution_counts[0] = nsol;
      cout << "found solution" << nsol << "no need xor\n";
    }
  }
  hash_count = hash_count > 0 ? hash_count : (right + left) / 2;
  while (left < right && (nsol < max_sol_ * 0.6 || nsol >= max_sol_)) {
    solution_lits.clear();
    solution_strs.clear();
    cout << "starting... hash_count=" << hash_count << std::endl << std::flush;
    long start = cpuTimeTotal();
    Sample(solver, target_count_vars, hash_count, count_watch, added_count_lits,
           count_rhs, lit_Undef, true);
    cout << "sample time cost=" << cpuTimeTotal() - start << std::endl;
    assump.clear();
    // assump = secret_watch;
    assump.insert(assump.end(), count_watch.begin(),
                  count_watch.begin() + hash_count);
    if (!solution_counts.count(hash_count)) {
      solution_counts[hash_count] =
          bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
      hash_solutions[hash_count] = solution_lits;
      hash_solution_strs[hash_count] = solution_strs;
      cached_inter_solution.insert(cached_inter_solution.end(),
                                   solution_lits.begin(), solution_lits.end());
    }
    nsol = solution_counts[hash_count];
    if (nsol >= max_sol_) {
      left = hash_count + 1;
    } else if (nsol < max_sol_ * 0.6) {
      right = hash_count;
      nice_hash_count = hash_count;
      if (nsol > 0) {
        hash_count = std::max(
            left, hash_count - int(floor(log2(max_sol_ * 1.0 / nsol))));
        left = std::max(left, hash_count -
                                  int(floor(log2(max_sol_ * 1.0 / nsol))) - 1);
        cout << "hash_count=" << hash_count << ", nsol=" << nsol
             << "left=" << left << "right=" << right << std::endl;
        continue;
      }
    } else {
      nice_hash_count = hash_count;
      right = hash_count;
      left = hash_count;
      break;
    }
    if (right <= left && solution_counts[hash_count] >= max_sol_) {
      if (solution_counts.rbegin()->second >= max_sol_) {
        right = int(target_count_vars.size());
      }
    }
    if (right <= left && solution_counts[hash_count] == 0) {
      if (solution_counts.begin()->second == 0) {
        left = 0;
      }
    }
    cout << "hash_count=" << hash_count << ", nsol=" << nsol << "left=" << left
         << "right=" << right << std::endl;
    hash_count = left + (right - left) / 2;
  }
  hash_count = nice_hash_count;
  bool retry = false, retry_max_sol = max_sol_;
  if (!solution_counts.count(hash_count) && hash_count >= 0) {
    retry = true;
  }
  if (solution_counts[hash_count] > max_sol_) {
    retry = true;
    retry_max_sol = max_sol_ * 4;
  }
  if (solution_counts[hash_count] == 0) {
    if (solution_counts.count(hash_count - 1) &&
        solution_counts[hash_count - 1] > 0) {
      retry = true;
      hash_count = hash_count - 1;
      retry_max_sol = max_sol_ * 4;
    }
  }
  if (retry) {
    // std::cerr << "error !solution_counts.count(hash_count) && hash_count >=
    // 0"; assert(false);
    long start = cpuTimeTotal();
    Sample(solver, target_count_vars, hash_count, count_watch, added_count_lits,
           count_rhs, lit_Undef, true);
    cout << "sample time cost=" << cpuTimeTotal() - start << std::endl;
    solution_lits.clear();
    solution_strs.clear();
    assump.clear();
    // assump = secret_watch;
    assump.insert(assump.end(), count_watch.begin(),
                  count_watch.begin() + hash_count);
    solution_counts[hash_count] = bounded_sol_count(
        solver, target_count_vars, retry_max_sol, assump, true);
    hash_solutions[hash_count] = solution_lits;
    hash_solution_strs[hash_count] = solution_strs;
    cout << "retry hashcount=" << hash_count
         << ", nsols=" << solution_counts[hash_count];
  }

  left = std::max(0, hash_count - std::min(5, (hash_count + 1) / 2));
  right = std::min(int(target_count_vars.size()),
                   hash_count + std::min(5, (hash_count + 1) / 2));
  cout << "found solution" << solution_counts[hash_count] << "* 2^"
       << hash_count << std::endl;
  solution_lits = hash_solutions[hash_count];
  solution_strs = hash_solution_strs[hash_count];
  cout << "Total time=" << cpuTimeTotal() - total_start << std::endl;
  return solution_counts;
}

vector<unsigned> Count::getCISAlt() {
  vector<unsigned> ret;
  string id0 = "_0", id1 = "_1";
  for (auto l : control_lits) {
    ret.push_back(l.var());
  }
  for (auto l : all_other_lits[id1]) {
    ret.push_back(l.var());
  }
  for (auto l : all_secret_lits[id1]) {
    ret.push_back(l.var());
  }
  return ret;
}
bool Count::countCISAlt(SATSolver *solver, vector<unsigned> &secret_vars) {
  count_vars = getCISAlt();
  // when in declassification mode, backup_solvers.size()=2; when in normal
  // mode, backup_solvers.size()=1
  vector<vector<unsigned>> backup_count_vars(backup_solvers.size());
  for (int i = 0; i < backup_solvers.size(); ++i) {
    backup_count_vars[i] = getCISAlt();
    // backup_solvers[i]->set_sampling_vars(&backup_count_vars[i]);
  }
  auto cvar = count_vars;
  // solver->set_sampling_vars(&cvar);
  vector<vector<unsigned>> added_secret_vars;
  map<string, vector<vector<unsigned>>> all_added_secret_vars;
  map<string, vector<bool>> all_added_secret_rhs;
  vector<Lit> secret_watch;
  vector<bool> secret_rhs;
  string secret_rnd = "";
  // trimVar(solver, secret_vars);
  cout << "count\n"
       << solver << ", secret size=" << secret_vars.size()
       << "count size=" << count_vars.size();
  cout << "Sample\n" << std::flush;
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n"
         << std::flush;
    num_xor_cls_ = secret_vars.size();
  }
  set<vector<bool>> secret_rhs_set;
  map<unsigned, int> var_index;
  string id = "_0";
  vector<unsigned> current_secret_vars, alt_secret_vars;
  int offset = 0;
  current_secret_vars.clear();
  for (auto lit : all_secret_lits[id]) {
    current_secret_vars.push_back(lit.var());
    var_index[lit.var()] = offset;
    offset++;
  }
  for (auto lit : all_secret_lits["_1"]) {
    alt_secret_vars.push_back(lit.var());
  }
  // when one secret set is selcted, we should generate another set using
  // same hash but with different rhs to ensure disjoint sets.
  auto rhs_watch = new_watch(solver);
  // assert h(Si)=ri;
  secret_watch.clear();
  secret_rnd += Sample(solver, current_secret_vars, num_xor_cls_, secret_watch,
                       added_secret_vars, secret_rhs, rhs_watch, true);
  secret_watch.clear();
  solver->add_clause({~rhs_watch});
  Sample(solver, alt_secret_vars, num_xor_cls_, secret_watch, added_secret_vars,
         secret_rhs, lit_Undef, true);
  for (auto &l : secret_watch) {
    l = ~l;
  }
  solver->add_clause(secret_watch);
  solver->simplify();
  if (solver->solve() == l_False) {
    return false;
  }
  assert(backup_solvers.size());
  for (int i = 0; i < backup_solvers.size(); ++i) {
    // assert h(Si)=ri;
    secret_watch.clear();
    Sample(backup_solvers[i], current_secret_vars, num_xor_cls_, secret_watch,
           added_secret_vars, secret_rhs, lit_Undef, true);
    // hash(s)!=r;
    // xor1(s1,s2..) = watch1;
    // xor2(s1,s2..) = watch2;
    // ...
    // ~watch1 || ~watch2 ...
    for (auto &l : secret_watch) {
      l = ~l;
    }
    backup_solvers[i]->add_clause(secret_watch);

    backup_solvers[i]->simplify();
    trimVar(backup_solvers[i], backup_count_vars[i]);
  }
  cout << "count size=" << count_vars.size() << std::endl;

  int hash_count = 0;
  int left, right;
  vector<int> backup_left(backup_solvers.size(), 0),
      backup_right(backup_solvers.size(), 0),
      backup_hash_count(backup_solvers.size(), 0);
  left = left_ ? left_ : ((min_log_size_ == -1) ? 0 : min_log_size_);
  right = right_ ? right_
                 : ((max_log_size_ == -1) ? count_vars.size() : max_log_size_);
  for (int i = 0; i < backup_solvers.size(); ++i) {
    backup_left[i] = backup_left_[i] ? backup_left_[i] : left;
    backup_right[i] = backup_right_[i]
                          ? backup_right_[i]
                          : ((max_log_size_ == -1) ? backup_count_vars[i].size()
                                                   : max_log_size_);
    backup_hash_count[i] = 0;
  }
  int max_sol = max_sol_;
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {

    cout << count_times << "=========count for target "
         << "left=" << left << ",right= " << right << "\n\n";
    cached_inter_solution.clear();
    if (count_times == 0) {
      max_sol_ = 2;
    } else if (count_times > 0) {
      max_sol_ = max_sol;
      left -= floor(max_sol / 2);
      right -= floor(max_sol / 2);
      for (int i = 0; i < backup_solvers.size(); ++i) {
        backup_left[i] -= floor(max_sol / 2);
        backup_right[i] -= floor(max_sol / 2);
      }
    }
    map<int, unsigned> solution_counts =
        count_once(solver, count_vars, {}, left, right, hash_count);
    RecordSolution(secret_rnd);
    cached_inter_solution = solution_lits;
    auto inter_solution_lits = solution_lits;
    auto inter_solution_strs = solution_strs;
    auto prev_count_vars = &count_vars;
    vector<map<int, unsigned>> backup_solution_counts(backup_solvers.size());
    int idx = 0;
    for (int i = 0; i < backup_solvers.size(); ++i) {
      cout << "======count for id=" << i << "left=" << backup_left[i]
           << ",right= " << backup_right[i] << "\n\n";
      backup_solution_counts[i] = count_once(
          backup_solvers[i], backup_count_vars[i], {}, backup_left[i],
          backup_right[i], backup_hash_count[i], true);
      RecordSolution(secret_rnd, "." + std::to_string(i));
    }
    calculateDiffSolution(inter_solution_lits, solution_lits,
                          inter_solution_strs, solution_strs, secret_rnd);
    if (hash_count != backup_hash_count[0] ||
        solution_counts[hash_count] != backup_solution_counts[0][hash_count]) {
      std::cerr << "find non zero J";
      exit(-1);
    }
    if (inter_mode_ == 0)
      RecordCount(solution_counts, hash_count, secret_rnd);
    else {
      if (count_times > 0)
        RecordCountInter(solution_counts, hash_count, backup_solution_counts,
                         backup_hash_count, secret_rnd);
    }
  }
  left_ = 0;
  for (size_t i = 0; i < backup_right_.size(); ++i) {
    backup_left_[i] = 0;
    // backup_right_[i] = backup_right[i] + 3;
  }
  return true;
}

void compose_distinct_secretset(
    SATSolver *solver,
    const map<string, vector<Lit>> &solver_secret_rhs_watches, bool useCup) {
  auto choice1 = Lit(solver->nVars(), true);
  auto choice2 = Lit(choice1.var() + 1, true);
  solver->new_vars(2);
  for (auto id_watches_pair : solver_secret_rhs_watches) {
    auto id_watches = id_watches_pair.second;
    if (id_watches.size() != 2) {
      std::cerr << "id_watches.size()=" << id_watches.size() << std::endl;
    }
    solver->add_clause({~id_watches[0], choice1});
    solver->add_clause({~id_watches[1], choice2});
    cout << "====compose_distinct_secretset===\n";
    cout << ~id_watches[0] << "," << choice1 << std::endl;
    cout << ~id_watches[1] << "," << choice2 << std::endl;
  }
  if (useCup) {
    // ( h(S1)=r1 && h(S2)=r2 ) or (h(S1)=r2 && h(S2)=r1)
    solver->add_xor_clause({choice2.var(), choice1.var()}, true);
  } else {
    // ( h(S1)=r1 && h(S2)=r2 )
    solver->add_clause({~choice1});
    // solver->add_clause({choice2});
  }
}

bool Count::count(SATSolver *solver, vector<unsigned> &secret_vars) {
  vector<vector<unsigned>> added_secret_vars;
  map<string, vector<vector<unsigned>>> all_added_secret_vars;
  map<string, vector<bool>> all_added_secret_rhs;
  vector<Lit> secret_watch;
  vector<bool> secret_rhs;
  string secret_rnd = "";
  // trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n" << std::flush;
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n"
         << std::flush;
    num_xor_cls_ = secret_vars.size();
  }
  map<string, vector<Lit>> solver_secret_rhs_watches;
  if (inter_mode_ == 0) {
    auto rhs_watch = new_watch(solver);
    solver->add_clause({~rhs_watch});
    secret_rnd = Sample(solver, secret_vars, num_xor_cls_, secret_watch,
                        added_secret_vars, secret_rhs, rhs_watch);

  } else {
    map<unsigned, int> prev_secret_var_to_index;
    int number_S = 0;
    vector<string> ids = getIDs();
    for (size_t i = 0; i < ids.size(); ++i) {
      // for (auto id_lits : all_secret_lits) {
      string id = ids[i];
      cout << id;
      auto current_secret_vars = Lits2Vars(all_secret_lits[id]);
      // when one secret set is selcted, we should generate another set using
      // same hash but with different rhs to ensure disjoint sets.

      if (i > 1 || shuffle(secret_rhs)) {
        for (auto &added_vars : added_secret_vars) {
          // replace var from secret_1 to secret_2
          for (auto &var : added_vars) {
            var = current_secret_vars[prev_secret_var_to_index[var]];
          }
        }
      }
      for (int offset = 0; offset < current_secret_vars.size(); ++offset) {
        prev_secret_var_to_index[current_secret_vars[offset]] = offset;
      }
      if (i < 2) {
        auto rhs_watch = new_watch(solver);

        // assert h(Si)=ri;
        secret_watch.clear();
        secret_rnd +=
            Sample(solver, current_secret_vars, num_xor_cls_, secret_watch,
                   added_secret_vars, secret_rhs, rhs_watch, true);
        solver_secret_rhs_watches[id].push_back(rhs_watch);
      } else {
        auto rhs_watch = solver_secret_rhs_watches[ids[i - 1]].back();
        secret_watch.clear();
        secret_rnd +=
            Sample(solver, current_secret_vars, num_xor_cls_, secret_watch,
                   added_secret_vars, secret_rhs, rhs_watch, true);
      }
      // solver->add_clause({~rhs_watch});
      all_added_secret_vars[id] = added_secret_vars;
      all_added_secret_rhs[id] = secret_rhs;
    }
    for (size_t i = 0; i < 2; ++i) {
      std::cout << "sample opposite sets: H(S1)=r2, H(S2)=r1" << std::endl;
      string id = ids[i];
      string add_id = ids[1 - i];
      auto current_secret_vars = Lits2Vars(all_secret_lits[id]);
      auto added_secret_vars = all_added_secret_vars[id];
      auto secret_rhs = all_added_secret_rhs[add_id];
      // add H(S1)=r2 xor solver_secret_rhs_watches[2]
      // add H(S2)=r1 xor solver_secret_rhs_watches[3]
      auto secret_rhs_watch = new_watch(solver);
      secret_watch.clear();
      solver_secret_rhs_watches[id].push_back(secret_rhs_watch);
      Sample(solver, current_secret_vars, num_xor_cls_, secret_watch,
             added_secret_vars, secret_rhs, secret_rhs_watch, true);
    }
    for (size_t i = 2; i < ids.size(); ++i) {
      secret_watch.clear();
      auto secret_rhs = all_added_secret_rhs[ids[1]];
      auto added_secret_vars = all_added_secret_vars[ids[i]];
      Sample(solver, Lits2Vars(all_secret_lits[ids[i]]), num_xor_cls_,
             secret_watch, added_secret_vars, secret_rhs,
             solver_secret_rhs_watches[ids[1]].back(), true);
    }
    compose_distinct_secretset(solver, solver_secret_rhs_watches,
                               use_overlap_coefficient_);
    std::ofstream ff(out_dir_ + "/" + std::to_string(num_xor_cls_) +
                         ".inter.cnf",
                     std::ofstream::out);
    solver->dump_irred_clauses_ind_only(&ff);
    ff.close();
    // exit(1);
    for (int k = 0; k < backup_solvers.size(); ++k) {
      cout << "sample for solver id" << k << std::endl;
      map<string, vector<Lit>> backup_secret_rhs_watches;
      backup_secret_rhs_watches.clear();
      for (size_t i = 0; i < 2; ++i) {
        // for (auto id_lits : all_secret_lits) {
        string id = ids[i];
        // for (auto id_added_secret_vars : all_added_secret_vars) {
        // auto id = id_added_secret_vars.first;
        backup_secret_rhs_watches[id].resize(2);
        for (size_t j = 0; j < 2; ++j) {
          string jid = ids[j];
          auto secret_rhs = all_added_secret_rhs[jid];
          auto added_secret_vars = all_added_secret_vars[id];
          auto current_secret_vars = Lits2Vars(all_secret_lits[id]);
          auto rhs_watch = new_watch(backup_solvers[k]);
          if (id == jid)
            backup_secret_rhs_watches[id][0] = rhs_watch;
          else
            backup_secret_rhs_watches[id][1] = rhs_watch;
          secret_watch.clear();
          Sample(backup_solvers[k], current_secret_vars, num_xor_cls_,
                 secret_watch, added_secret_vars, secret_rhs, rhs_watch, true);
        }
      }
      // ( h(S1)=r1 && h(S2)=r2 ) or (h(S1)=r2 && h(S2)=r1)
      compose_distinct_secretset(backup_solvers[k], backup_secret_rhs_watches,
                                 use_overlap_coefficient_);
      std::ofstream fff(out_dir_ + "/" + std::to_string(num_xor_cls_) +
                            ".back.cnf" + std::to_string(k),
                        std::ofstream::out);
      backup_solvers[k]->dump_irred_clauses_ind_only(&fff);
      fff.close();
    }
  }
  return after_secret_sample_count(solver, secret_rnd);
}
bool Count::after_secret_sample_count(SATSolver *solver, string secret_rnd) {
  // exit(0);
  cout << "Sample end\n" << std::flush;
  cout << "used_vars.size=" << used_vars.size() << std::endl;
  /*solver->set_sampling_vars(nullptr);
  for(int i=0;i<backup_solvers.size();++i)
    backup_solvers[i]->set_sampling_vars(nullptr);*/
  solver->simplify();

  //  solver->add_clause(secret_watch);
  cout << "count size=" << count_vars.size();
  string trim = trimVar(backup_solvers[0], count_vars);
  unrelated_number_countvars = std::count(trim.begin(), trim.end(), 'u');
  cout << "secret size=" << secret_vars.size() << std::endl;
  cout << "count size=" << count_vars.size()
       << ",unrelated vars=" << unrelated_number_countvars << std::endl;
  if (backup_solvers[0]->solve() == l_False) {
    std::cout << "solve is false" << std::endl;
    return false;
  }
  std::cout << "solve is ok" << std::endl;
  int hash_count = 0;
  int left, right;
  vector<int> backup_left(backup_solvers.size()),
      backup_right(backup_solvers.size()),
      backup_hash_count(backup_solvers.size());
  left = (left_ > -1) ? left_ : ((min_log_size_ == -1) ? 0 : min_log_size_);
  right = (right_ > -1)
              ? right_
              : ((max_log_size_ == -1) ? count_vars.size() : max_log_size_);
  for (size_t i = 0; i < backup_solvers.size(); ++i) {
    backup_left[i] = backup_left_[i] ? backup_left_[i] : left;
    backup_right[i] = backup_right_[i] ? backup_right_[i] : right;
    backup_hash_count[i] = 0;
  }
  map<int, unsigned> solution_counts;
  int max_hash_count = 0;
  vector<int> backup_max_hash_count(backup_right_.size(), 0);
  int max_sol = max_sol_;
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    if (count_times == 0) {
      max_sol_ = 16;
    } else {
      max_sol_ = max_sol;
      left -= floor(max_sol / 2);
      right -= floor(max_sol / 2);
      for (int i = 0; i < backup_solvers.size(); ++i) {
        backup_left[i] -= floor(max_sol / 2);
        backup_right[i] -= floor(max_sol / 2);
      }
    }
    solution_lits.clear();
    solution_strs.clear();
    cout << "=========count for target "
         << "left=" << left << ",right= " << right << "\n\n";
    solution_counts.clear();
    cached_inter_solution.clear();
    solution_counts =
        count_once(solver, count_vars, {}, left, right, hash_count);
    RecordSolution(secret_rnd);
    auto inter_solution_lits = solution_lits;
    auto inter_solution_strs = solution_strs;
    auto prev_count_vars = &count_vars;
    vector<map<int, unsigned>> backup_solution_counts(backup_solvers.size());
    int idx = 0;
    for (size_t i = 0; i < backup_solvers.size(); ++i) {
      cout << "======count for id=" << i << "left=" << backup_left[i]
           << ",right= " << backup_right[i] << "\n\n";
      // auto &current_count_vars = all_count_vars.begin()->second;
      // replace_vars(added_count_lits, *prev_count_vars, current_count_vars);
      backup_solution_counts[i] =
          count_once(backup_solvers[i], count_vars, {}, backup_left[i],
                     backup_right[i], backup_hash_count[i], true);
      RecordSolution(secret_rnd, "." + std::to_string(i));
      backup_max_hash_count[i] =
          std::max(backup_max_hash_count[i], backup_hash_count[i]);
      // prev_count_vars = &current_count_vars;
    }
    calculateDiffSolution(inter_solution_lits, solution_lits,
                          inter_solution_strs, solution_strs, secret_rnd);
    if (inter_mode_ == 0)
      RecordCount(solution_counts, hash_count, secret_rnd);
    else {
      if (count_times > 0)
        RecordCountInter(solution_counts, hash_count, backup_solution_counts,
                         backup_hash_count, secret_rnd);
    }
    max_hash_count = std::max(max_hash_count, hash_count);
  }
  left_ = std::max(0, max_hash_count - 10);
  right_ = std::min(int(count_vars.size()), max_hash_count + 10);
  for (size_t i = 0; i < backup_right_.size(); ++i) {
    backup_left_[i] = std::max(0, backup_max_hash_count[i] - 10);
    backup_right_[i] =
        std::min(int(count_vars.size()), backup_max_hash_count[i] + 10);
  }
  return true;
}

static void RecordHash(string filename,
                       const vector<vector<unsigned>> &added_secret_vars,
                       const vector<bool> &count_rhs) {
  std::ofstream f(filename, std::ofstream::out | std::ofstream::app);
  int i = 0;
  f << "p cnf 1000 " << added_secret_vars.size() << std::endl;
  for (auto xor_lits : added_secret_vars) {
    f << "x" << (count_rhs[i] ? "-" : "");
    for (auto v : xor_lits) {
      f << v + 1 << " ";
    }
    f << " 0\n";
    i++;
  }
  f.close();
}

void Count::simulate_count(SATSolver *solver, vector<unsigned> &secret_vars) {
  solver->set_sampling_vars(&count_vars);
  vector<vector<unsigned>> added_secret_vars;
  vector<Lit> secret_watch;
  vector<bool> secret_rhs;
  // trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n";
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n";
    num_xor_cls_ = secret_vars.size();
  }
  auto rhs_watch = new_watch(solver);
  solver->add_clause({~rhs_watch});
  Sample(solver, secret_vars, num_xor_cls_, secret_watch, added_secret_vars,
         secret_rhs, rhs_watch);
  RecordHash("secret_hash.cnf", added_secret_vars, secret_rhs);
  cout << "Sample end\n";
  //  solver->add_clause(secret_watch);
  // trimVar(solver, count_vars);
  vector<Lit> count_watch;
  // solver->add_clause(secret_watch);
  int hash_count = 0;
  hash_count = max_log_size_;

  vector<vector<unsigned>> added_count_lits;
  vector<bool> count_rhs;
  int pid = -1;
  string secret_cnf = "final_secret_hash.cnf";
  std::ofstream f(secret_cnf, std::ofstream::out);
  solver->dump_irred_clauses_ind_only(&f);
  f.close();
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    if (pid == 0) {
      continue;
    }
    pid = 0;
    pid = fork();
    if (pid != 0) {
      continue;
    }
    SATSolver newsolver(&conf);
    readInAFile(&newsolver, secret_cnf);
    cout << count_times << std::endl;
    added_count_lits.clear();
    count_watch.clear();
    count_rhs.clear();

    Sample(solver, count_vars, hash_count, count_watch, added_count_lits,
           count_rhs, lit_Undef);
    RecordHash("count_hash" + std::to_string(count_times) + ".cnf",
               added_count_lits, count_rhs);
    solver->GetSolver(0)->conf.simplified_cnf =
        "final_count_hash" + std::to_string(count_times) + ".cnf";
    solver->set_preprocess(1);
    solver->solve();
    solver->set_preprocess(0);
  }
}
void Count::setBackupSolvers(vector<SATSolver *> &bs) {
  auto ids = getIDs();
  backup_solvers = bs;
  backup_unused_sampling_vars.clear();
  backup_unused_sampling_vars.resize(2);
  if (inter_mode_) {
    for (int i = 0; i < 2; ++i) {
      symbol_vars.clear();
      sampling_vars.clear();
      readInAFile(backup_solvers[i], filesToRead[0]);
      if (((declassification_mode_ == 0 && i == 1) ||
           (declassification_mode_ == 1 && i == 0)) &&
          all_declass_lits.size()) {
        if (all_declass_lits.count("_2")) {
          cout << "add all_declass_lits[_0], all_declass_lits[_1];"
               << std::endl;
          map<string, vector<Lit>> diff_declass_lits;
          diff_declass_lits["_0"] = all_declass_lits["_0"];
          diff_declass_lits["_1"] = all_declass_lits["_1"];
          AddVariableSame(backup_solvers[i], diff_declass_lits);
        } else
          AddVariableSame(backup_solvers[i], all_declass_lits);
      }
    }
    if (all_declass_lits.size() == 0 || declassification_mode_ == 1) {
      backup_solvers.resize(1);
    }
  }
  backup_left_.resize(backup_solvers.size());
  backup_right_.resize(backup_solvers.size());
  backup_unused_sampling_vars.resize(backup_solvers.size());
}
bool Count::ProbToDiffFromSecretSet() {
  SATSolver s(&conf);
  solver = newCounterSolver(&s, (void *)&conf);
  inputfile = filesToRead[0];
  symbol_vars.clear();
  sampling_vars.clear();
  readInAFile(solver, inputfile);
  setSecretVars();
  setCountVars();

  AddVariableSame(solver, all_observe_lits);
  if (all_declass_lits.size())
    AddVariableSame(solver, all_declass_lits);
  SATSolver bs1(&conf);
  SATSolver bs2(&conf);
  vector<SATSolver *> bs = {newCounterSolver(&bs1, &conf),
                            newCounterSolver(&bs2, &conf)};
  setBackupSolvers(bs);
  return countCISAlt(solver, secret_vars);
}
void Count::run() {
  string target_file = filesToRead[0];
  if (mode_ == "nonblock")
    conf.max_sol_ = max_sol_;
  else {
    conf.max_sol_ = 1;
  }
  if (inter_mode_ == 3) {
    for (int t = 0; t < nsample; ++t) {
      if (ProbToDiffFromSecretSet() == false) {
        t--;
      }
      backup_solvers.resize(0);
    }
    return;
  }
  SATSolver s1(&conf);
  solver = newCounterSolver(&s1, (void *)&conf);
  inputfile = filesToRead[0];
  readInAFileToCache(solver, inputfile);

  if (init_file_.length() > 0)
    readInAFile(solver, init_file_);

  if (symmap_file_.length() > 0) {
    symbol_vars.clear();
    sampling_vars.clear();
    readInAFile(solver, symmap_file_);
  }
  cout << "read model\n";
  if (readVictimModel(solver)) {
    return;
  }
  cout << "end model\n";

  // this will set keep_symbol=0, which means it will keep sampling_var but
  // eliminate symbol
  setSecretVars();
  setCountVars();
  target_file = inputfile;
  /*
  target_file = out_dir_ + "//" + out_file_ + ".tmp";
  std::ofstream finalout(target_file);
  solver->dump_irred_clauses_ind_only(&finalout);
  finalout.close();*/

  if (mode_ == "simulate") {
    if (inter_mode_ == 2) {
      AddVariableSame(solver, all_observe_lits);
      auto ids = getIDs();
      count_vars = all_count_vars[ids[0]];

      /*target_file = out_dir_ + "//" + out_file_ + ".same";
      std::ofstream finalout(target_file);
      solver->dump_irred_clauses_ind_only(&finalout);
      finalout.close();*/
    }
    simulate_count(solver, secret_vars);
  } else {
    clearFlagVars();
    for (int t = 0; t < nsample; ++t) {
      symbol_vars.clear();
      sampling_vars.clear();
      SATSolver ss(&conf);
      // delete solver;
      solver = newCounterSolver(&ss, (void *)&conf);
      readInAFileToCache(solver, target_file);
      std::cerr << "I am here";
      setSecretVars();
      setCountVars();
      /*
            if (inter_mode_ == 1) {
              auto ids = getIDs();
              count_vars = all_count_vars[ids[0]];
              AddVariableDiff(solver, all_observe_lits);
            }*/
      if (inter_mode_ == 2) {
        cout << "AddVariableSame for solver";
        all_observe_lits.erase("_2");
        AddVariableSame(solver, all_observe_lits);
        if (all_declass_lits.size()) {
          if (all_declass_lits.count("_2")) {
            cout << "add all_declass_lits[_0], all_declass_lits[_2];"
                 << std::endl;
            map<string, vector<Lit>> diff_declass_lits;
            diff_declass_lits["_0"] = all_declass_lits["_0"];
            diff_declass_lits["_2"] = all_declass_lits["_2"];
            AddVariableSame(solver, diff_declass_lits);
            if (declassification_mode_ == 1) {
              diff_declass_lits["_1"] = all_declass_lits["_1"];
              diff_declass_lits.erase("_2");
              AddVariableSame(solver, diff_declass_lits);
            }
          } else
            AddVariableSame(solver, all_declass_lits);
        }
        auto ids = getIDs();
        count_vars = all_count_vars[ids[0]];
        cout << "count vars:";
        for (auto v : count_vars) {
          cout << v << "\t";
        }
        cout << std::endl;
      }
      solver->set_up_for_jaccard_count();
      SATSolver bs1(&conf);
      SATSolver bs2(&conf);
      vector<SATSolver *> bs = {newCounterSolver(&bs1, &conf),
                                newCounterSolver(&bs2, &conf)};
      setBackupSolvers(bs);
      std::ofstream finalout("solver.cnf");
      solver->dump_irred_clauses_ind_only(&finalout);
      finalout.close();
      std::cout << "sample once" << std::endl << std::flush;
      if (count(solver, secret_vars) == false) {
        t--;
      }
    }
  }
  /*solver = new SATSolver((void *)&conf);
  parseInAllFiles(solver, filesToRead[0]);*/
}
