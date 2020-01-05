#include "count.h"
#include "src/dimacsparser.h"
#include <boost/lexical_cast.hpp>
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
vector<uint32_t> Lits2Vars(vector<Lit> &lits) {
  vector<uint32_t> vars;
  for (auto l : lits) {
    vars.push_back(l.var());
  }
  return vars;
}
void replace_vars(vector<vector<uint32_t>> &added_count_lits,
                  vector<uint32_t> &old_count_vars,
                  vector<uint32_t> &new_count_vars) {
  unordered_map<uint32_t, uint32_t> old_to_new;
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
  string diff_file = out_dir_ + "//" + out_file_ + ".testhash";
  std::ofstream finalout(diff_file);
  for (int i = 0; i < len; ++i) {
    vector<uint32_t> clause;
    auto new_watch = solver->nVars();
    solver->new_var();
    clause.push_back(new_watch);
    watches.push_back(Lit(new_watch, true));
    bool xor_bool = true;
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign())
        xor_bool = ~xor_bool;
    }
    solver->add_xor_clause(clause, xor_bool);
    finalout << "x" << xor_bool ? "" : "-";
    for (auto v : clause)
      finalout << v + 1;
    finalout << "\n";
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
  vector<uint32_t> other_control_vars;
  for (auto name_lits : symbol_vars) {
    if (!name_lits.first.compare(0, CONTROLLED_.length(), CONTROLLED_)) {
      for (auto lit : name_lits.second) {
        // count_vars.push_back(lit.var());
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
    vector<uint32_t> clause;
    bool xor_bool = false;
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign())
        xor_bool = ~xor_bool;
    }
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

static string trimVar(SATSolver *solver, vector<uint32_t> &secret_vars) {
  string ret = "";
  std::unordered_map<uint32_t, string> fixed_var_set;
  vector<uint32_t> new_secret_vars;
  for (auto lit : solver->get_zero_assigned_lits()) {
    fixed_var_set[lit.var()] = lit.sign() ? "0" : "1";
  }
  for (auto var : secret_vars) {
    if (fixed_var_set.count(var) > 0) {
      ret += fixed_var_set[var];
      continue;
    }
    new_secret_vars.push_back(var);
    ret += "x";
  }
  std::swap(new_secret_vars, secret_vars);
  return ret;
}
static string trimVar(SATSolver *solver, vector<Lit> &secret_vars) {
  string ret = "";
  std::unordered_map<uint32_t, string> fixed_var_set;
  vector<Lit> new_secret_vars;
  for (auto lit : solver->get_zero_assigned_lits()) {
    fixed_var_set[lit.var()] = lit.sign() ? "0" : "1";
  }
  for (auto lit : secret_vars) {
    if (fixed_var_set.count(lit.var()) > 0) {
      ret += fixed_var_set[lit.var()];
      continue;
    }
    new_secret_vars.push_back(lit);
    ret += "x";
  }
  std::swap(new_secret_vars, secret_vars);
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
    cout << "\n";
  }
}
static string getSSignature(vector<vector<uint32_t>> &added_secret_vars) {
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
void Count::RecordCount(map<int, uint64_t> &sols, int hash_count, string rnd) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sols[hash_count] << "\t" << hash_count << "\t%" << rnd << "\n";
  count_f.close();
}

void Count::RecordCountInter(map<int, uint64_t> &sols, int hash_count,
                             vector<map<int, uint64_t>> b_sols,
                             vector<int> b_hash_counts, string rnd) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".inter.count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sols[hash_count] << "\t" << hash_count << "\t";
  int norm_sum_sols = 0;
  for (int id = 0; id < b_sols.size(); ++id) {
    int hash = b_hash_counts[id];
    count_f << b_sols[id][hash] << "\t" << hash << "\t";
    norm_sum_sols += b_sols[id][hash] * pow(2, hash - hash_count);
  }
  double j =
      1 - 1.0 * sols[hash_count] / double(norm_sum_sols - sols[hash_count]);
  count_f << std::setprecision(4) << j << "\t%" << rnd << "\n";
  count_f.close();
}

void Count::RecordSolution(string rnd) {

  if (!record_solution_)
    return;
  std::cout << "start record solution\n";
  std::ofstream solution_f(out_dir_ + "//" + out_file_ + ".sol",
                           std::ofstream::out | std::ofstream::app);
  for (auto lit : solution_lits)
    solution_f << lit << " % " << rnd << "\n";
  solution_f.close();
}

void Count::add_count_options() {
  countOptions_.add_options()("cycles", po::value(&cycles_)->default_value(1),
                              "Number of composition cycles.");
  countOptions_.add_options()(
      "victim", po::value(&victim_model_config_)->default_value(""),
      "Victim model config: secret  sym_name offset size\n observe: "
      "(sym_name,offset,size)\n control: (sym_name,offset,size) ");
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
  countOptions_.add_options()("count_mode",
                              po::value(&mode_)->default_value("block"),
                              "mode: nonblock-> backtrack, block -> block");
  countOptions_.add_options()(
      "inter_mode", po::value(&inter_mode_)->default_value(0),
      "true-> secret_1 and secret_2, observe_1 and observe_2, false: single");
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
           << size << "\n";
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

  for (auto &vars : new_symbol_vars) {
    auto values = trimVar(solver, vars.second);
    symbol_tmpf << vars.first << "\t" << values << "\n";
  }
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
  delete solver;
  auto newconf = conf;
  solver = new SATSolver((void *)&newconf);
  symbol_vars.clear();
  sampling_vars.clear();
  readInAFile(solver, victim_cnf_file);
  return true;
  /*
  vector<uint32_t> secret_vars(victim_model_[SECRET_].begin(),
                               victim_model_[SECRET_].end());
  count_vars.insert(count_vars.end(), victim_model_[CONTROLLED_].begin(),
                    victim_model_[CONTROLLED_].end());
  count_vars.insert(count_vars.end(), victim_model_[OBSERVABLE_].begin(),
                    victim_model_[OBSERVABLE_].end());
  count_vars.insert(count_vars.end(), victim_model_[OTHER_].begin(),
                    victim_model_[OTHER_].end());*/
}

string Count::Sample(SATSolver *solver2, std::vector<uint32_t> vars,
                     int num_xor_cls, vector<Lit> &watch,
                     vector<vector<uint32_t>> &alllits, vector<bool> &rhs,
                     Lit addInner, bool is_restarted) {
  double ratio = xor_ratio_;
  if (num_xor_cls * ratio > max_xor_per_var_) {
    ratio = max_xor_per_var_ * 1.0 / num_xor_cls;
    cout << "to many xor... we hope to use at most" << max_xor_per_var_
         << " xor per var, thus change ratio to" << ratio << "\n";
  }
  string randomBits =
      GenerateRandomBits_prob((vars.size()) * num_xor_cls, ratio);
  string randomBits_rhs = GenerateRandomBits(num_xor_cls);
  vector<uint32_t> lits;
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
      for (unsigned j = 0; j < vars.size(); j++) {
        if (randomBits[i * vars.size() + j] == '1')
          lits.push_back(vars[j]);
        if (hashf)
          *hashf << vars[j] + 1 << " ";
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
      for (auto l : lits) {
        cout << l << "\t";
      }
      cout << "\n";
    }

    // e.g., xor watch 1 2 4 ..
    if (lits.size() < 2) {
      continue;
    }

    solver2->add_xor_clause(lits, rhs[i]);
  }
  return randomBits + randomBits_rhs;
}

int64_t Count::bounded_sol_count(SATSolver *solver,
                                 vector<uint32_t> &target_count_vars,
                                 uint32_t maxSolutions,
                                 const vector<Lit> &assumps, bool only_ind) {
  uint64_t solutions = 0;
  lbool ret;
  // solver->load_state(conf.saved_state_file);
  // setCountVars();
  solver->set_sampling_vars(&target_count_vars);
  if (mode_ == "nonblock") {
    vector<Lit> solution;
    ret = solver->solve(&assumps, only_ind);
    for (auto sol_str : solver->get_solutions()) {
      std::stringstream ss(sol_str);
      string token;
      solution.clear();
      while (ss >> token) {
        int int_lit = std::stoi(token);
        uint32_t var = abs(int_lit) - 1;
        solution.push_back(Lit(var, int_lit < 0));
      }
      solution_lits.push_back(solution);
    }
    // delete solver;
    return solver->n_seareched_solutions();
  }
  // Set up things for adding clauses that can later be removed
  vector<lbool> model;
  vector<Lit> new_assumps(assumps);
  solver->new_var();
  uint32_t act_var = solver->nVars() - 1;
  new_assumps.push_back(Lit(act_var, true));
  if (new_assumps.size() > 1)
    solver->simplify(&new_assumps);

  while (solutions < maxSolutions) {
    ret = solver->solve(&new_assumps, only_ind);
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
    solutions += std::max(1, solver->n_seareched_solutions());
    model = solver->get_model();

    if (solutions < maxSolutions) {
      vector<Lit> lits, solution;
      lits.push_back(Lit(act_var, false));
      for (const uint32_t var : target_count_vars) {
        if (solver->get_model()[var] != l_Undef) {
          lits.push_back(Lit(var, solver->get_model()[var] == l_True));
        } else {
          assert(false);
        }
      }
      for (const uint32_t var : target_count_vars) {
        if (solver->get_model()[var] != l_Undef) {
          solution.push_back(Lit(var, solver->get_model()[var] == l_False));
        } else {
          assert(false);
        }
      }
      /*for (const uint32_t var : full_secret_vars) {
        if (solver->get_model()[var] != l_Undef) {
          solution.push_back(Lit(var, solver->get_model()[var] == l_False));
        }else{
          assert(false);
        }
      }*/
      if (conf.verbosity > 1) {
        cout << "====result==="
             << "\n";
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
          cout << "\n";
        }
        cout << std::setbase(10);
        cout << std::setbase(10);
        cout << "[appmc] Adding banning clause: " << lits << endl;
      }
      solver->add_clause(lits);
      if (record_solution_)
        solution_lits.push_back(solution);
    }
    solutions += solver->n_seareched_solutions();
  }
  // Remove clauses added
  vector<Lit> cl_that_removes;
  cl_that_removes.push_back(Lit(act_var, false));
  solver->add_clause(cl_that_removes);

  assert(ret != l_Undef);
  return solutions;
}
map<int, uint64_t> Count::count_once(SATSolver *solver,
                                     vector<uint32_t> &target_count_vars,
                                     const vector<Lit> &secret_watch, int &left,
                                     int &right, int &hash_count,
                                     bool reserve_xor) {
  int nsol = 0;
  /*vector<vector<uint32_t>> added_count_lits;
  vector<bool> count_rhs;
  vector<Lit> count_watch;*/
  if (!reserve_xor) {
    added_count_lits.clear();
    count_rhs.clear();
    count_watch.clear();
  } else {
    count_watch.clear();
    Sample(solver, target_count_vars, added_count_lits.size(), count_watch,
           added_count_lits, count_rhs, lit_Undef, true);
  }

  map<int, uint64_t> solution_counts;
  int prev_hash_count = 0;
  vector<Lit> assump;
  solution_lits.clear();
  cout << "target count size" << target_count_vars.size() << std::endl;
  if (left <= 0) {
    nsol = bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    if (nsol < max_sol_) {
      left = right = hash_count = 0;
      solution_counts[0] = nsol;
      cout << "found solution" << nsol << "no need xor\n";
    }
  }
  hash_count = left;
  while (left < right) {
    hash_count = left + (right - left) / 2;
    cout << "starting... hash_count=" << hash_count << std::endl << std::flush;
    std::ofstream hash_f(hash_file, std::ofstream::out);
    Sample(solver, target_count_vars, hash_count, count_watch, added_count_lits,
           count_rhs, lit_Undef);
    assump.clear();
    // assump = secret_watch;
    assump.insert(assump.end(), count_watch.begin(),
                  count_watch.begin() + hash_count);
    if (!solution_counts.count(hash_count))
      nsol =
          bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    else
      nsol = solution_counts[hash_count];
    if (nsol >= max_sol_) {
      left = hash_count + 1;
    } else if (nsol < max_sol_ * 0.6) {
      right = hash_count;
      if (nsol > 0)
        left = std::max(left, hash_count - int(2 + log2(max_sol_ / nsol)));
    } else {
      right = hash_count;
      left = hash_count;
    }
    solution_counts[hash_count] = nsol;
    cout << "hash_count=" << hash_count << ", nsol=" << nsol << "left=" << left
         << "right=" << right << "sol=" << nsol << "\n";
    prev_hash_count = hash_count;
  }
  hash_count = right;
  if (!solution_counts.count(hash_count) && hash_count >= 0) {
    solution_counts[hash_count] =
        bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    // hash_count--;
  }
  while ((!solution_counts.count(hash_count) ||
          solution_counts[hash_count] == 0) &&
         hash_count > 0) {
    hash_count--;
  }
  left = std::max(0, hash_count - std::min(5, (hash_count + 1) / 2));
  right = std::min(int(target_count_vars.size()),
                   hash_count + std::min(5, (hash_count + 1) / 2));
  cout << "found solution" << solution_counts[hash_count] << "* 2^"
       << hash_count << "\n";
  return solution_counts;
}

vector<uint32_t> Count::getCISAlt() {
  vector<uint32_t> ret;
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
bool Count::countCISAlt(SATSolver *solver, vector<uint32_t> &secret_vars) {
  count_vars = getCISAlt();
  // when in declassification mode, backup_solvers.size()=2; when in normal
  // mode, backup_solvers.size()=1
  vector<vector<uint32_t>> backup_count_vars(backup_solvers.size());
  for (int i = 0; i < backup_solvers.size(); ++i) {
    backup_count_vars[i] = getCISAlt();
    backup_solvers[i]->set_sampling_vars(&backup_count_vars[i]);
  }
  solver->set_sampling_vars(&count_vars);

  vector<vector<uint32_t>> added_secret_vars;
  map<string, vector<vector<uint32_t>>> backup_added_secret_vars;
  map<string, vector<bool>> backup_added_secret_rhs;
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
  map<uint32_t, int> var_index;
  string id = "_0";
  vector<uint32_t> current_secret_vars, alt_secret_vars;
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
  auto rhs_watch = Lit(solver->nVars(), false);
  solver->new_var();
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

  trimVar(solver, count_vars);
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
  vector<int> backup_left(backup_solvers.size()),
      backup_right(backup_solvers.size()),
      backup_hash_count(backup_solvers.size());
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
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    solution_lits.clear();
    cout << "=========count for target "
         << "left=" << left << ",right= " << right << "\n\n";
    map<int, uint64_t> solution_counts =
        count_once(solver, count_vars, {}, left, right, hash_count);
    RecordSolution(secret_rnd);
    auto prev_count_vars = &count_vars;
    vector<map<int, uint64_t>> backup_solution_counts(backup_solvers.size());
    int idx = 0;
    for (int i = 0; i < backup_solvers.size(); ++i) {
      cout << "======count for id=" << i << "left=" << backup_left[i]
           << ",right= " << backup_right[i] << "\n\n";
      backup_solution_counts[i] = count_once(
          backup_solvers[i], backup_count_vars[i], {}, backup_left[i],
          backup_right[i], backup_hash_count[i], true);
    }
    if (inter_mode_ == 0)
      RecordCount(solution_counts, hash_count, secret_rnd);
    else {
      RecordCountInter(solution_counts, hash_count, backup_solution_counts,
                       backup_hash_count, secret_rnd);
    }
  }
  left_ = left;
  right_ = right_;
  for (size_t i = 0; i < backup_right_.size(); ++i) {
    backup_left_[i] = backup_left[i] - 3;
    backup_right_[i] = backup_right[i] + 3;
  }
  return true;
}

bool Count::count(SATSolver *solver, vector<uint32_t> &secret_vars) {
  solver->set_sampling_vars(&count_vars);
  vector<vector<uint32_t>> added_secret_vars;
  map<string, vector<vector<uint32_t>>> backup_added_secret_vars;
  map<string, vector<bool>> backup_added_secret_rhs;
  vector<Lit> secret_watch;
  vector<bool> secret_rhs;
  string secret_rnd = "";
  trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n" << std::flush;
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n"
         << std::flush;
    num_xor_cls_ = secret_vars.size();
  }
  if (inter_mode_) {
    set<vector<bool>> secret_rhs_set;
    map<uint32_t, int> var_index;
    for (auto id_lits : all_secret_lits) {
      vector<uint32_t> current_secret_vars;
      string id = id_lits.first;
      int offset = 0;
      current_secret_vars.clear();
      for (auto lit : id_lits.second) {
        current_secret_vars.push_back(lit.var());
        var_index[lit.var()] = offset;
        offset++;
      }
      // when one secret set is selcted, we should generate another set using
      // same hash but with different rhs to ensure disjoint sets.
      while (secret_rhs.size() > 0) {
        for (int i = 0; i < secret_rhs.size(); ++i) {
          secret_rhs[i] = (rand() % 2) ? true : false;
        }
        for (auto &added_vars : added_secret_vars) {
          // replace var from secret_1 to secret_2
          for (auto &var : added_vars) {
            var = current_secret_vars[var_index[var]];
          }
        }
        if (secret_rhs_set.count(secret_rhs) == 0) {
          break;
        } else {
          secret_rhs[0] = !secret_rhs[0];
          break;
        }
      }
      auto rhs_watch = Lit(solver->nVars(), false);
      solver->new_var();
      // assert h(Si)=ri;

      secret_watch.clear();
      secret_rnd +=
          Sample(solver, current_secret_vars, num_xor_cls_, secret_watch,
                 added_secret_vars, secret_rhs, rhs_watch, true);
      solver->add_clause({~rhs_watch});
      backup_added_secret_vars[id] = added_secret_vars;
      backup_added_secret_rhs[id] = secret_rhs;
      cout << "secret_" << id_lits.first << " add secret xor:\n" << std::flush;
      for (auto &vars : added_secret_vars) {
        for (auto var : vars)
          cout << var << "\t";
        cout << secret_rhs[0] << "\n";
      }

      secret_rhs_set.insert(secret_rhs);
    }
    std::ofstream ff("inter.cnf", std::ofstream::out);

    solver->dump_irred_clauses_ind_only(&ff);
    ff.close();
    // exit(1);
    for (int i = 0; i < backup_solvers.size(); ++i) {
      cout << "sample for id" << i << "\n";
      vector<Lit> rhs_watchs;
      rhs_watchs.clear();
      for (auto id_added_secret_vars : backup_added_secret_vars) {
        auto id = id_added_secret_vars.first;
        auto added_secret_vars = id_added_secret_vars.second;
        auto current_secret_vars = Lits2Vars(all_secret_lits[id]);
        for (auto id_backup_added_secret_rhs : backup_added_secret_rhs) {
          auto secret_rhs = id_backup_added_secret_rhs.second;
          auto rhs_watch = Lit(backup_solvers[i]->nVars(), false);
          rhs_watchs.push_back(rhs_watch);
          backup_solvers[i]->new_var();
          secret_watch.clear();
          Sample(backup_solvers[i], current_secret_vars, num_xor_cls_,
                 secret_watch, added_secret_vars, secret_rhs, rhs_watch, true);
        }
      }
      // ( h(S1)=r1 && h(S2)=r2 ) or (h(S1)=r2 && h(S2)=r1)
      auto choice1 = Lit(backup_solvers[i]->nVars(), true);
      auto choice2 = Lit(choice1.var() + 1, true);
      backup_solvers[i]->new_vars(2);
      backup_solvers[i]->add_clause({~rhs_watchs[0], choice1});
      backup_solvers[i]->add_clause({~rhs_watchs[3], choice1});
      backup_solvers[i]->add_clause({~rhs_watchs[1], choice2});
      backup_solvers[i]->add_clause({~rhs_watchs[2], choice2});
      backup_solvers[i]->add_xor_clause({choice2.var(), choice1.var()}, true);
      cout << ~rhs_watchs[0] << "," << choice1;
      cout << ~rhs_watchs[3] << "," << choice1;
      cout << ~rhs_watchs[1] << "," << choice2;
      cout << ~rhs_watchs[2] << "," << choice2;

      // backup_solvers[i]->simplify();
      /*std::ofstream f("backup" + std::to_string(i) + ".cnf",
                      std::ofstream::out);
      backup_solvers[i]->dump_irred_clauses_ind_only(&f);
      f.close();*/

      // assert h(S1)!= h(S2)
    }
  } else {
    auto rhs_watch = Lit(solver->nVars(), false);
    solver->new_var();
    solver->add_clause({~rhs_watch});
    secret_rnd = Sample(solver, secret_vars, num_xor_cls_, secret_watch,
                        added_secret_vars, secret_rhs, rhs_watch);
  }
  // exit(0);
  cout << "Sample end\n" << std::flush;
  //  solver->add_clause(secret_watch);
  trimVar(solver, count_vars);
  solver->simplify();
  int hash_count = 0;
  int left, right;
  vector<int> backup_left(backup_solvers.size()),
      backup_right(backup_solvers.size()),
      backup_hash_count(backup_solvers.size());
  left = left_ ? left_ : ((min_log_size_ == -1) ? 0 : min_log_size_);
  right = right_ ? right_
                 : ((max_log_size_ == -1) ? count_vars.size() : max_log_size_);
  for (int i = 0; i < backup_solvers.size(); ++i) {
    backup_left[i] = backup_left_[i] ? backup_left_[i] : left;
    backup_right[i] = backup_right_[i] ? backup_right_[i] : count_vars.size();
    backup_hash_count[i] = 0;
  }
  if (solver->solve() == l_False) {
    return false;
  }
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    solution_lits.clear();
    cout << "=========count for target "
         << "left=" << left << ",right= " << right << "\n\n";
    map<int, uint64_t> solution_counts =
        count_once(solver, count_vars, {}, left, right, hash_count);
    RecordSolution(secret_rnd);
    auto prev_count_vars = &count_vars;
    vector<map<int, uint64_t>> backup_solution_counts(backup_solvers.size());
    int idx = 0;
    for (int i = 0; i < backup_solvers.size(); ++i) {
      cout << "======count for id=" << i << "left=" << backup_left[i]
           << ",right= " << backup_right[i] << "\n\n";
      // auto &current_count_vars = all_count_vars.begin()->second;
      // replace_vars(added_count_lits, *prev_count_vars, current_count_vars);
      backup_solution_counts[i] =
          count_once(backup_solvers[i], count_vars, {}, backup_left[i],
                     backup_right[i], backup_hash_count[i], true);
      // prev_count_vars = &current_count_vars;
    }
    if (inter_mode_ == 0)
      RecordCount(solution_counts, hash_count, secret_rnd);
    else {
      RecordCountInter(solution_counts, hash_count, backup_solution_counts,
                       backup_hash_count, secret_rnd);
    }
  }
  left_ = left;
  right_ = right_;
  for (size_t i = 0; i < backup_right_.size(); ++i) {
    backup_right_[i] = backup_right[i] - 2;
    backup_left_[i] = backup_left[i] + 2;
  }
  return true;
}

static void RecordHash(string filename,
                       const vector<vector<uint32_t>> &added_secret_vars,
                       const vector<bool> &count_rhs) {
  std::ofstream f(filename, std::ofstream::out | std::ofstream::app);
  int i = 0;
  f << "p cnf 1000 " << added_secret_vars.size() << "\n";
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

void Count::simulate_count(SATSolver *solver, vector<uint32_t> &secret_vars) {
  solver->set_sampling_vars(&count_vars);
  vector<vector<uint32_t>> added_secret_vars;
  vector<Lit> secret_watch;
  vector<bool> secret_rhs;
  trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n";
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n";
    num_xor_cls_ = secret_vars.size();
  }
  auto rhs_watch = Lit(solver->nVars(), false);
  solver->new_var();
  solver->add_clause({~rhs_watch});
  Sample(solver, secret_vars, num_xor_cls_, secret_watch, added_secret_vars,
         secret_rhs, rhs_watch);
  RecordHash("secret_hash.cnf", added_secret_vars, secret_rhs);
  cout << "Sample end\n";
  //  solver->add_clause(secret_watch);
  trimVar(solver, count_vars);
  vector<Lit> count_watch;
  // solver->add_clause(secret_watch);
  int prev_hash_count = 0, hash_count = 0;
  hash_count = max_log_size_;

  vector<vector<uint32_t>> added_count_lits;
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
    cout << count_times << "\n";
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
void Count::setBackupSolvers() {
  auto ids = getIDs();
  backup_solvers.resize(0);
  backup_solvers.resize(2);
  if (inter_mode_) {
    for (int i = 0; i < 2; ++i) {
      symbol_vars.clear();
      sampling_vars.clear();
      if (backup_solvers[i] != nullptr) {
        delete backup_solvers[i];
      }
      backup_solvers[i] = (new SATSolver((void *)&conf));
      readInAFile(backup_solvers[i], filesToRead[0]);
      backup_solvers[i]->set_up_for_jaccard_count();
      if (i == 1 && all_declass_lits.size())
        AddVariableSame(backup_solvers[i], all_declass_lits);
      if (all_declass_lits.size() == 0) {
        backup_solvers.resize(1);
      }
    }
  }
  backup_left_.resize(backup_solvers.size());
  backup_right_.resize(backup_solvers.size());
}
bool Count::ProbToDiffFromSecretSet() {
  solver = new SATSolver((void *)&conf);
  inputfile = filesToRead[0];
  symbol_vars.clear();
  sampling_vars.clear();
  readInAFile(solver, inputfile);
  setSecretVars();
  setCountVars();
  AddVariableSame(solver, all_observe_lits);
  if (all_declass_lits.size())
    AddVariableSame(solver, all_declass_lits);
  setBackupSolvers();
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
  solver = new SATSolver((void *)&conf);
  inputfile = filesToRead[0];
  readInAFile(solver, inputfile);

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

  cout << "secret size=" << secret_vars.size();
  cout << "count size=" << count_vars.size();

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
      delete solver;
      solver = new SATSolver((void *)&conf);
      readInAFile(solver, target_file);
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
        AddVariableSame(solver, all_observe_lits);
        if (all_declass_lits.size())
          AddVariableSame(solver, all_declass_lits);
        auto ids = getIDs();
        count_vars = all_count_vars[ids[0]];
      }
      solver->set_up_for_jaccard_count();
      setBackupSolvers();
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
