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

void Count::AddVariableSame(SATSolver *solver,
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
    finalout << "x" << xor_bool ? "" : "-";
    for (auto v : clause)
      finalout << (v + 1) << " ";
    finalout << "\n";
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
                             map<string, map<int, uint64_t>> b_sols,
                             map<string, int> b_hash_counts, string rnd) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".inter.count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sols[hash_count] << "\t" << hash_count << "\t";
  for (auto id_sols : b_sols) {
    auto id = id_sols.first;
    int hash = b_hash_counts[id];
    count_f << id_sols.second[hash] << "\t" << hash << "\t";
  }
  count_f << "%" << rnd << "\n";
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

string Count::Sample(SATSolver *solver, std::vector<uint32_t> vars,
                     int num_xor_cls, vector<Lit> &watch,
                     vector<vector<uint32_t>> &alllits, vector<bool> &rhs,
                     bool addInner, bool is_restarted) {
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
  assert(addInner || watch.size() == alllits.size());
  if (!addInner && watch.size() < num_xor_cls) {

    int diff = num_xor_cls - watch.size();
    int base = watch.size();
    watch.resize(num_xor_cls);
    for (int i = 0; i < diff; ++i) {
      watch[base + i] = Lit(solver->nVars() + i, false);
    }
    solver->new_vars(diff);
  }
  for (int i = 0; i < num_xor_cls; ++i) {
    lits.clear();
    if (alllits.size() > i) {
      // reuse generated xor lits;
      // lits = alllits[i];
      if (is_restarted) {
        auto lit = alllits[i];
        if (!addInner) {
          if (watch[i].var() >= solver->nVars()) {
            cout << "new var for watch";
            solver->new_vars(watch[i].var() - solver->nVars() + 1);
          }
          lits.push_back(watch[i].var());
        }
        solver->add_xor_clause(lits, rhs[i]);
      }
      continue;
    } else {
      for (unsigned j = 0; j < vars.size(); j++) {
        if (randomBits[i * vars.size() + j] == '1')
          lits.push_back(vars[j]);
        if (hashf)
          *hashf << vars[j] + 1 << " ";
      }
      alllits.push_back(lits);
      rhs.push_back(randomBits_rhs[i] == '1');
      // 0 xor 1 = 1, 0 xor 0= 0, thus,we add watch=0 => xor(1,2,4) = r
      if (!addInner) {
        if (watch[i].var() >= solver->nVars()) {
          cout << "new var for watch";
          solver->new_vars(watch[i].var() - solver->nVars() + 1);
        }
        lits.push_back(watch[i].var());
      }
      // e.g., xor watch 1 2 4 ..
      solver->add_xor_clause(lits, randomBits_rhs[i] == '1');
    }
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
                                     int &right, int &hash_count) {
  int nsol = 0;
  vector<vector<uint32_t>> added_count_lits;
  vector<bool> count_rhs;
  vector<Lit> count_watch;
  map<int, uint64_t> solution_counts;
  int prev_hash_count = 0;
  vector<Lit> assump;
  solution_lits.clear();
  if (left <= 0) {
    nsol = bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    if (nsol < max_sol_) {
      left = right = hash_count = 0;
      solution_counts[0] = nsol;
    }
  }
  while (left < right) {
    hash_count = left + (right - left) / 2;
    cout << "starting... hash_count=" << hash_count << "\n";
    std::ofstream hash_f(hash_file, std::ofstream::out);
    Sample(solver, target_count_vars, hash_count, count_watch, added_count_lits,
           count_rhs, false);
    assump.clear();
    assump = secret_watch;
    assump.insert(assump.end(), count_watch.begin(),
                  count_watch.begin() + hash_count);
    if (!solution_counts.count(hash_count))
      nsol =
          bounded_sol_count(solver, target_count_vars, max_sol_, assump, true);
    else
      nsol = solution_counts[hash_count];
    if (nsol >= max_sol_) {
      left = hash_count + 1;
    } else if (nsol < max_sol_ * 0.8) {
      right = hash_count;
      if (nsol > 0)
        left = std::max(left, hash_count - int(2 + log2(max_sol_ / nsol)));
    } else {
      right = hash_count;
      left = hash_count;
    }
    solution_counts[hash_count] = nsol;
    cout << "hash_count=" << hash_count << ", nsol=" << nsol << "left=" << left
         << "right=" << right << "\n";
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
         hash_count >= 0) {
    hash_count--;
  }
  left = std::max(0, hash_count - (hash_count + 1) / 2);
  right = std::min(int(target_count_vars.size()),
                   hash_count + (hash_count + 1) / 2);
  cout << "found solution" << solution_counts[hash_count] << "* 2^"
       << hash_count << "\n";
  return solution_counts;
}

void Count::count(SATSolver *solver, vector<uint32_t> &secret_vars) {
  solver->set_sampling_vars(&count_vars);
  vector<vector<uint32_t>> added_secret_vars;
  map<string, vector<vector<uint32_t>>> backup_added_secret_vars;
  vector<Lit> secret_watch;
  map<string, vector<Lit>> backup_secret_watch;
  vector<bool> secret_rhs;
  string secret_rnd = "";
  trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n";
  if (secret_vars.size() < num_xor_cls_) {
    cout << "add more xor " << num_xor_cls_ << " than secret var size\n";
    num_xor_cls_ = secret_vars.size();
  }
  if (inter_mode_) {
    set<vector<bool>> secret_rhs_set;
    map<uint32_t, int> var_index;
    for (auto id_lits : all_secret_vars) {
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
        if (secret_rhs_set.count(secret_rhs) != 0) {
          break;
        } else {
          secret_rhs[0] = !secret_rhs[0];
          break;
        }
      }
      secret_rnd += Sample(solver, current_secret_vars, num_xor_cls_,
                           secret_watch, added_secret_vars, secret_rhs, true);
      Sample(backup_solvers[id], current_secret_vars, num_xor_cls_,
             backup_secret_watch[id], backup_added_secret_vars[id], secret_rhs,
             true);
      cout << "secret_" << id_lits.first << " add secret xor:\n";
      for (auto &vars : added_secret_vars) {
        for (auto var : vars)
          cout << var << "\t";
        cout << "\n";
      }
      secret_rhs_set.insert(secret_rhs);
    }
  } else
    secret_rnd = Sample(solver, secret_vars, num_xor_cls_, secret_watch,
                        added_secret_vars, secret_rhs, true);

  cout << "Sample end\n";
  //  solver->add_clause(secret_watch);
  trimVar(solver, count_vars);
  solver->simplify();
  int hash_count = 0;
  int left, right;
  map<string, int> backup_left, backup_right, backup_hash_count;
  left = (max_log_size_ == -1) ? 1 : max_log_size_ / 2;
  right = (max_log_size_ == -1) ? count_vars.size() - log2(max_sol_)
                                : max_log_size_;
  for (auto id_solver : backup_solvers) {
    auto id = id_solver.first;
    backup_left[id] = left;
    backup_right[id] = right;
    backup_hash_count[id] = 0;
  }
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    solution_lits.clear();
    cout << "=========count for target "
         << "left=" << left << ",right= " << right << "\n\n";
    map<int, uint64_t> solution_counts =
        count_once(solver, count_vars, secret_watch, left, right, hash_count);
    RecordSolution(secret_rnd);
    map<string, map<int, uint64_t>> backup_solution_counts;
    for (auto id_solver : backup_solvers) {
      auto id = id_solver.first;
      cout << "======count for id=" << id << "left=" << backup_left[id]
           << ",right= " << backup_right[id] << "\n\n";
      backup_solution_counts[id] = count_once(
          backup_solvers[id], all_count_vars[id], backup_secret_watch[id],
          backup_left[id], backup_right[id], backup_hash_count[id]);
    }

    if (inter_mode_ == 0)
      RecordCount(solution_counts, hash_count, secret_rnd);
    else {
      RecordCountInter(solution_counts, hash_count, backup_solution_counts,
                       backup_hash_count, secret_rnd);
    }
  }
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
  Sample(solver, secret_vars, num_xor_cls_, secret_watch, added_secret_vars,
         secret_rhs, true);
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
           count_rhs, true);
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
  if (inter_mode_) {
    for (int i = 0; i < 2; ++i) {
      symbol_vars.clear();
      sampling_vars.clear();
      if(backup_solvers[ids[i]]!=nullptr){
        delete backup_solvers[ids[i]];
      }
      backup_solvers[ids[i]] = (new SATSolver((void *)&conf));
      readInAFile(backup_solvers[ids[i]], filesToRead[0]);
    }
  }
}

void Count::run() {
  string target_file = filesToRead[0];
  if (mode_ == "nonblock")
    conf.max_sol_ = max_sol_;
  else {
    conf.max_sol_ = 1;
  }
  solver = new SATSolver((void *)&conf);
  readInAFile(solver, filesToRead[0]);

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
  solver->set_up_for_jaccard_count();
  setSecretVars();
  /*vector<uint32_t> secret_vars;
  for (auto lit : symbol_vars[SECRET_]) {
    secret_vars.push_back(lit.var());
  }*/
  setCountVars();

  /*if(inter_mode_>0)
    AddVariableDiff(solver,all_secret_vars);*/
  if (inter_mode_ == 1) {
    AddVariableDiff(solver, all_observe_lits);
    target_file = out_dir_ + "//" + out_file_ + ".diff";
    std::ofstream finalout(target_file);
    solver->dump_irred_clauses_ind_only(&finalout);
    finalout.close();
  }
  if (inter_mode_ == 2) {
    AddVariableSame(solver, all_observe_lits);
    auto ids = getIDs();
    count_vars = all_count_vars[ids[0]];
    target_file = out_dir_ + "//" + out_file_ + ".same";
    std::ofstream finalout(target_file);
    solver->dump_irred_clauses_ind_only(&finalout);
    finalout.close();
  }
  cout << "secret size=" << secret_vars.size();
  cout << "count size=" << count_vars.size();

  if (mode_ == "simulate") {
    simulate_count(solver, secret_vars);
  } else {
    for (int t = 0; t < nsample; ++t) {
      symbol_vars.clear();
      sampling_vars.clear();
      delete solver;
      solver = new SATSolver((void *)&conf);
      readInAFile(solver, target_file);
      solver->set_up_for_jaccard_count();
      setBackupSolvers();
      count(solver, secret_vars);
    }
  }
  /*solver = new SATSolver((void *)&conf);
  parseInAllFiles(solver, filesToRead[0]);*/
}

int main(int argc, char **argv) {
  srand(time(NULL));
  Count Count(argc, argv);
  Count.conf.verbStats = 0;
  Count.conf.preprocess = 0;
  Count.conf.restart_first = 1000000;
  Count.conf.keep_symbol = 1;
  Count.conf.simplified_cnf = ".simpfile.cnf";
  // Count.conf.doRenumberVars = true;
  Count.parseCommandLine();
  Count.run();
}
