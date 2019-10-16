#include "count.h"
#include "src/dimacsparser.h"
#include <boost/lexical_cast.hpp>
#include <iostream>
#include <unordered_map>
using boost::lexical_cast;
using std::cerr;
using std::exit;
using std::map;
using std::ofstream;
using std::unordered_map;
using std::unordered_set;
static void trimVar(SATSolver *solver, vector<uint32_t> &secret_vars) {
  std::unordered_set<uint32_t> fixed_var_set;
  vector<uint32_t> new_secret_vars;
  for (auto lit : solver->get_zero_assigned_lits()) {
    fixed_var_set.insert(lit.var());
  }
  for (auto var : secret_vars) {
    if (fixed_var_set.count(var) > 0)
      continue;
    new_secret_vars.push_back(var);
  }
  std::swap(new_secret_vars, secret_vars);
}
static void trimVar(SATSolver *solver, vector<Lit> &secret_vars) {
  std::unordered_set<uint32_t> fixed_var_set;
  vector<Lit> new_secret_vars;
  for (auto lit : solver->get_zero_assigned_lits()) {
    fixed_var_set.insert(lit.var());
  }
  for (auto lit : secret_vars) {
    if (fixed_var_set.count(lit.var()) > 0)
      continue;
    new_secret_vars.push_back(lit);
  }
  std::swap(new_secret_vars, secret_vars);
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
static string getSSignature(vector<vector<uint32_t>> &added_secret_lits) {
  string sxor = "";
  for (auto x : added_secret_lits) {
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
void Count::RecordCount(int sol, int hash_count,
                        vector<vector<uint32_t>> &added_secret_lits) {
  std::ofstream count_f(out_dir_ + "/" + out_file_ + ".count",
                        std::ofstream::out | std::ofstream::app);

  count_f << sol << "\t" << hash_count << "\t%"
          << getSSignature(added_secret_lits) << "\n";
  count_f.close();
}

void Count::RecordSolution(vector<vector<uint32_t>> &added_secret_lits) {

  if (!record_solution_)
    return;
  std::cout << "start record solution\n";
  std::ofstream solution_f(out_dir_ + "//" + out_file_ + ".sol",
                           std::ofstream::out | std::ofstream::app);
  for (auto lit : solution_lits)
    solution_f << lit << " % " << getSSignature(added_secret_lits) << "\n";
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
  countOptions_.add_options()("max_log_size",
                              po::value(&max_log_size_)->default_value(-1));
  countOptions_.add_options()("count_mode",
                              po::value(&mode_)->default_value("block"),
                              "mode: nonblock-> backtrack, block -> block");
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

void Count::readVictimModel(SATSolver *&solver) {
  std::ifstream vconfig_f;
  if (victim_model_config_.length() == 0)
    return;
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
      cerr << "error victim model: " << line;
      exit(1);
    }
    string name = tokens[1];
    int offset = std::stoi(tokens[2]);
    int size = std::stoi(tokens[3]);
    if (symbol_vars.count(name) == 0) {
      cerr << "not found symbol: " << name;
      exit(1);
    }
    if (!IsValidVictimLabel(tokens[0])) {
      cerr << "Error Victim Label " << tokens[0];
      exit(1);
    }
    if (symbol_vars[name].size() < size) {
      cerr << "Error symbol " << name << " " << symbol_vars[name].size() << " "
           << size << "\n";
      exit(1);
    }
    for (int i = offset; i < offset + size; ++i) {
      victim_model_[tokens[0]].push_back(symbol_vars[name][i].var());
      new_symbol_vars[tokens[0]].push_back(symbol_vars[name][i]);
    }
  }
  solver->set_symbol_vars(&new_symbol_vars);
  for (auto &vars : new_symbol_vars)
    trimVar(solver, vars.second);
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

void Count::Sample(SATSolver *solver, std::vector<uint32_t> vars,
                   int num_xor_cls, vector<Lit> &watch,
                   vector<vector<uint32_t>> &alllits, bool addInner) {
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
      continue;
    } else {
      for (unsigned j = 0; j < vars.size(); j++) {
        if (randomBits[i * vars.size() + j] == '1')
          lits.push_back(vars[j]);
      }
      alllits.push_back(lits);
      // 0 xor 1 = 1, 0 xor 0= 0, thus,we add watch=0 => xor(1,2,4) = r
      if (!addInner)
        lits.push_back(watch[i].var());
      // e.g., xor watch 1 2 4 ..
      solver->add_xor_clause(lits, randomBits_rhs[i] == '1');
    }
  }
}

int64_t Count::bounded_sol_count(SATSolver *&solver, uint32_t maxSolutions,
                                 const vector<Lit> &assumps, bool only_ind) {
  uint64_t solutions = 0;
  lbool ret;
  delete solver;
  solver=new SATSolver(&conf);
  //solver->load_state(conf.saved_state_file);
  symbol_vars.clear();
  sampling_vars.clear();
  readInAFile(solver,conf.simplified_cnf);
  setCountVars();
  solver->set_sampling_vars(&count_vars);
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
      for (const uint32_t var : count_vars) {
        if (solver->get_model()[var] != l_Undef) {
          lits.push_back(Lit(var, solver->get_model()[var] == l_True));
          solution.push_back(Lit(var, solver->get_model()[var] == l_False));
        } else {
          assert(false);
        }
      }
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

void Count::count(SATSolver *solver, vector<uint32_t> &secret_vars) {
  solver->set_sampling_vars(&count_vars);
  vector<vector<uint32_t>> added_secret_lits;
  vector<Lit> secret_watch;
  trimVar(solver, secret_vars);
  cout << "count\n" << solver << ", secret size=" << secret_vars.size();
  cout << "Sample\n";
  if (secret_vars.size() < num_xor_cls_) {
    cerr << "add more xor " << num_xor_cls_ << " than secret var size\n";
    num_xor_cls_ = secret_vars.size();
  }
  Sample(solver, secret_vars, num_xor_cls_, secret_watch, added_secret_lits,
         true);
  cout << "Sample end\n";
  //  solver->add_clause(secret_watch);
  solver->set_preprocess(1);
  solver->simplify();
  trimVar(solver, count_vars);
  cout << "count size=" << count_vars.size();
  solver->solve();
  solver->set_preprocess(0);
  int nsol = bounded_sol_count(solver, max_sol_, secret_watch, true);
  RecordSolution(added_secret_lits);
  cout << "count end\n";
  vector<Lit> count_watch;
  // solver->add_clause(secret_watch);
  int prev_hash_count = 0, hash_count = 0;
  int left = max_log_size_ == -1 ? 1 : max_log_size_ / 2,
      right = max_log_size_ == -1 ? count_vars.size() : max_log_size_;
  vector<vector<uint32_t>> added_count_lits;
  cout << "size=" << count_vars.size() << " " << nsol << "\n";
  if (nsol == -1)
    return;
  cout << "found solution" << nsol << "* 2^" << hash_count;
  if (nsol < max_sol_) {
    RecordCount(nsol, hash_count, added_secret_lits);
    int nsol = bounded_sol_count(solver, max_sol_, secret_watch, true);
    cout << "again found solution" << nsol << "* 2^" << hash_count;
    return;
  }
  if (search_all == false) {
    return;
  }
  unordered_map<int, uint64_t> solution_counts;
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    added_count_lits.clear();
    solution_counts.clear();
    count_watch.clear();
    prev_hash_count = 0;
    vector<Lit> assump;
    solution_lits.clear();
    while (left < right) {
      hash_count = left + (right - left) / 2;
      cout << "starting... hash_count=" << hash_count << "\n";
      Sample(solver, count_vars, hash_count, count_watch, added_count_lits);
      assump.clear();
      assump = secret_watch;
      assump.insert(assump.end(), count_watch.begin(),
                    count_watch.begin() + hash_count);
      cout << assump.size();
      if (!solution_counts.count(hash_count))
        nsol = bounded_sol_count(solver, max_sol_, assump, true);
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
      cout << "hash_count=" << hash_count << ", nsol=" << nsol
           << "left=" << left << "right=" << right << "\n";
      prev_hash_count = hash_count;
    }
    hash_count = right;
    if (!solution_counts.count(hash_count) && hash_count >= 0) {
      solution_counts[hash_count] =
          bounded_sol_count(solver, max_sol_, assump, true);
      // hash_count--;
    }
    while ((!solution_counts.count(hash_count) ||
            solution_counts[hash_count] == 0) &&
           hash_count >= 0) {
      hash_count--;
    }
    cout << "found solution" << solution_counts[hash_count] << "* 2^"
         << hash_count << "\n";
    RecordCount(solution_counts[hash_count], hash_count, added_secret_lits);
    RecordSolution(added_secret_lits);
    left = hash_count - hash_count / 2 - 1;
    right = std::min(int(count_vars.size()), hash_count + hash_count / 2 + 1);
  }
}

void Count::run() {
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
  cerr << "read model\n";
  readVictimModel(solver);
  cerr << "end model\n";

  // this will set keep_symbol=0, which means it will keep sampling_var but
  // eliminate symbol
  solver->set_up_for_jaccard_count();

  vector<uint32_t> secret_vars;
  for (auto lit : symbol_vars[SECRET_]) {
    secret_vars.push_back(lit.var());
  }
  setCountVars();
  cerr << "secret size=" << secret_vars.size();
  cerr << "count size=" << count_vars.size();
  count(solver, secret_vars);

  /*solver = new SATSolver((void *)&conf);
  parseInAllFiles(solver, filesToRead[0]);*/
}

int main(int argc, char **argv) {
  srand(time(NULL));
  Count Count(argc, argv);
  Count.conf.verbosity = 0;
  Count.conf.verbStats = 0;
  Count.conf.preprocess = 0;
  Count.conf.restart_first = 1000000;
  Count.conf.keep_symbol = 1;
  Count.conf.simplified_cnf=".simpfile.cnf";
  // Count.conf.doRenumberVars = true;
  Count.parseCommandLine();
  Count.run();
}
