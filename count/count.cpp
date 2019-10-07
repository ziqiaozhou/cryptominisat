#include "count.h"
#include "src/dimacsparser.h"
#include <boost/lexical_cast.hpp>
#include <iostream>
#include <unordered_map>
using boost::lexical_cast;
using std::cerr;
using std::exit;
using std::ofstream;
using std::unordered_map;
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

void Count::add_count_options() {
  countOptions_.add_options()("cycles", po::value(&cycles_)->default_value(1),
                              "Number of composition cycles.");
  countOptions_.add_options()(
      "victim", po::value(&victim_model_config_)->default_value("victim.conf"),
      "Victim model config: secret  sym_name offset size\n observe: "
      "(sym_name,offset,size)\n control: (sym_name,offset,size) ");
  countOptions_.add_options()("symmap",
                              po::value(&symmap_file_)->default_value(""),
                              "Initilization constraint file.");
  countOptions_.add_options()("count_out",
                              po::value(&out_file_)->default_value("out"),
                              "Countd filename.");
  countOptions_.add_options()("out",
                              po::value(&out_dir_)->default_value("tmp"));
  countOptions_.add_options()("xor_ratio",
                              po::value(&xor_ratio_)->default_value(0.5));
  countOptions_.add_options()("num_xor_cls",
                              po::value(&num_xor_cls_)->default_value(1));
  countOptions_.add_options()("max_sol",
                              po::value(&max_sol_)->default_value(1));
  countOptions_.add_options()("max_count_times",
                              po::value(&max_count_times_)->default_value(10));
  countOptions_.add_options()(
      "Count_mode", po::value(&mode_)->default_value("inc"),
      "mode: inc-> incrementally Count multicycle condition; copy: add a "
      "copy of instance; noninterference: add a copy of instance and add "
      "noninterference constraint");
  help_options_simple.add(countOptions_);
  help_options_complicated.add(countOptions_);
}
void Count::add_supported_options() {
  Main::add_supported_options();
  add_count_options();
}
void Count::readVictimModel() {
  std::ifstream vconfig_f;
  vconfig_f.open(victim_model_config_);
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
    for (int i = offset; i < offset + size; ++i) {
      victim_model_[tokens[0]].insert(symbol_vars[name][i].var());
    }
  }
}
void Count::Sample(SATSolver *solver, std::vector<uint32_t> vars,
                   int num_xor_cls, vector<Lit> &watch,
                   vector<vector<uint32_t>> &alllits) {
  string randomBits =
      GenerateRandomBits_prob((vars.size()) * num_xor_cls, xor_ratio_);
  string randomBits_rhs = GenerateRandomBits(num_xor_cls);
  vector<uint32_t> lits;
  // assert watch=0;
  if (watch.size() < num_xor_cls) {

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
      lits = alllits[i];
    } else {
      for (unsigned j = 0; j < vars.size(); j++) {
        if (randomBits[i * vars.size() + j] == '1')
          lits.push_back(vars[j]);
      }
    }
    alllits.push_back(lits);

    // 0 xor 1 = 1, 0 xor 0= 0, thus,we add watch=0 => xor(1,2,4) = r
    lits.push_back(watch[i].var());
    // e.g., xor watch 1 2 4 ..
    solver->add_xor_clause(lits, randomBits_rhs[i] == '1');
  }
}
static void RecordCount(int sol, int hash_count, ofstream *count_f) {
  *count_f << sol << "\t" << hash_count << "\n";
}
int64_t Count::bounded_sol_count(SATSolver *solver, uint32_t maxSolutions,
                                 const vector<Lit> &assumps, bool only_ind) {

  // Set up things for adding clauses that can later be removed
  vector<lbool> model;
  vector<Lit> new_assumps(assumps);
  solver->new_var();
  uint32_t act_var = solver->nVars() - 1;
  new_assumps.push_back(Lit(act_var, true));
  // solver->simplify(&new_assumps);

  uint64_t solutions = 0;
  lbool ret;
  while (solutions < maxSolutions) {
    ret = solver->solve(&new_assumps, only_ind);
    assert(ret == l_False || ret == l_True);

    if (conf.verbosity >= 2) {
      cout << "[appmc] bounded_sol_count ret: " << std::setw(7) << ret;
      if (ret == l_True) {
        cerr << " sol no.  " << std::setw(3) << solutions;
      } else {
        cout << " No more. " << std::setw(3) << "";
      }
    }

    if (ret != l_True) {
      break;
    }
    model = solver->get_model();

    if (solutions < maxSolutions) {
      vector<Lit> lits;
      lits.push_back(Lit(act_var, false));
      for (const uint32_t var : count_vars) {
        if (solver->get_model()[var] != l_Undef) {
          lits.push_back(Lit(var, solver->get_model()[var] == l_True));
        } else {
          assert(false);
        }
      }
      if (conf.verbosity > 0) {
        cout << "[appmc] Adding banning clause: " << lits << endl;
      }
      solver->add_clause(lits);
    }
    solutions++;
  }
  // Remove clauses added
  vector<Lit> cl_that_removes;
  cl_that_removes.push_back(Lit(act_var, false));
  solver->add_clause(cl_that_removes);

  assert(ret != l_Undef);
  return solutions;
}
void Count::run() {
  solver = new SATSolver((void *)&conf);
  readInAFile(solver, filesToRead[0]);
  readInAFile(solver, symmap_file_);
  readVictimModel();
  std::ofstream count_f(out_file_);
  vector<uint32_t> secret_vars(victim_model_[SECRET_].begin(),
                               victim_model_[SECRET_].end());
  count_vars.insert(count_vars.end(), victim_model_[CONTROLLED_].begin(),
                    victim_model_[CONTROLLED_].end());
  count_vars.insert(count_vars.end(), victim_model_[OBSERVABLE_].begin(),
                    victim_model_[OBSERVABLE_].end());
  count_vars.insert(count_vars.end(), victim_model_[OTHER_].begin(),
                    victim_model_[OTHER_].end());
  count(solver, secret_vars, count_vars, &count_f);
  solver = new SATSolver((void *)&conf);
  readInAFile(solver, filesToRead[0]);
}
void Count::count(SATSolver *solver, vector<uint32_t> secret_vars,
           vector<uint32_t> count_vars, std::ofstream *count_f) {
  solver->set_independent_vars(&count_vars);
  vector<vector<uint32_t>> added_secret_lits;
  vector<Lit> secret_watch;
  Sample(solver, secret_vars, num_xor_cls_, secret_watch, added_secret_lits);
  //  solver->add_clause(secret_watch);
  int nsol = bounded_sol_count(solver, max_sol_, secret_watch, true);
  vector<Lit> count_watch;
  int prev_hash_count = 0, hash_count = 0;
  int left = 0, right = count_vars.size();
  vector<vector<uint32_t>> added_count_lits;
  cout << "size=" << count_vars.size() << " " << nsol << "\n";
  if (nsol == -1)
    return;
  if (nsol < max_sol_) {
    cout << "found solution" << nsol << "* 2^" << hash_count;
    RecordCount(nsol, hash_count, count_f);
    return;
  }
  unordered_map<int, uint64_t> solutions;
  for (int count_times = 0; count_times < max_count_times_; ++count_times) {
    added_count_lits.clear();
    count_watch.clear();
    prev_hash_count = 0;
    while (left < right) {
      hash_count = (left + right) / 2;
      if (hash_count > prev_hash_count)
        Sample(solver, count_vars, hash_count - prev_hash_count, count_watch,
               added_count_lits);
      vector<Lit> assump(count_watch.begin(), count_watch.begin() + hash_count);
      assump.insert(assump.end(), secret_watch.begin(), secret_watch.end());
      nsol = bounded_sol_count(solver, max_sol_, assump, true);
      if (nsol >= max_sol_) {
        left = hash_count + 1;
      } else if (nsol < max_sol_ / 2) {
        right = hash_count;
      } else {
        right = hash_count;
        left = hash_count;
      }
      solutions[hash_count] = nsol;
      cout << "hash_count=" << hash_count;
      prev_hash_count = hash_count;
      left = hash_count-hash_count/2;
      right= hash_count+ hash_count/2;
    }
    cout << "found solution" << solutions[right] << "* 2^" << right;
    RecordCount(solutions[right], right, count_f);
  }
}

int main(int argc, char **argv) {
  srand(time(NULL));
  Count Count(argc, argv);
  Count.conf.verbosity = 1;
  Count.conf.verbStats = 1;
  Count.conf.preprocess = 0;
  Count.conf.doRenumberVars = false;
  Count.parseCommandLine();
  Count.run();
}
