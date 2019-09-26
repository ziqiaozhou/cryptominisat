#include "compose.h"
#include "src/dimacsparser.h"
#include <boost/lexical_cast.hpp>
using boost::lexical_cast;
void print_map(std::map<std::string, vector<uint32_t>> &map) {
  for (auto var : map) {
    cout << var.first << " ";
    for (auto i : var.second)
      cout << i << " ";
    cout << "\n";
  }
}
void Compose::add_compose_options() {
  composeOptions_.add_options()("cycles", po::value(&cycles_)->default_value(1),
                                "Number of composition cycles.")(
      "init", po::value(&init_file_)->default_value(""),
      "Initilization constraint file.")(
      "composedfile", po::value(&out_file_)->default_value(""),
      "Composed filename.")("simplify_interval",
                            po::value(&simplify_interval_)->default_value(1),
                            "n: simplify the cnf per n cycle.")(
      "start_cycle", po::value(&start_cycle_)->default_value(0),
      "set this if compose a multi-cycle CNF from an intermediate state. "
      "For example, you already have cnf for state s8 and want to extend to s "
      "20. "
      "--start_cycle=8 --cycles=20")(
      "out", po::value(&out_dir_)->default_value("tmp"));
  help_options_simple.add(composeOptions_);
  help_options_complicated.add(composeOptions_);
}
void Compose::add_supported_options() {
  Main::add_supported_options();
  add_compose_options();
}

static int createReplaceTable(
    int offset, std::map<std::string, vector<uint32_t>> &original_symbol_vars,
    std::map<std::string, vector<uint32_t>> &to_symbol_vars,
    vector<uint32_t> &outerToInter) {
  for (auto &symbols : original_symbol_vars) {
    std::string sym_name = symbols.first;
    auto &vars = symbols.second;
    if (to_symbol_vars.count(sym_name) == 0)
      continue;
    for (int i = 0; i < vars.size(); ++i) {
      outerToInter[vars[i]] = to_symbol_vars[sym_name][i];
    }
  }
  for (int i = 0; i < outerToInter.size(); ++i) {
    if (outerToInter[i] == -1) {
      uint32_t new_var = offset++;
      outerToInter[i] = new_var;
    }
  }
  for (auto &symbols : original_symbol_vars) {
    std::string sym_name = symbols.first;
    auto &vars = symbols.second;
    if (to_symbol_vars.count(sym_name) == 0) {
      to_symbol_vars[sym_name] = original_symbol_vars[sym_name];
      for (auto &var : to_symbol_vars[sym_name]) {
        var = outerToInter[var];
      }
    }
  }
  return offset;
}
/*void Compose::createReplaceMap(
    SATSolver *solver2, std::map<std::string, vector<uint32_t>> &symbol_vars2,
    std::map<std::string, vector<uint32_t>> &symbol_vars) {
  vector<uint32_t> outerToInter(solver2->nVars(), -1);

  for (auto &symbols : symbol_vars2) {
    std::string sym_name = symbols.first;
    auto &vars = symbols.second;
    if (symbol_vars.count(sym_name) == 0)
      continue;
    for (int i = 0; i < vars.size(); ++i) {
      std::cerr << vars[i] << "\n";
      outerToInter[vars[i]] = symbol_vars[sym_name][i];
    }
  }

  for (int i = 0; i < outerToInter.size(); ++i) {
    if (outerToInter[i] == -1) {
      uint32_t new_var = transition_solver_->nVars();
      transition_solver_->new_vars(1);
      outerToInter[i] = new_var;
    }
  }
  // Ensure variable number consistant.
  if (solver2->nVars() < transition_solver_->nVars()) {
    solver2->new_vars(transition_solver_->nVars() - solver2->nVars());
  }
  transition_solver_->add_clause({Lit(0, true), Lit(0, false)});
  solver2->add_clause({Lit(0, true), Lit(0, false)});
  vector<uint32_t> interToOuter(transition_solver_->nVars(), -1);
  for (int i = 0; i < outerToInter.size(); ++i) {
    interToOuter[outerToInter[i]] = i;
  }
  uint32_t new_var = outerToInter.size();
  for (int i = 0; i < interToOuter.size(); ++i) {
    if (interToOuter[i] == -1) {
      interToOuter[i] = new_var++;
      outerToInter.push_back(i);
    }
  }
  for (auto &symbols : symbol_vars2) {
    for (auto &var : symbols.second) {
      var = outerToInter[var];
    }
  }

  assert(outerToInter.size() == new_var);
  solver2->renumber_clauses_by_table(outerToInter, interToOuter);
}
*/
void Compose::createNextState(
    SATSolver *solver2,
    std::map<std::string, vector<uint32_t>> &trans_symbol_vars,
    std::map<std::string, vector<uint32_t>> &symbol_vars2) {
  cout << "------------\n";
  print_map(trans_symbol_vars);
  cout << "-->\n";
  print_map(symbol_vars2);
  vector<uint32_t> table(n_trans_vars, -1);
  std::cerr << "old nvar is " << solver2->nVars() << "\n";
  int nvar = createReplaceTable(solver2->nVars(), trans_symbol_vars,
                                symbol_vars2, table);
  /*  cout << "Table details:\n";
    for (int i = 0; i < table.size(); ++i) {
      cout << i << ":" << table[i] << "\n";
    }
  */
  if (solver2->nVars() < nvar)
    solver2->new_vars(nvar - solver2->nVars());
  std::cerr << "extend nvar to " << solver2->nVars() << "\n";
  for (auto lits : trans_clauses) {
    for (auto &lit : lits) {
      lit = Lit(table[lit.var()], lit.sign());
    }
    solver2->add_clause(lits);
  }
  for (auto xor_cl : trans_xor_clauses) {
    for (auto &var : xor_cl.first) {
      var = table[var];
    }
    solver2->add_xor_clause(xor_cl.first, xor_cl.second);
  }
}

void Compose::readInAFileToCache(SATSolver *solver2, const string &filename) {
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

  if (!independent_vars_str.empty() && !parser.independent_vars.empty()) {
    std::cerr << "ERROR! Independent vars set in console but also in CNF."
              << endl;
    exit(-1);
  }

  if (!independent_vars_str.empty()) {
    assert(independent_vars.empty());
    std::stringstream ss(independent_vars_str);
    uint32_t i;
    while (ss >> i) {
      const uint32_t var = i - 1;
      independent_vars.push_back(var);

      if (ss.peek() == ',' || ss.peek() == ' ')
        ss.ignore();
    }
  } else {
    independent_vars.insert(independent_vars.end(),
                            parser.independent_vars.begin(),
                            parser.independent_vars.end());
  }
  symbol_vars.insert(parser.symbol_vars.begin(), parser.symbol_vars.end());
  if (conf.keep_symbol) {
    for (auto one_symbol_vars : symbol_vars) {
      independent_vars.insert(independent_vars.end(),
                              one_symbol_vars.second.begin(),
                              one_symbol_vars.second.end());
    }
  }
  jaccard_vars.swap(parser.jaccard_vars);
  jaccard_vars2.swap(parser.jaccard_vars2);
  ob_vars.swap(parser.ob_vars);
  attack_vars.swap(parser.attack_vars);
  if (independent_vars.empty()) {
    if (only_indep_solution) {
      std::cout << "ERROR: only independent vars are requested in the "
                   "solution, but no independent vars have been set!"
                << endl;
      exit(-1);
    }
  } else {
    solver2->set_independent_vars(&independent_vars);
  }
  solver2->set_symbol_vars(&symbol_vars);

  call_after_parse();

#ifndef USE_ZLIB
  fclose(in);
#else
  gzclose(in);
#endif
  cout << "parse finish and close\n";
}

void Compose::run() {
  transition_solver_ = new SATSolver((void *)&conf);
  SolverConf conf2 = conf;
  SolverConf conf_copy = conf;
  vector<uint32_t> ind_vars;
  conf2.doRenumberVars = false;
  SATSolver *init_solver = new SATSolver((void *)&conf2);
  // Read transition CNF
  std::cerr << "read1"
            << "\n";
  readInAFileToCache(transition_solver_, filesToRead[0]);
  n_trans_vars = transition_solver_->nVars();
  auto trans_symbol_vars = symbol_vars;
  std::cerr << "read2"
            << "\n";
  // read init CNF file;
  symbol_vars.clear();
  independent_vars.clear();
  readInAFile(init_solver, init_file_);
  auto init_symbol_vars = symbol_vars;
  std::cerr << "after read2"
            << "\nsym:" << conf.symbol_vars << "\t" << conf2.symbol_vars;
  std::map<std::string, std::vector<uint32_t>> current_trans_symbol_vars;
  current_trans_symbol_vars = trans_symbol_vars;
  auto base_trans_symbol_vars = trans_symbol_vars;
  current_trans_symbol_vars.erase("s0");
  current_trans_symbol_vars.erase("s1");
  for (int i = start_cycle_; i < cycles_; ++i) {
    // compose;
    std::string state_path = out_dir_;
    std::cerr << "cycle" << i << "\n";
    std::string prev_state = "s" + std::to_string(i);
    std::string current_state = "s" + std::to_string(i + 1);
    state_path = state_path + "//" + current_state + ".cnf";
    current_trans_symbol_vars[prev_state] = trans_symbol_vars["s0"];
    current_trans_symbol_vars[current_state] = trans_symbol_vars["s1"];
    createNextState(init_solver, current_trans_symbol_vars, init_symbol_vars);
    current_trans_symbol_vars.erase(prev_state);
    if (prev_state != "s0")
      init_symbol_vars.erase(prev_state);
    init_solver->set_symbol_vars(&init_symbol_vars);
    ind_vars.clear();
    for (auto vars : init_symbol_vars)
      for (auto var : vars.second)
        ind_vars.push_back(var);
    init_solver->set_independent_vars(&ind_vars);
    // cout << "init_symbol_vars\n";
    // print_map(init_symbol_vars);
    if (i % simplify_interval_ == 0) {
      init_solver->simplify();
      init_solver->renumber_variables(true);
    }
    std::ofstream finalout(state_path);
    init_solver->dump_irred_clauses_ind_only(&finalout);
    finalout.close();
    if (i % simplify_interval_ == 0) {
      delete init_solver;
      conf2 = conf_copy;
      init_solver = new SATSolver((void *)&conf2);
      symbol_vars.clear();
      independent_vars.clear();
      readInAFile(init_solver, state_path);
      init_symbol_vars = symbol_vars;
    }
    // init_solver->renumber_variables(true);
    cout << "after renumber: init_symbol_vars\n";
    print_map(init_symbol_vars);
  }
  if (cycles_ - 1 % simplify_interval_ != 0) {
    init_solver->simplify();
    init_solver->renumber_variables(true);
  }
  std::ofstream finalout(out_dir_ + "//" + out_file_);
  init_solver->dump_irred_clauses_ind_only(&finalout);
  finalout.close();
}
int main(int argc, char **argv) {
  Compose compose(argc, argv);
  compose.conf.verbosity = 1;
  compose.conf.verbStats = 1;
  compose.conf.preprocess = 1;
  compose.conf.doRenumberVars = false;
  compose.parseCommandLine();
  compose.run();
}
