/*
 * Jaccard Count Header
 */

#ifndef COMPOSE_H
#define COMPOSE_H

#include "cryptominisat5/cryptominisat.h"
#include "src/main.h"
#include <array>
#include <fstream>
#include <map>
#include <random>
class Compose : public Main {
public:
  void add_compose_options();

  explicit Compose(int argc, char **argv)
      : Main(argc, argv), composeOptions_("Composition options") {}
  void add_supported_options() override;
  void readInAFileToCache(SATSolver *solver2, const string &filename);
  void run();
  void incremental_compose();
  void copy_compose();

private:
  // solver2: Working solver to add clauses
  // trans_symbol_vars: mapping from symbol to var in base transition
  // constraint symbol_vars2: mapping from symbol to var for the existing
  // CNF in solver2;
  void createNextState(SATSolver *solver2,
                       std::map<std::string, vector<Lit>> &trans_symbol_vars,
                       std::map<std::string, vector<Lit>> &symbol_vars2,std::string prev_state);

  void createReplaceMap(SATSolver *solver2,
                        std::map<std::string, vector<Lit>> &symbol_vars2,
                        std::map<std::string, vector<Lit>> &symbol_vars);

  void readInAFileForNewState(SATSolver *solver2, const string &filename);
  SATSolver *transition_solver_;
  po::options_description composeOptions_;
  std::vector<int> replace_tables;
  int cycles_;
  std::string init_file_;
  std::string out_file_;
  SolverConf init_conf_;
  int simplify_interval_;
  int start_cycle_;
  std::string out_dir_;
  vector<vector<Lit>> trans_clauses;
  vector<std::pair<vector<uint32_t>, bool>> trans_xor_clauses;
  int n_trans_vars;
  string mode_;
  int add_clauses_threshold;
};
#endif // COMPOSE_H
