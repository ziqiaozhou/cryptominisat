/*
 * Jaccard Count Header
 */

#ifndef COUNT_H
#define COUNT_H
#include "cryptominisat5/cryptominisat.h"
#include "src/main.h"
#include <array>
#include <fstream>
#include <map>
#include <random>
#include <unordered_set>
class Count : public Main {
public:
  void add_count_options();

  explicit Count(int argc, char **argv)
      : Main(argc, argv), countOptions_("Count options") {}
  void add_supported_options() override;
  void run();

private:
  // solver2: Working solver to add clauses
  // trans_symbol_vars: mapping from symbol to var in base transition
  // constraint symbol_vars2: mapping from symbol to var for the existing
  // CNF in solver2;
  const std::string SECRET_ = "secret";
  const std::string CONTROLLED_ = "control";
  const std::string OBSERVABLE_ = "observe";
  const std::string OTHER_ = "other";
  void Sample(SATSolver *solver, std::vector<uint32_t> vars, int num_xor_cls,
              vector<Lit> &watch, vector<vector<uint32_t>> &alllits,
              bool addInner = false);
  int64_t bounded_sol_count(SATSolver *solver, uint32_t maxSolutions,
                            const vector<Lit> &assumps, bool only_ind = true);
  void count(SATSolver *solver, vector<uint32_t> &secret_vars,
             std::ofstream *count_f);
  bool IsValidVictimLabel(std::string label) {
    static std::unordered_set<std::string> labels = {SECRET_, CONTROLLED_,
                                                     OBSERVABLE_, OTHER_};
    if (labels.count(label) == 0)
      return false;
    return true;
  }
  void RecordSolution();
  void readVictimModel(SATSolver *&solver);
  po::options_description countOptions_;
  std::vector<int> replace_tables;
  int cycles_;
  std::string symmap_file_;
  std::string out_file_;
  std::string init_file_;
  SolverConf init_conf_;
  std::string out_dir_;
  std::string victim_model_config_;
  std::map<std::string, std::vector<uint32_t>> victim_model_;
  vector<vector<Lit>> trans_clauses;
  vector<std::pair<vector<uint32_t>, bool>> trans_xor_clauses;
  int n_trans_vars;
  string mode_;
  // model counting setting
  vector<uint32_t> count_vars;
  double xor_ratio_;
  int num_xor_cls_;
  int max_sol_;
  int backtrack_;

  int max_count_times_;
  bool record_solution_;
  vector<vector<Lit>> solution_lits;
};
#endif // COMPOSE_H
