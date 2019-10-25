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
      : Main(argc, argv), countOptions_("Count options"), max_xor_per_var_(32) {
    hash_file = ".hash.cnf";
    hashf = nullptr;
  }
  ~Count() {}
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
  void AddVariableDiff(SATSolver * solver,map<string,vector<Lit>> all_vars);
  void AddVariableSame(SATSolver * solver,map<string,vector<Lit>> all_vars);

  string Sample(SATSolver *solver, std::vector<uint32_t> vars, int num_xor_cls,
              vector<Lit> &watch, vector<vector<uint32_t>> &alllits,
              vector<bool> &rhs, bool addInner = false,
              bool is_restarted = false);
  int64_t bounded_sol_count(SATSolver *solver, uint32_t maxSolutions,
                            const vector<Lit> &assumps, bool only_ind = true);
  void count(SATSolver *solver, vector<uint32_t> &secret_vars);
  void simulate_count(SATSolver *solver, vector<uint32_t> &secret_vars);

  bool IsValidVictimLabel(std::string label) {
    static std::unordered_set<std::string> labels = {SECRET_, CONTROLLED_,
                                                     OBSERVABLE_, OTHER_};
    if (labels.count(label) == 0)
      return false;
    return true;
  }
  void setSecretVars() {
    for (auto name_lits : symbol_vars) {
      int name_len =  SECRET_.length();
      if (!name_lits.first.compare(0, SECRET_.length(), SECRET_)) {
        auto id = name_lits.first.substr(name_len);
        for (auto lit : name_lits.second) {
          secret_vars.push_back(lit.var());
          all_secret_vars[id].push_back(lit);
        }
      }
    }
  }
  void setCountVars() {
    count_vars.clear();
    for (auto name_lits : symbol_vars) {
      if (!name_lits.first.compare(0, CONTROLLED_.length(), CONTROLLED_)) {
        for (auto lit : name_lits.second)
          count_vars.push_back(lit.var());
      } else if (!name_lits.first.compare(0, OBSERVABLE_.length(), OBSERVABLE_)){
        int name_len =  OBSERVABLE_.length();
        auto id = name_lits.first.substr(name_len);
        for (auto lit : name_lits.second) {
          count_vars.push_back(lit.var());
          all_observe_vars[id].push_back(lit);
        }
      } else if (!name_lits.first.compare(0, OTHER_.length(), OTHER_)) {
        for (auto lit : name_lits.second)
          count_vars.push_back(lit.var());
      }
    }
    /*
    for (auto lit : symbol_vars[CONTROLLED_]) {
      count_vars.push_back(lit.var());
    }
    for (auto lit : symbol_vars[OBSERVABLE_]) {
      count_vars.push_back(lit.var());
    }
    for (auto lit : symbol_vars[OTHER_]) {
      count_vars.push_back(lit.var());
    }*/
  }
  void RecordSolution(string rnd);
  void RecordCount(int sol, int hash_count,
                  string rnd);
  // Return true if reading victim model;
  // Return false if no model to read;
  bool readVictimModel(SATSolver *&solver);
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
  vector<uint32_t> full_count_vars;
  vector<uint32_t> secret_vars;
  vector<uint32_t> full_secret_vars;

  std::map<string, vector<Lit>> all_observe_vars;
  std::map<string, vector<Lit>> all_secret_vars;
  double xor_ratio_;
  int num_xor_cls_;
  int max_sol_;
  int backtrack_;
  bool search_all;
  int max_count_times_;
  bool record_solution_;
  int max_log_size_;
  vector<vector<Lit>> solution_lits;
  int max_xor_per_var_;
  string hash_file;
  std::ofstream *hashf;
  int inter_mode_;
  int nsample;
};
void findComponent(const SATSolver *solver);
#endif // COMPOSE_H
