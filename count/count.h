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
#include <unordered_map>
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
  void AddVariableDiff(SATSolver *solver, map<string, vector<Lit>> all_vars);
  void AddVariableSame(SATSolver *solver, map<string, vector<Lit>> all_vars);

  string Sample(SATSolver *solver, std::vector<uint32_t> vars, int num_xor_cls,
                vector<Lit> &watch, vector<vector<uint32_t>> &alllits,
                vector<bool> &rhs, bool addInner = false,
                bool is_restarted = false);
  int64_t bounded_sol_count(SATSolver *solver, vector<uint32_t> &count_vars, uint32_t maxSolutions,
                            const vector<Lit> &assumps, bool only_ind = true);
  map<int, uint64_t> count_once(SATSolver *solver, vector<uint32_t> &count_vars,
                                const vector<Lit> &secret_watch, int &left,
                                int &right, int &hash_count ,bool reserve_xor=false);
  void count(SATSolver *solver, vector<uint32_t> &secret_vars);

  void simulate_count(SATSolver *solver, vector<uint32_t> &secret_vars);

  bool IsValidVictimLabel(std::string label) {
    static std::unordered_set<std::string> labels = {SECRET_, CONTROLLED_,
                                                     OBSERVABLE_, OTHER_};
    if (labels.count(label) == 0)
      return false;
    return true;
  }
  void setBackupSolvers();
  vector<string> getIDs() {
    vector<string> ids;
    for (auto id_var : all_secret_vars) {
      ids.push_back(id_var.first);
    }
    return ids;
  }
  void setSecretVars() {
    for (auto name_lits : symbol_vars) {
      int name_len = SECRET_.length();
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
    vector<uint32_t> other_control_vars;
    count_vars.clear();
    for (auto name_lits : symbol_vars) {
      if (!name_lits.first.compare(0, CONTROLLED_.length(), CONTROLLED_)) {
        for (auto lit : name_lits.second) {
          count_vars.push_back(lit.var());
          other_control_vars.push_back(lit.var());
        }
      } else if (!name_lits.first.compare(0, OBSERVABLE_.length(),
                                          OBSERVABLE_)) {
        int name_len = OBSERVABLE_.length();
        auto id = name_lits.first.substr(name_len);
        for (auto lit : name_lits.second) {
          count_vars.push_back(lit.var());
          all_observe_lits[id].push_back(lit);
        }
      } else if (!name_lits.first.compare(0, OTHER_.length(), OTHER_)) {
        for (auto lit : name_lits.second) {
          count_vars.push_back(lit.var());
          other_control_vars.push_back(lit.var());
        }
      }
    }
    for (auto id_lits : all_observe_lits) {
      all_count_vars[id_lits.first] = other_control_vars;
      for (auto lit : id_lits.second)
        all_count_vars[id_lits.first].push_back(lit.var());
    }
  }
  void RecordSolution(string rnd);
  void RecordCount(map<int, uint64_t> &sols, int hash_count, string rnd);
  void RecordCountInter(map<int, uint64_t> &sols, int hash_count,
                        map<string, map<int, uint64_t>> b_sols,
                        map<string, int> b_hash_counts, string rnd);

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
  map<string, SATSolver *> backup_solvers;
  std::string out_dir_;
  std::string victim_model_config_;
  std::map<std::string, std::vector<uint32_t>> victim_model_;
  vector<vector<Lit>> trans_clauses;
  vector<std::pair<vector<uint32_t>, bool>> trans_xor_clauses;
  int n_trans_vars;
  string mode_;
  // model counting setting
  vector<uint32_t> count_vars;
  vector<uint32_t> secret_vars;
  std::map<string, vector<Lit>> all_observe_lits;
  std::map<string, vector<uint32_t>> all_count_vars;
  std::map<string, vector<Lit>> all_secret_vars;

  double xor_ratio_;
  int num_xor_cls_;
  int max_sol_;
  int backtrack_;
  bool search_all;
  int max_count_times_;
  bool record_solution_;
  int max_log_size_;
  int min_log_size_;
  vector<vector<Lit>> solution_lits;
  int max_xor_per_var_;
  string hash_file;
  std::ofstream *hashf;
  int inter_mode_;
  int nsample;
  vector<vector<uint32_t>> added_count_lits;
  vector<bool> count_rhs;
  vector<Lit> count_watch;
};
void findComponent(const SATSolver *solver);
#endif // COMPOSE_H
