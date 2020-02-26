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
  SATSolver *newCounterSolver(void *conf) {
    SATSolver *s = new SATSolver(conf);
    s->set_up_for_scalmc();
    s->set_allow_otf_gauss();
    return s;
  }
  explicit Count(int argc, char **argv)
      : Main(argc, argv), countOptions_("Count options") {
    hash_file = ".hash.cnf";
    hashf = nullptr;
    left_ = -1;
    right_ = -1;
  }
  ~Count() {}
  void add_supported_options() override;
  void run();

protected:
  // solver2: Working solver to add clauses
  // trans_symbol_vars: mapping from symbol to var in base transition
  // constraint symbol_vars2: mapping from symbol to var for the existing
  // CNF in solver2;
  const std::string SECRET_ = "secret";
  const std::string DECLASS_ = "declass";
  const std::string CONTROLLED_ = "control";
  const std::string OBSERVABLE_ = "observe";
  const std::string OTHER_ = "other";
  void AddVariableDiff(SATSolver *solver, map<string, vector<Lit>> all_vars);
  void AddVariableSame(SATSolver *solver, map<string, vector<Lit>> all_vars);

  string Sample(SATSolver *solver2, std::vector<uint32_t> vars, int num_xor_cls,
                vector<Lit> &watch, vector<vector<uint32_t>> &alllits,
                vector<bool> &rhs, Lit addInner = lit_Undef,
                bool is_restarted = false);
  int64_t bounded_sol_count(SATSolver *solver,
                            const vector<uint32_t> &count_vars,
                            uint32_t maxSolutions, const vector<Lit> &assumps,
                            bool only_ind = true);
  map<int, uint64_t> count_once(SATSolver *solver, vector<uint32_t> &count_vars,
                                const vector<Lit> &secret_watch, int &left,
                                int &right, int &hash_count,
                                bool reserve_xor = false);
  bool count(SATSolver *solver, vector<uint32_t> &secret_vars);
  bool countCISAlt(SATSolver *solver, vector<uint32_t> &secret_vars);

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
    for (auto id_var : all_secret_lits) {
      ids.push_back(id_var.first);
    }
    return ids;
  }
  void clearFlagVars() {
    all_secret_lits.clear();
    all_declass_lits.clear();
    all_observe_lits.clear();
    all_count_vars.clear();
    count_vars.resize(0);
    secret_vars.resize(0);
  }
  void setSecretVars();
  void setCountVars();
  void RecordSolution(string rnd);
  void RecordCount(map<int, uint64_t> &sols, int hash_count, string rnd);

  void RecordCountInter(map<int, uint64_t> &sols, int hash_count,
                        vector<map<int, uint64_t>> b_sols,
                        vector<int> b_hash_counts, string rnd);
  vector<uint32_t> getCISAlt();
  // Return true if reading victim model;
  // Return false if no model to read;
  bool readVictimModel(SATSolver *&solver);
  vector<string> getCIISSModel(SATSolver *solver);
  bool ProbToDiffFromSecretSet();
  void calculateDiffSolution(vector<vector<Lit>> &sol1,
                             vector<vector<Lit>> &sol2, vector<string> &s1,
                             vector<string> &s2, string rnd);
  po::options_description countOptions_;
  std::vector<int> replace_tables;
  int cycles_;
  std::string symmap_file_;
  std::string out_file_;
  std::string init_file_;
  SolverConf init_conf_;
  // backup_solvers[0] count original denominator, backup_solver1 count declass
  // denominator solver-> declass_1=delcass_2  && h(secret_1)=r1 && h(secret_2)
  // =r1 backup_solvers[0]-> declass_1=delcass_2  && (h(secret_1)=r1 ||
  // h(secret_1) =r2) && (h(secret_2)=r1 || h(secret_2) =r2) &&
  // h(secret_1)!=h(secret_2);
  // backup_solvers[1]->
  // (h(secret_1)=r1 || h(secret_1) =r2) &&
  // (h(secret_2)=r1 || h(secret_2) =r2) &&
  // h(secret_1)!=h(secret_2);
  vector<SATSolver *> backup_solvers;
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
  std::map<string, vector<Lit>> all_secret_lits;
  std::map<string, vector<Lit>> all_declass_lits;
  std::map<string, vector<Lit>> all_observe_lits;
  std::vector<Lit> control_lits;
  std::map<string, vector<Lit>> all_other_lits;
  std::map<string, vector<uint32_t>> all_count_vars;

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
  vector<string> solution_strs;
  int max_xor_per_var_;
  string hash_file;
  string inputfile;
  std::ofstream *hashf;
  int inter_mode_;
  int nsample;
  vector<vector<uint32_t>> added_count_lits;
  vector<bool> count_rhs;
  vector<Lit> count_watch;
  vector<int> backup_left_;
  vector<int> backup_right_;
  int left_;
  int right_;
  bool use_overlap_coefficient_;
};
void findComponent(const SATSolver *solver);
#endif // COMPOSE_H
