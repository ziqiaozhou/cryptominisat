#ifndef SAMPLE_H
#define SAMPLE_H
#include "count.h"
#include <sys/time.h>
class Sampler : public Count {
public:
  explicit Sampler(int argc, char **argv)
      : Count(argc, argv), sampleOptions_("Sample options") {
    solver = NULL;
    complementary_solver = NULL;
  }
  ~Sampler() {
    sample_sol_f->close();
    sample_sol_f_same->close();
    delete sample_sol_f_same;
    delete sample_sol_f;
    if (record_full_) {
      sample_sol_complete_f_same->close();
      delete sample_sol_complete_f_same;
      sample_sol_complete_f->close();
      delete sample_sol_complete_f;
    }
    if (solver) {
      delete solver;
    }
    if (complementary_solver) {
      delete complementary_solver;
    }
    solver = NULL;
    complementary_solver = NULL;
  }
  void add_sample_options();
  void add_supported_options() override;
  void run();
  vector<uint32_t> GetCIISS();
  vector<uint32_t> GetVars(string label);
  vector<string> getCIISSModel(SATSolver *solver);
  vector<Lit> getCISSModelLit(SATSolver *solver);
  void RecordSampleSolSame(vector<string> &sol);

  void RecordSampleSol(vector<string> &sol);
  int64_t bounded_sol_generation(SATSolver *solver,
                                 vector<uint32_t> &target_count_vars,
                                 uint32_t maxSolutions,
                                 const vector<Lit> &assumps);
  Lit AddVariableSameHelper(SATSolver *solver,
                            map<string, vector<Lit>> &all_vars);
  vector<Lit> AddVariableDiffHelper(SATSolver *solver,
                                    map<string, vector<Lit>> &all_vars);
  void AddVariableSameOrDiff(SATSolver *solver,
                             map<string, vector<Lit>> &all_vars,
                             map<string, vector<Lit>> diff_vars);

private:
  po::options_description sampleOptions_;
  std::ofstream *sample_sol_f;
  std::ofstream *sample_sol_complete_f;
  std::ofstream *sample_sol_f_same;
  std::ofstream *sample_sol_complete_f_same;
  int sample_noninterference_;
  uint32_t num_cxor_cls_;
  uint32_t num_sxor_cls_;
  uint32_t num_ixor_cls_;
  SATSolver *complementary_solver;
  bool useOtherAlt;
  bool record_full_;
  struct timeval start;
  int nTotalSolutions;
  double perf;
  int nESolver;
};
#endif
