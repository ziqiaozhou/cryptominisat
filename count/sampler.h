#ifndef SAMPLE_H
#define SAMPLE_H
#include "count.h"
class Sampler : public Count {
public:
  explicit Sampler(int argc, char **argv)
      : Count(argc, argv), sampleOptions_("Sample options") {}
  ~Sampler() {
    sample_sol_f->close();
    delete sample_sol_f;
    sample_sol_complete_f->close();
    delete sample_sol_complete_f;
  }
  void add_sample_options();
  void add_supported_options() override;
  void run();
  vector<uint32_t> GetCISS();
  vector<uint32_t> GetVars(string label);
  vector<string> getCISSModel(SATSolver *solver);

  void RecordSampleSol(vector<string> &sol);
  int64_t bounded_sol_generation(SATSolver *solver,
                                 vector<uint32_t> &target_count_vars,
                                 uint32_t maxSolutions,
                                 const vector<Lit> &assumps);
  Lit AddVariableSameHelper(SATSolver *solver,
                            map<string, vector<Lit>> &all_vars);
  vector<Lit> AddVariableDiffHelper(SATSolver *solver,
                                    map<string, vector<Lit>> &all_vars);
  void AddVariableSameOrDiff(SATSolver *solver, map<string, vector<Lit>> &all_vars,
                        map<string, vector<Lit>> diff_vars);

private:
  po::options_description sampleOptions_;
  std::ofstream *sample_sol_f;
  std::ofstream *sample_sol_complete_f;
  bool sample_noninterference_;
  uint32_t num_cxor_cls_;
  uint32_t num_sxor_cls_;
  uint32_t num_ixor_cls_;
};
#endif
