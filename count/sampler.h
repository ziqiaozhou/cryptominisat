#ifndef SAMPLE_H
#define SAMPLE_H
#include "count.h"
class Sampler : public Count {
public:
  explicit Sampler(int argc, char **argv)
      : Count(argc, argv), sampleOptions_("Sample options") {

  }
  ~Sampler() {
    sample_sol_f->close();
    delete sample_sol_f;
  }
  void add_sample_options();
  void add_supported_options() override;
  void run();
  vector<uint32_t> GetCISS();
  string getCISSModel(SATSolver *solver);

  void RecordSampleSol(string sol);
  int64_t bounded_sol_generation(SATSolver *solver,
                                 vector<uint32_t> &target_count_vars,
                                 uint32_t maxSolutions,
                                 const vector<Lit> &assumps);

private:
  po::options_description sampleOptions_;
  std::ofstream *sample_sol_f;
  bool sample_noninterference_;
};
#endif
