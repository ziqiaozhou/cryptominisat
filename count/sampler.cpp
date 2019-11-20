#include "src/dimacsparser.h"
//#include <boost/lexical_cast.hpp>

#include "sampler.h"
#include <iostream>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_map>
vector<Lit> Sampler::AddVariableDiffHelper(SATSolver *solver,
                                           map<string, vector<Lit>> &all_vars) {
  size_t len = -1;
  vector<Lit> watches;
  assert(all_vars.size() > 0);
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    len = lits.size();
  }
  string diff_file = out_dir_ + "//" + out_file_ + ".testhash";
  std::ofstream finalout(diff_file);
  for (int i = 0; i < len; ++i) {
    vector<uint32_t> clause;
    auto new_watch = solver->nVars();
    solver->new_var();
    clause.push_back(new_watch);
    watches.push_back(Lit(new_watch, true));
    bool xor_bool = true;
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign())
        xor_bool = ~xor_bool;
    }
    solver->add_xor_clause(clause, xor_bool);
    finalout << "x" << xor_bool ? "" : "-";
    for (auto v : clause)
      finalout << v + 1;
    finalout << "\n";
  }
  return watches;
}
Lit Sampler::AddVariableSameHelper(SATSolver *solver,
                                   map<string, vector<Lit>> &all_vars) {
  size_t len=0;
  vector<Lit> clause;
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    len = lits.size();
  }
  auto same_watch = solver->nVars();
  solver->new_var();
  clause.push_back(Lit(same_watch,false));
  for (int i = 0; i < len; ++i) {
    vector<uint32_t> clause;
    auto new_watch = solver->nVars();
    solver->new_var();
    clause.push_back(new_watch);
    solver->add_clause({Lit(new_watch, true), Lit(same_watch, true)});
    bool xor_bool = false;
    for (auto id_vars : all_vars) {
      auto id = id_vars.first;
      auto &lits = id_vars.second;
      clause.push_back(lits[i].var());
      if (lits[i].sign())
        xor_bool = ~xor_bool;
    }
    solver->add_xor_clause(clause, xor_bool);
  }
  solver->add_clause(clause);
  return Lit(same_watch, false);
}
void Sampler::AddVariableSameOrDiff(SATSolver *solver,
                                    map<string, vector<Lit>> &all_vars,
                                    map<string, vector<Lit>> diff_vars) {
  int len = -1;
  vector<Lit> watches;
  if (all_vars.size() != 0) {
    watches.push_back(AddVariableSameHelper(solver,all_vars));
  }
  if (diff_vars.size()) {
    auto ws = AddVariableDiffHelper(solver,diff_vars);
    for (auto w : ws) {
      watches.push_back(w);
    }
  }
  solver->add_clause(watches);
}

void Sampler::add_supported_options() {
  Count::add_supported_options();
  add_sample_options();
}
void Sampler::add_sample_options() {
  sampleOptions_.add_options()(
      "noninter", po::value(&sample_noninterference_)->default_value(false),
      "Number of samples");
  help_options_simple.add(sampleOptions_);
  help_options_complicated.add(sampleOptions_);
}
vector<uint32_t> Sampler::GetCISS() {
  vector<uint32_t> sample_vars;
  vector<string> labels = {CONTROLLED_, OTHER_, SECRET_ + "_0", SECRET_ + "_1"};
  for (auto label : labels)
    for (auto l : symbol_vars[label]) {
      sample_vars.push_back(l.var());
    }
  return sample_vars;
}

vector<string> Sampler::getCISSModel(SATSolver *solver) {
  string ret = "";
  std::stringstream ret2;
  vector<string> labels = {CONTROLLED_, OTHER_, SECRET_ + "_0", SECRET_ + "_1"};
  vector<string> complete_labels = {CONTROLLED_,        OTHER_,
                                    SECRET_ + "_0",     SECRET_ + "_1",
                                    OBSERVABLE_ + "_0", OBSERVABLE_ + "_1"};
  auto &model = solver->get_model();
  for (auto label : complete_labels) {
    if (symbol_vars.count(label) == 0)
      continue;
    for (auto l : symbol_vars[label]) {
      ret2 << Lit(l.var(), model[l.var()] == l_False) << ", ";
    }
    ret2 << ", ";
  }
  for (auto label : labels) {
    if (symbol_vars.count(label) == 0)
      continue;
    ret += "";
    for (auto l : symbol_vars[label]) {
      if (model[l.var()] == l_Undef)
        ret += "x";
      if (model[l.var()] == l_True)
        ret += l.sign() ? "0" : "1";
      if (model[l.var()] == l_False)
        ret += l.sign() ? "1" : "0";
      ret += ", ";
    }
    ret += ", ";
  }
  return {ret2.str(), ret};
}
void Sampler::RecordSampleSol(vector<string> &sol) {

  if (!record_solution_)
    return;
  *sample_sol_complete_f << sol[0] << endl;
  *sample_sol_f << sol[1] << endl;
}

int64_t Sampler::bounded_sol_generation(SATSolver *solver,
                                        vector<uint32_t> &target_count_vars,
                                        uint32_t maxSolutions,
                                        const vector<Lit> &assumps) {
  solver->set_sampling_vars(&target_count_vars);
  vector<lbool> model;
  lbool ret;
  int solutions = 0;
  bool only_ind = true;
  vector<Lit> new_assumps(assumps);
  solver->new_var();
  uint32_t act_var = solver->nVars() - 1;
  new_assumps.push_back(Lit(act_var, true));
  if (new_assumps.size() > 1)
    solver->simplify(&new_assumps);

  while (solutions < maxSolutions) {
    ret = solver->solve(&new_assumps, only_ind);
    assert(ret == l_False || ret == l_True);

    if (conf.verbosity >= 2) {
      cout << "[appmc] bounded_sol_count ret: " << std::setw(7) << ret;
      if (ret == l_True) {
        cout << " sol no.  " << std::setw(3) << solutions;
      } else {
        cout << " No more. " << std::setw(3) << "";
      }
    }

    if (ret != l_True) {
      break;
    }
    solutions += std::max(1, solver->n_seareched_solutions());
    if (solutions < maxSolutions) {
      vector<Lit> lits, solution;
      lits.push_back(Lit(act_var, false));
      for (const uint32_t var : target_count_vars) {
        if (solver->get_model()[var] != l_Undef) {
          lits.push_back(Lit(var, solver->get_model()[var] == l_True));
        } else {
          assert(false);
        }
      }
      auto cissmodel = getCISSModel(solver);
      RecordSampleSol(cissmodel);
      solver->add_clause(lits);
    }
    solutions += solver->n_seareched_solutions();
  }
  // Remove clauses added
  solver->add_clause({Lit(act_var, false)});
}
void Sampler::run() {

  solver = new SATSolver((void *)&conf);
  inputfile = filesToRead[0];
  readInAFile(solver, inputfile);
  setSecretVars();
  setCountVars();
  if (sample_noninterference_) {
    AddVariableSameOrDiff(solver, all_observe_lits, all_declass_lits);
    sample_sol_f = new std::ofstream(out_dir_ + "//" + out_file_ + ".same.csv",
                                     std::ofstream::out | std::ofstream::app);
    sample_sol_complete_f =
        new std::ofstream(out_dir_ + "//" + out_file_ + ".same_complete.csv",
                          std::ofstream::out | std::ofstream::app);
    // AddVariableSame(solver, all_declass_lits);
  } else {
    AddVariableDiff(solver, all_observe_lits);
    sample_sol_f = new std::ofstream(out_dir_ + "//" + out_file_ + ".diff.csv",
                                     std::ofstream::out | std::ofstream::app);
    sample_sol_complete_f =
        new std::ofstream(out_dir_ + "//" + out_file_ + ".diff_complete.csv",
                          std::ofstream::out | std::ofstream::app);
    AddVariableSame(solver, all_declass_lits);
  }

  AddVariableDiff(solver, all_secret_lits);
  vector<uint32_t> CISS = GetCISS();
  vector<Lit> ciss_assump;
  vector<vector<uint32_t>> ciss_added_vars;
  vector<bool> ciss_rhs;
  for (int t = 0; t < nsample; ++t) {
    ciss_assump.clear();
    ciss_added_vars.clear();
    ciss_rhs.clear();
    Count::Sample(solver, CISS, num_xor_cls_, ciss_assump, ciss_added_vars,
                  ciss_rhs, lit_Undef);
    bounded_sol_generation(solver, CISS, max_sol_, ciss_assump);
  }
}

int main(int argc, char **argv) {
  srand(time(NULL));
  Sampler sampler(argc, argv);
  // Count.conf.doRenumberVars = true;
  sampler.parseCommandLine();
  sampler.run();
}
