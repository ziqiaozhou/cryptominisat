#include "src/dimacsparser.h"
//#include <boost/lexical_cast.hpp>

#include "sampler.h"
#include <iostream>
#include <sys/types.h>
#include <unistd.h>
#include <unordered_map>
vector<Lit> Sampler::AddVariableDiffHelper(SATSolver *solver2,
                                           map<string, vector<Lit>> &all_vars) {
  size_t len = -1;
  vector<Lit> watches;
  assert(all_vars.size() > 0);
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    len = lits.size();
  }
  string diff_file = out_dir_ + "//" + out_file_ + ".testdiffhash";
  std::ofstream finalout(diff_file);
  vector<uint32_t> clause;
  auto new_watch=solver2->nVars()-1;
  solver2->new_vars(len);
  for (int i = 0; i < len; ++i) {
    clause.clear();
    new_watch++;
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
    solver2->add_xor_clause(clause, xor_bool);
    finalout << "xx" << xor_bool ? "" : "-";
    for (auto v : clause)
      finalout << v + 1 << " ";
    finalout << "\n";
  }
  return watches;
}
Lit Sampler::AddVariableSameHelper(SATSolver *solver,
                                   map<string, vector<Lit>> &all_vars) {
  size_t len = 0;
  vector<Lit> clause;
  for (auto id_lits : all_vars) {
    auto id = id_lits.first;
    auto lits = id_lits.second;
    len = lits.size();
  }
  auto same_watch = solver->nVars();
  solver->new_var();
  clause.push_back(Lit(same_watch, false));
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
  string samefile = out_dir_ + "//" + out_file_ + ".testsamehash";
  std::ofstream finalout(samefile);
  finalout << "x" << xor_bool ? "" : "-";
  for (auto v : clause)
    finalout << v + 1 << " ";
  solver->add_clause(clause);
  finalout.close();
  return Lit(same_watch, false);
}
void Sampler::AddVariableSameOrDiff(SATSolver *solver,
                                    map<string, vector<Lit>> &all_vars,
                                    map<string, vector<Lit>> diff_vars) {
  int len = -1;
  vector<Lit> watches;
  if (all_vars.size() != 0) {
    watches.push_back(AddVariableSameHelper(solver, all_vars));
  }
  if (diff_vars.size()) {
    auto ws = AddVariableDiffHelper(solver, diff_vars);
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
      "noninterference? or interference sample");
  sampleOptions_.add_options()("num_cxor_cls",
                               po::value(&num_cxor_cls_)->default_value(10),
                               "num_cxor_cls");
  sampleOptions_.add_options()("num_sxor_cls",
                               po::value(&num_sxor_cls_)->default_value(2),
                               "num_sxor_cls");
  sampleOptions_.add_options()("num_ixor_cls",
                               po::value(&num_ixor_cls_)->default_value(2),
                               "num_ixor_cls");
  sampleOptions_.add_options()("useOtherAlt",
                               po::value(&useOtherAlt)->default_value(false),
                               "useOtherAlt");
  sampleOptions_.add_options()("recordFull",
                               po::value(&record_full_)->default_value(false),
                               "record all variables into full sols");
  help_options_simple.add(sampleOptions_);
  help_options_complicated.add(sampleOptions_);
}
vector<uint32_t> Sampler::GetCIISS() {
  vector<uint32_t> sample_vars;
  vector<string> labels = {CONTROLLED_, OTHER_ + "_0", OTHER_ + "_1",
                           SECRET_ + "_0", SECRET_ + "_1"};
  for (auto label : labels)
    for (auto l : symbol_vars[label]) {
      if (!useOtherAlt && label == (OTHER_ + "_1")) {
        continue;
      }
      sample_vars.push_back(l.var());
    }

  return sample_vars;
}
vector<uint32_t> Sampler::GetVars(string label) {
  vector<uint32_t> sample_vars;
  for (auto l : symbol_vars[label]) {
    sample_vars.push_back(l.var());
  }
  return sample_vars;
}
vector<Lit> Sampler::getCISSModelLit(SATSolver *solver) {
  vector<Lit> ret;
  vector<string> labels = {CONTROLLED_, OTHER_ + "_0", SECRET_ + "_0",
                           SECRET_ + "_1"};
  auto &model = solver->get_model();
  for (auto label : labels) {
    if (symbol_vars.count(label) == 0)
      continue;
    for (auto l : symbol_vars[label]) {
      ret.push_back(Lit(l.var(), model[l.var()] == l_False));
    }
  }
  return ret;
}

vector<string> Sampler::getCIISSModel(SATSolver *solver) {
  string ret = "";
  std::stringstream ret2;
  vector<string> labels = {CONTROLLED_, OTHER_ + "_0", OTHER_ + "_1",
                           SECRET_ + "_0", SECRET_ + "_1"};
  vector<string> complete_labels = {
      CONTROLLED_,    OTHER_ + "_0",      OTHER_ + "_1",     SECRET_ + "_0",
      SECRET_ + "_1", OBSERVABLE_ + "_0", OBSERVABLE_ + "_1"};
  auto &model = solver->get_model();
  for (auto label : complete_labels) {
    if (symbol_vars.count(label) == 0)
      continue;
    if (!useOtherAlt && label == (OTHER_ + "_1")) {
      continue;
    }
    for (auto l : symbol_vars[label]) {
      ret2 << Lit(l.var(), model[l.var()] == l_False) << ", ";
    }
    ret2 << ", ";
  }
  for (auto label : labels) {
    if (symbol_vars.count(label) == 0) {
      ret += ", ";
      continue;
    }
    if (!useOtherAlt && label == (OTHER_ + "_1")) {
      ret += ", ";
      continue;
    }
    ret += "";
    for (auto l : symbol_vars[label]) {
      if (model[l.var()] == l_Undef || !used_vars.count(l.var()))
        ret += "x";
      else if (model[l.var()] == l_True)
        ret += l.sign() ? "0" : "1";
      else if (model[l.var()] == l_False)
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

  if (record_full_)
    *sample_sol_complete_f << sol[0] << endl;
  *sample_sol_f << sol[1] << endl;
}

void Sampler::RecordSampleSolSame(vector<string> &sol) {

  if (!record_solution_)
    return;
  if (record_full_)
    *sample_sol_complete_f_same << sol[0] << endl;
  *sample_sol_f_same << sol[1] << endl;
}

int64_t Sampler::bounded_sol_generation(SATSolver *solver,
                                        vector<uint32_t> &target_count_vars,
                                        uint32_t maxSolutions,
                                        const vector<Lit> &assumps) {

  vector<lbool> model;
  lbool ret;
  int solutions = 0, total_sol = 0;
  bool only_ind = true;
  vector<Lit> new_assumps(assumps);
  solver->new_var();
  uint32_t act_var = solver->nVars() - 1;
  new_assumps.push_back(Lit(act_var, true));
  if (new_assumps.size() > 1)
    solver->simplify(&new_assumps);

  while (total_sol < maxSolutions) {
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
    solutions++;
    total_sol++;
    if (solutions < maxSolutions) {
      vector<Lit> lits, solution;

      for (const uint32_t var : target_count_vars) {
        if (solver->get_model()[var] != l_Undef && used_vars.count(var)) {
          lits.push_back(Lit(var, solver->get_model()[var] == l_True));
        }
      }

      auto cissmodel = getCIISSModel(solver);
      lits.push_back(Lit(act_var, false));
      solver->add_clause(lits);
      if (!sample_noninterference_) {
        if (!useOtherAlt) {
          vector<Lit> sol_lits = getCISSModelLit(solver);
          if (complementary_solver->solve(&sol_lits) == l_True) {
            // not actual leakage
            RecordSampleSolSame(cissmodel);
            // std::cout<<"complementary_solver->solve(&sol_lits) == l_True\n";
            solutions--;
            continue;
          }
        }
      }
      RecordSampleSol(cissmodel);
    }
    solutions += solver->n_seareched_solutions();
  }
  // Remove clauses added
  solver->add_clause({Lit(act_var, false)});
  return solutions;
}

void Sampler::run() {

  solver = newCounterSolver((void *)&conf);
  inputfile = filesToRead[0];
  readInAFileToCache(solver, inputfile);
  setSecretVars();
  setCountVars();
  if (sample_noninterference_) {
    AddVariableSameOrDiff(solver, all_observe_lits, all_declass_lits);

    sample_sol_f = new std::ofstream(out_dir_ + "//" + out_file_ + ".same.csv",
                                     std::ofstream::out | std::ofstream::app);
    if (record_full_)
      sample_sol_complete_f =
          new std::ofstream(out_dir_ + "//" + out_file_ + ".same_complete.csv",
                            std::ofstream::out | std::ofstream::app);

  } else {
    complementary_solver = newCounterSolver((void *)&conf);
    readInAFile(complementary_solver, inputfile);
    AddVariableSameOrDiff(complementary_solver, all_observe_lits,
                          all_declass_lits);
    AddVariableDiff(solver, all_observe_lits);
    sample_sol_f = new std::ofstream(out_dir_ + "//" + out_file_ + ".diff.csv",
                                     std::ofstream::out | std::ofstream::app);
    if (record_full_)
      sample_sol_complete_f =
          new std::ofstream(out_dir_ + "//" + out_file_ + ".diff_complete.csv",
                            std::ofstream::out | std::ofstream::app);
    sample_sol_f_same =
        new std::ofstream(out_dir_ + "//" + out_file_ + ".same.csv",
                          std::ofstream::out | std::ofstream::app);
    if (record_full_)
      sample_sol_complete_f_same =
          new std::ofstream(out_dir_ + "//" + out_file_ + ".same_complete.csv",
                            std::ofstream::out | std::ofstream::app);
    AddVariableSame(solver, all_declass_lits);
  }
  AddVariableDiff(solver, all_secret_lits);

  vector<uint32_t> CISS = GetCIISS();
  solver->set_sampling_vars(&CISS);
  solver->simplify();
  string victim_cnf_file = out_dir_ + "//" + out_file_ + ".sol.simp";
  std::ofstream finalout(victim_cnf_file);
  solver->dump_irred_clauses_ind_only(&finalout);
  vector<Lit> ciss_assump, c_assump, s_assump, salt_assump, i_assump,
      ialt_assump;
  vector<vector<uint32_t>> ciss_added_vars, c_added_vars, s_added_vars,
      salt_added_vars, i_added_vars, ialt_added_vars;
  vector<bool> ciss_rhs, c_rhs, s_rhs, salt_rhs, i_rhs, ialt_rhs;
  std::cout << "used_vars.size()=" << used_vars.size() << std::endl;
  for (int t = 0; t < nsample; ++t) {
    ciss_assump.clear();
    ciss_added_vars.clear();
    ciss_rhs.clear();
    c_added_vars.clear();
    s_added_vars.clear();
    salt_added_vars.clear();
    salt_added_vars.clear();
    i_added_vars.clear();
    ialt_added_vars.clear();
    c_rhs.clear();
    s_rhs.clear();
    salt_rhs.clear();
    i_rhs.clear();
    ialt_rhs.clear();
    c_assump.clear();
    s_assump.clear();
    salt_assump.clear();
    i_assump.clear();
    ialt_assump.clear();
    Count::Sample(solver, CISS, num_xor_cls_, ciss_assump, ciss_added_vars,
                  ciss_rhs, lit_Undef);
    if (num_cxor_cls_ > 0)
      Count::Sample(solver, GetVars(CONTROLLED_), num_cxor_cls_, c_assump,
                    c_added_vars, c_rhs, lit_Undef);
    if (num_sxor_cls_ > 0) {
      Count::Sample(solver, GetVars(SECRET_ + "_0"), num_sxor_cls_, s_assump,
                    s_added_vars, s_rhs, lit_Undef);
      Count::Sample(solver, GetVars(SECRET_ + "_1"), num_sxor_cls_, salt_assump,
                    salt_added_vars, salt_rhs, lit_Undef);
    }
    if (num_ixor_cls_ > 0) {
      Count::Sample(solver, GetVars(OTHER_ + "_0"), num_ixor_cls_, i_assump,
                    i_added_vars, i_rhs, lit_Undef);
      if (useOtherAlt)
        Count::Sample(solver, GetVars(OTHER_ + "_1"), num_ixor_cls_,
                      ialt_assump, ialt_added_vars, ialt_rhs, lit_Undef);
    }
    ciss_assump.insert(ciss_assump.end(), c_assump.begin(), c_assump.end());
    ciss_assump.insert(ciss_assump.end(), s_assump.begin(), s_assump.end());
    ciss_assump.insert(ciss_assump.end(), salt_assump.begin(),
                       salt_assump.end());
    ciss_assump.insert(ciss_assump.end(), i_assump.begin(), i_assump.end());
    ciss_assump.insert(ciss_assump.end(), ialt_assump.begin(),
                       ialt_assump.end());

    // trimVar(solver,sample_vars);
    auto nsol = bounded_sol_generation(solver, CISS, max_sol_, ciss_assump);
    cout << "nsol=" << nsol << std::endl;
  }
}

int main(int argc, char **argv) {
  srand(time(NULL));
  Sampler sampler(argc, argv);
  // Count.conf.doRenumberVars = true;
  sampler.parseCommandLine();
  sampler.run();
}
