/******************************************
Copyright (c) 2018, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "clausedumper.h"
#include "compfinder.h"
#include "comphandler.h"
#include "occsimplifier.h"
#include "solver.h"
#include "varreplacer.h"
#include"unordered_map"

using namespace CMSat;

class DisjointSet { // to represent disjoint set

public:
  std::vector<uint32_t> parent;

  DisjointSet(uint32_t n) {
    parent.resize(n);
    for(int i=0;i<n;++i) parent[i]=i;
  }
  uint32_t Find(uint32_t l) { // Find the root of the set in which element l belongs
    if (parent[l] == l) // if l is root
      return l;
    return Find(parent[l]); // recurs for parent till we find root
  }
  int Union(uint32_t m, uint32_t n) { // perform Union of two subsets m and n
    uint32_t x = Find(m);
    uint32_t y = Find(n);
    if (y < x)
      parent[x] = y;
    else
      parent[y] = x;
    return std::min(x,y);
  }
};

void AnalyzeClauses(const Solver *solver, const vector<ClOffset> &cls,
                    DisjointSet &ds, vector<int> &nclause,
                    bool outer_numbering = false) {
  for (vector<ClOffset>::const_iterator it = cls.begin(), end = cls.end();
       it != end; ++it) {
      Clause &cl = *(solver->cl_alloc.ptr(*it));

      uint32_t group = cl[0].var();
      for (size_t i = 0; i < cl.size(); i++) {
        group = ds.Union(group, cl[i].var());
        nclause[cl[i].var()]++;
    }
  }
}
void ClauseDumper::findComponent(const Solver *solver,
                                 std::map<uint32_t, bool> &useless,
                                 bool outer_numbering) {
  for (uint32_t var : *solver->conf.sampling_vars) {
    if(solver->varReplacer &&  solver->varReplacer->get_num_replaced_vars())
     var=solver->varReplacer->get_var_replaced_with_outer(var);
    var=solver->map_outer_to_inter(var);
  }
  cout << "try find component\n";
  size_t nvar = solver->nVars();

  vector<int> nclause(nvar);
  if (solver->conf.sampling_vars == nullptr ||
      solver->conf.sampling_vars->size() == 0)
    return;
  size_t wsLit = 0;
  DisjointSet ds(nvar);

  auto first_var = solver->conf.sampling_vars->at(0);
  if(solver->varReplacer &&  solver->varReplacer->get_num_replaced_vars())
   first_var=solver->varReplacer->get_var_replaced_with_outer(first_var);
  first_var=solver->map_outer_to_inter(first_var);
  for (auto var : independent_set) {
    ds.Union(first_var, var);
  }
  for (watch_array::const_iterator it = solver->watches.begin(),
                                   end = solver->watches.end();
       it != end; ++it, wsLit++) {
    Lit lit = Lit::toLit(wsLit);
    for (const Watched *it2 = it->begin(), *end2 = it->end(); it2 != end2;
         it2++) {
      if (it2->isBin() && lit < it2->lit2() && !it2->red()) {
        auto var1 = lit.var(), var2 = it2->lit2().var();

        ds.Union(lit.var(), it2->lit2().var());
        nclause[lit.var()]++;
        nclause[it2->lit2().var()]++;
      }
    }
  }
  AnalyzeClauses(solver, solver->longIrredCls, ds, nclause, outer_numbering);
  int group = ds.Find(first_var);
  int nirrel = 0;
  for (uint32_t i = 0; i < nvar; ++i) {
    if (independent_set.count(i))
      continue;
    if (ds.Find(i) != group) {
      if (outer_numbering) {
        cout << "outer_numbering " << solver->map_inter_to_outer(i) << "\t";
      } else
        cout << "useless " << i << "\t";
      useless[i] = 1;
      nirrel++;
    } else if (nclause[i] < 2) {
      cout << "<2 \t";
      if (outer_numbering) {
        cout << "outer_numbering " << solver->map_inter_to_outer(i) << "\t";
      } else
        cout << " " << i << "\t";
      // useless[i] = 1;
      // nirrel++;
    }
  }
  for (auto var : independent_set)
    useless[var] = 0;
  cout << "number of unrelated vars:" << nirrel << "\n";
}

  void ClauseDumper::write_unsat(std::ostream * out) {
    *out << "p cnf 0 1\n"
         << "0\n";
  }

  void ClauseDumper::open_file_and_write_unsat(const std::string &fname) {
    open_dump_file(fname);
    write_unsat(outfile);
    delete outfile;
    outfile = NULL;
  }

void ClauseDumper::dump_irred_clauses(std::ostream *out) {
    if (!solver->okay()) {
      write_unsat(out);
    } else {
      dump_irred_cls(out, true);
    }
    std::cout << "dump symbol\n";
    dump_symbol_vars(out);
  }

  void ClauseDumper::open_file_and_dump_irred_clauses(
      const string &irredDumpFname) {
    open_dump_file(irredDumpFname);
    try {
      dump_irred_clauses(outfile);
    } catch (std::ifstream::failure &e) {
      cout << "Error writing clause dump to file: " << e.what() << endl;
      std::exit(-1);
    }

    delete outfile;
    outfile = NULL;
  }

  void ClauseDumper::dump_red_clauses(std::ostream * out) {
    if (!solver->okay()) {
      write_unsat(out);
    } else {
      dump_red_cls(out, true);
    }
  }

  void ClauseDumper::open_file_and_dump_red_clauses(
      const string &redDumpFname) {
    open_dump_file(redDumpFname);
    try {
      dump_red_clauses(outfile);
    } catch (std::ifstream::failure &e) {
      cout << "Error writing clause dump to file: " << e.what() << endl;
      std::exit(-1);
    }
    delete outfile;
    outfile = NULL;
  }

  size_t ClauseDumper::get_preprocessor_num_cls(bool outer_numbering) {
    size_t num_cls = 0;
    num_cls += solver->longIrredCls.size();
    num_cls += solver->binTri.irredBins;
    if (!outer_numbering) {
      vector<Lit> units = solver->get_toplevel_units_internal(false);
      num_cls += units.size();
    } else {
      vector<Lit> units = solver->get_zero_assigned_lits();
      num_cls += units.size();
    }
    num_cls += solver->undef_must_set_vars.size();
    num_cls +=
        solver->varReplacer->print_equivalent_literals(outer_numbering) * 2;
    cout << "\nlong ir cls: " << solver->longIrredCls.size()
         << "\nbinIr cls: " << solver->binTri.irredBins
         << "\nundef cls:" << solver->undef_must_set_vars.size() << "\n eq cls="
         << solver->varReplacer->print_equivalent_literals(outer_numbering) * 2;
    return num_cls;
  }
  void ClauseDumper::dump_symbol_vars(std::ostream * out) {
	  if(solver->conf.symbol_vars==nullptr) return;
    for (auto one_symbol_vars : *solver->conf.symbol_vars) {
      *out << "c " << one_symbol_vars.first << " --> [";
      for ( auto lit : one_symbol_vars.second) {
        //auto outer_lit=solver->map_to_with_bva(lit);
        auto outer_lit=lit;
        if(solver->varReplacer){
           outer_lit=solver->varReplacer->get_lit_replaced_with_outer(lit);
         }

        *out << " " << Lit(solver->map_outer_to_inter(outer_lit.var()),outer_lit.sign());
      }
      *out << "]\n";
    }
    if (solver->conf.dump_ind && solver->conf.sampling_vars) {
      *out << "c ind ";
      vector<uint32_t> used(solver->nVars(), false);
      for ( auto var : *solver->conf.sampling_vars) {

        //var=solver->map_to_with_bva(var);
        auto new_var=var;
        if(solver->varReplacer &&  solver->varReplacer->get_num_replaced_vars())
         new_var=solver->varReplacer->get_var_replaced_with_outer(var);
        new_var=solver->map_outer_to_inter(var);
        if (used[new_var])
          continue;
        used[new_var] = true;
        *out << " " << new_var + 1;
      }
      *out << " 0\n";
    }
  }
  void ClauseDumper::dump_irred_clauses_preprocessor(std::ostream * out) {
    if (!solver->okay()) {
      write_unsat(out);
    } else {
      *out << "p cnf " << solver->nVars() << " "
           << get_preprocessor_num_cls(false) << "\n";
      std::cout << "dump symbol\n";
      dump_symbol_vars(out);
      dump_irred_cls_for_preprocessor(out, false);


    }
  }

  void ClauseDumper::open_file_and_dump_irred_clauses_preprocessor(
      const string &irredDumpFname) {
    open_dump_file(irredDumpFname);
    try {
      std::cout << "dump file 2--\n";
      std::ofstream f;
      f.open("renumber.map3");
      f << solver << "\n";
      for (unsigned i = 0; i < 5; ++i) {
        f << i << " " << solver->map_outer_to_inter(i) << "\n";
      }
      f.close();
      dump_irred_clauses_preprocessor(outfile);
    } catch (std::ifstream::failure &e) {
      cout << "Error writing clause dump to file: " << e.what() << endl;
      std::exit(-1);
    }
    cout << "======Dumped status:\n";
    for (auto s : comp_clauses_sizes) {
      cout << "comp-" << s.first << "\t:" << s.second << "\n";
    }
    delete outfile;
    outfile = NULL;
  }

  void ClauseDumper::dump_red_cls(std::ostream * out, bool outer_numbering) {
    if (solver->get_num_bva_vars() > 0) {
      std::cerr << "ERROR: cannot make meaningful dump with BVA turned on."
                << endl;
      exit(-1);
    }

    *out << "c --- c red bin clauses" << endl;
    dump_bin_cls(out, true, false, outer_numbering);

    *out << "c ----- red long cls locked in the DB" << endl;
    dump_clauses(out, solver->longRedCls[0], outer_numbering);

    dump_eq_lits(out, outer_numbering);
  }

  void ClauseDumper::dump_irred_cls(std::ostream * out, bool outer_numbering) {
    if (solver->get_num_bva_vars() > 0) {
      std::cerr << "ERROR: cannot make meaningful dump with BVA turned on."
                << endl;
      exit(-1);
    }

    size_t num_cls = get_preprocessor_num_cls(outer_numbering);
    num_cls += dump_blocked_clauses(NULL, outer_numbering);
    num_cls += dump_component_clauses(NULL, outer_numbering);

    *out << "p cnf " << solver->nVarsOutside() << " " << num_cls << "\n";

    dump_irred_cls_for_preprocessor(out, outer_numbering);

    *out << "c ------------------ previously eliminated variables" << endl;
    dump_blocked_clauses(out, outer_numbering);

    *out << "c ---------- clauses in components" << endl;
    dump_component_clauses(out, outer_numbering);
  }

  void ClauseDumper::dump_unit_cls(std::ostream * out, bool outer_numbering) {
    *out << "c --------- unit clauses" << endl;
    vector<Lit> lits;
    if (outer_numbering) {
      //'trail' cannot be trusted between 0....size()
      lits = solver->get_zero_assigned_lits();
    } else {
      lits = solver->get_toplevel_units_internal(false);
    }
    for (Lit lit : lits) {
      /*if (independent_set.count(lit.var()) == 0)
        continue;
        */
      *out << lit << " 0\n";
    }
  }

  uint32_t ClauseDumper::dump_blocked_clauses(std::ostream * out,
                                              bool outer_numbering) {
    assert(outer_numbering);
    uint32_t num_cls = 0;
    if (solver->conf.perform_occur_based_simp) {
      num_cls = solver->occsimplifier->dump_blocked_clauses(out);
    }
    return num_cls;
  }

  uint32_t ClauseDumper::dump_component_clauses(std::ostream * out,
                                                bool outer_numbering) {
    assert(outer_numbering);
    uint32_t num_cls = 0;
    if (solver->compHandler) {
      num_cls = solver->compHandler->dump_removed_clauses(out);
    }
    return num_cls;
  }

  void ClauseDumper::open_dump_file(const std::string &filename) {
    delete outfile;
    outfile = NULL;
    std::ofstream *f = new std::ofstream;
    f->open(filename.c_str());
    if (!f->good()) {
      cout << "Cannot open file '" << filename << "' for writing. exiting"
           << endl;
      std::exit(-1);
    }
    f->exceptions(std::ifstream::failbit | std::ifstream::badbit);
    outfile = f;
  }
  uint32_t ClauseDumper::BelongsToIndComp(const Lit &l) {
    if (indCompSet.size() == 0)
      return true;
    if (compFinder == nullptr)
      return true;
    uint32_t comp = compFinder->getVarComp(l.var());
    bool ret = indCompSet.count(comp) > 0;
    return ret ? comp + 1 : 0;
  }
  void ClauseDumper::dump_bin_cls(std::ostream * out, const bool dumpRed,
                                  const bool dumpIrred,
                                  const bool outer_number) {
    size_t wsLit = 0;
    for (watch_array::const_iterator it = solver->watches.begin(),
                                     end = solver->watches.end();
         it != end; ++it, wsLit++) {
      Lit lit = Lit::toLit(wsLit);
      watch_subarray_const ws = *it;
      uint32_t comp = BelongsToIndComp(lit);
      if (useless[lit.var()])
        continue;
      if (!comp)
        continue;
      // Each element in the watchlist
      for (const Watched *it2 = ws.begin(), *end2 = ws.end(); it2 != end2;
           it2++) {
        // Only dump binaries

        if (it2->isBin() && lit < it2->lit2()) {
          bool toDump = false;
          if (it2->red() && dumpRed)
            toDump = true;
          if (!it2->red() && dumpIrred)
            toDump = true;
          if (useless[it2->lit2().var()])
            toDump = false;
          ;
          if (toDump) {
            tmpCl.clear();
            tmpCl.push_back(lit);
            tmpCl.push_back(it2->lit2());
            if (outer_number) {
              tmpCl[0] = solver->map_inter_to_outer(tmpCl[0]);
              tmpCl[1] = solver->map_inter_to_outer(tmpCl[1]);
            }
            comp_clauses_sizes[comp]++;
            *out << tmpCl[0] << " " << tmpCl[1] << " 0\n";
          }
        }
      }
    }
  }

  void ClauseDumper::dump_eq_lits(std::ostream * out, bool outer_numbering) {
    *out << "c ------------ equivalent literals" << endl;
    solver->varReplacer->print_equivalent_literals(outer_numbering, out, this);
  }

  void ClauseDumper::dump_clauses(std::ostream * out,
                                  const vector<ClOffset> &cls,
                                  const bool outer_numbering) {
    for (vector<ClOffset>::const_iterator it = cls.begin(), end = cls.end();
         it != end; ++it) {
      Clause *cl = solver->cl_alloc.ptr(*it);
      uint32_t comp = BelongsToIndComp((*cl)[0]);
      bool to_dump=true;
      for (int i = 0; i < cl->size(); ++i) {
        if (useless[(*cl)[i].var()] == 1) {
          to_dump=false;
        }
      }
      if (!comp || !to_dump)
        continue;
      comp_clauses_sizes[comp]++;
      if (outer_numbering) {
        *out << solver->clause_outer_numbered(*cl) << " 0\n";
      } else {
        *out << *cl << " 0\n";
      }
    }
  }

  void ClauseDumper::dump_vars_appearing_inverted(std::ostream * out,
                                                  bool outer_numbering) {
    *out << "c ------------ vars appearing inverted in cls" << endl;
    for (size_t i = 0; i < solver->undef_must_set_vars.size(); i++) {
      if (!solver->undef_must_set_vars[i] ||
          solver->map_outer_to_inter(i) >= solver->nVars() ||
          solver->value(solver->map_outer_to_inter(i)) != l_Undef) {
        continue;
      }

      Lit l = Lit(i, false);
      if (!outer_numbering) {
        l = solver->map_outer_to_inter(l);
      }
      *out << l << " " << ~l << " 0"
           << "\n";
    }
  }

  void
  ClauseDumper::dump_irred_cls_for_preprocessor(std::ostream *out,
                                                const bool outer_numbering) {
    indCompSet.clear();
    if (solver->conf.sampling_vars)
    for (uint32_t var : *solver->conf.sampling_vars) {
      auto new_var=var;
      if(solver->varReplacer &&  solver->varReplacer->get_num_replaced_vars())
       new_var=solver->varReplacer->get_var_replaced_with_outer(var);
      new_var=solver->map_outer_to_inter(var);
      independent_set.insert(new_var);
    }
    //  std::cout << "dump--\n";
    if (solver->conf.sampling_vars && compFinder) {
      for (uint32_t var : *solver->conf.sampling_vars) {
        auto comp = compFinder->getVarComp(var);
        if (comp != -1) {
          indCompSet.insert(comp);
          IndCompVars[comp].push_back(var);
        }
      }
      /*  for (auto c : indCompSet)
          std::cout << c << "--\n";*/
      for (uint32_t var : *solver->conf.sampling_vars) {
        auto comp = compFinder->getVarComp(var);
        if (comp == 0)
          continue;
        if (IndCompVars[comp].size() == 1 && solver->value(var) != l_Undef) {
          //  cout << "free var:" << var + 1 << "\n";
        }
      }
      findComponent(solver, useless,outer_numbering);

    }

    dump_unit_cls(out, outer_numbering);

    dump_vars_appearing_inverted(out, outer_numbering);

    *out << "c -------- irred bin cls" << endl;
    dump_bin_cls(out, false, true, outer_numbering);

    *out << "c -------- irred long cls" << endl;
    dump_clauses(out, solver->longIrredCls, outer_numbering);

    dump_eq_lits(out, outer_numbering);
  }
