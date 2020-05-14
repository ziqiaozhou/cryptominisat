#include "count.h"
#include "cryptominisat5/cryptominisat.h"
#include "cryptominisat5/solvertypesmini.h"
#include "src/solver.h"
class DisjointSet { // to represent disjoint set
  vector<int> parent;

public:
  DisjointSet(int n) { parent.resize(n, -1); }
  int Find(int l) { // Find the root of the set in which element l belongs
    if (parent[l] == -1)
      return l;
    if (parent[l] == l) // if l is root
      return l;
    return Find(parent[l]); // recurs for parent till we find root
  }
  int Union(int m, int n) { // perform Union of two subsets m and n
    int x = Find(m);
    int y = Find(n);
    if (y < x)
      parent[x] = y;
    else
      parent[y] = x;
    return std::min(x,y);
  }
};

void AnalyzeClauses(const Solver *solver,const vector<ClOffset> &cls, DisjointSet &ds,  vector<int>& nclause) {
  for (vector<ClOffset>::const_iterator it = cls.begin(), end = cls.end();
       it != end; ++it) {
    auto cl=solver->clause_outer_numbered(*(solver->cl_alloc.ptr(*it)));
    int group= cl[0].var();
    for(size_t i = 1; i < cl.size(); i++) {
      group=ds.Union(group,cl[i].var());
      nclause[cl[i].var()]++;
    }
  }
}
/*void findComponent(const SATSolver *sat_solver) {
  cout << "try find component\n";
  vector<int> nclause(sat_solver->nVars());
  auto solver = sat_solver->GetSolver(0);
  if (solver->conf.sampling_vars == nullptr ||
      solver->conf.sampling_vars->size() == 0)
    return;
  size_t wsLit = 0;
  DisjointSet ds(sat_solver->nVars());
  auto first_var = solver->conf.sampling_vars->at(0);
  for (auto var : *solver->conf.sampling_vars) {
    ds.Union(first_var, var);
  }
  for (watch_array::const_iterator it = solver->watches.begin(),
                                   end = solver->watches.end();
       it != end; ++it, wsLit++) {
    Lit lit = Lit::toLit(wsLit);
    for (const Watched *it2 = it->begin(), *end2 = it->end(); it2 != end2;
         it2++) {
      if (it2->isBin() && lit < it2->lit2() && it2->red()) {
        ds.Union(lit.var(), it2->lit2().var());
        nclause[lit.var()]++;
        nclause[it2->lit2().var()]++;
      }
    }
  }
  AnalyzeClauses(solver,solver->longIrredCls,ds,nclause);
  int group = ds.Find(first_var);
  int nirrel = 0;
  for (uint32_t i = 0; i < sat_solver->nVars(); ++i) {
    if (ds.Find(i) != group) {
      cout << " " << i << "\n";
      nirrel++;
    }else if(nclause[i]<2){
      cout << "<2 " << i << "\n";
      nirrel++;
    }
  }
  cout << "number of unrelated vars:" << nirrel << "\n";
}*/
