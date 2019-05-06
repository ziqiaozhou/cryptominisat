/*
 * Jaccard count
 */

#if defined(__GNUC__) && defined(__linux__)

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#endif

#include <stdio.h>
#include <stdlib.h>
#include <ctime>
#include <cstring>
#include <errno.h>
#include <string.h>
#include <sstream>
#include <iostream>
#include<fstream>
#include <iomanip>
#include <map>
#include <set>
#include <utility> 
#include <fstream>
#include <sys/stat.h>
#include <string.h>
#include <list>
#include <vector>
//#include<omp.h>
#include<pthread.h>
#include "jmc.h"
#include "src/time_mem.h"
#include "src/dimacsparser.h"
#include "cryptominisat5/cryptominisat.h"
#include "src/signalcode.h"
#include "src/clausedumper.h"
using std::cout;
using std::cerr;
using std::endl;
using boost::lexical_cast;
using std::list;
using std::map;
#define DELETE_SOLVER 0
#define PARALLEL 0
#define MAX_EXAMPLES 1
#define SIMPLE 1
std::string debug_info = "";

/*
 * convert int to binary string
 */
string binary(unsigned x, unsigned length)
{
	unsigned logSize = (x == 0 ? 1 : log2(x) + 1);
	string s;
	do {
		s.push_back('0' + (x & 1));
	} while (x >>= 1);
	for (unsigned i = logSize; i < (unsigned) length; i++) {
		s.push_back('0');
	}
	std::reverse(s.begin(), s.end());

	return s;

}
/**
 * Uniform-distributed Random bit 
 **/
string JaccardMC::GenerateRandomBits(unsigned size)
{
	string randomBits;
	std::uniform_int_distribution<unsigned> uid{0, 2147483647U};
	unsigned i = 0;
	while (i < size) {
		i += 31;
		randomBits += binary(uid(random_dev), 31);
	}
	return randomBits;
}

string JaccardMC::GenerateRandomBits_prob(unsigned size, double prob)
{
	string randomBits = "";
	std::uniform_int_distribution<unsigned> uid(0, 1000);
	unsigned i = 0;
	while (i < size) {
		i += 1;
		char x[2] = "";
		x[0] = '0' + ((uid(random_dev) <= prob * 1000) ? 1 : 0);
		randomBits += x;
	}
	std::reverse(randomBits.begin(), randomBits.end());
	return randomBits;
}

void JaccardMC::add_approxmc_options()
{
	approxMCOptions.add_options()
		("pivotAC", po::value(&pivotApproxMC)->default_value(pivotApproxMC)
		, "Max Number of solutions to check for")
		("std", po::value(&tStdError)->default_value(tStdError)
		, "STD threshold used to decide when to stop")
		("outprefix", po::value(&outPrefix)->default_value(""),
		"prefix for output filename")
		("mode", po::value(&searchMode)->default_value(searchMode)
		, "Seach mode:  Jn Mode (JaccardMC): =1, \\hat{Jn} Mode: = 3")
		("XorMax", po::value(&XorMax)->default_value(1000)
		, "default =1000, if xor is eceed this value, trim the xor by change the ratio for randombits")
		("JaccardXorRate", po::value(&jaccardXorRate)->default_value(jaccardXorRate)
		, "default =1(0-1), sparse xor can speed up, but may lose precision.VarXorRate * jaccard_size() ")
		("XorRate", po::value(&xorRate)->default_value(xorRate)
		, "default =1(0-1), sparse xor can speed up, but may lose precision.VarXorRate * jaccard_size() ")
		("printXor", po::value(&printXor)->default_value(0), "default(false)")
		("trimOnly", po::value(&trimOnly)->default_value(0), "just trim variables and not solving, default(false)")
		("onlyOne", po::value(&onlyOne)->default_value(0), "only count #<C,O > for one set S, default(false)")
		("onlyLast", po::value(&onlyLast)->default_value(0), "directly count intersection set instead of two sets separately, default(false)")
		("tApproxMC", po::value(&tApproxMC)->default_value(tApproxMC)
		, "Number of measurements")
		("tJaccardMC", po::value(&tJaccardMC)->default_value(tJaccardMC)
		, "Max Number of measurements for jaccard hash; reaching STD or exceeding tJaccardMC would stop measuring")
		("startIteration", po::value(&startIteration)->default_value(startIteration), "initial hash size, default 0")
		("lowerFib", po::value(&LowerFib)->default_value(0), "Max hash size")
		("UpperFib", po::value(&UpperFib)->default_value(0), "Min hash size")
		("looptout", po::value(&loopTimeout)->default_value(loopTimeout)
		, "Timeout for one measurement, consisting of finding pivotAC solutions")
		("logFileName", po::value(&logFileName)->default_value(logFileName), "")
		("unset", po::value(&unset_vars)->default_value(unset_vars),
		"Try to ask the solver to unset some independent variables, thereby"
		"finding more than one solution at a time")
		("notSample", po::value(&notSampled)->default_value(true),
		"do not sample manually when the set size is small"
		"default True, not sample")
		("debug", po::value(&debug)->default_value(false),
		"debug"
		"default:false")
		("JaccardIndex", po::value(&singleIndex)->default_value(singleIndex),
		"jaccard index=log(n/|S|)"
		"choose one otherwise use max")
		("test", po::value(&test_func)->default_value(0), "(Not Valid)test new feature, 0->default, 1-> hash attack first then ob")
		("diff", po::value(&is_diff)->default_value(0), "diff creation, let ob diff, ob is jac")
		("exclude", po::value(&exclude)->default_value(0), "Count solution with different ob, ob is labeled with jac and S is labeled with jac2")
		("same_set", po::value(&same_set)->default_value(0), "jac and jac2 use same set, default: false")
	("gauss_manual_setting", po::value(&gauss_manual)->default_value(0), "do not use default gauss setting, you can set by yourselfe")
		("distributionfile",po::value(&dFilename)->default_value(""),"distribution file")
		("useWeight",po::value(&useWeight)->default_value(0),"default: false");

	help_options_simple.add(approxMCOptions);
	help_options_complicated.add(approxMCOptions);
}

void JaccardMC::add_supported_options()
{
	Main::add_supported_options();
	add_approxmc_options();
}

void printVars(vector<Lit>& vars)
{
	std::stringstream ss;
	for (auto cl : vars) {
		ss << cl << " ";
	}
	std::cout << "added clause=" << ss.str() << "\n";

}

void print_xor(const vector<unsigned>& vars, const unsigned rhs, string text)
{

#if false
	std::ostream ff = cout;

	std::ostringstream filename("");
	filename << "xor.txt";
	ff.open(filename.str(), std::ofstream::out | std::ofstream::app);
#endif
	cout << text << "\n";
	cout << "x";
	for (size_t i = 1; i < vars.size(); i++) {
		cout << vars[i] + 1;
		if (i < vars.size() - 1) {
			cout << " ";
		}
	}
	cout << " " << (rhs ? "1" : "0") << endl;
#if false
	ff.close();
#endif
}

bool JaccardMC::openLogFile()
{
	LOGF.open(logFileName.c_str());
	if (!LOGF.is_open()) {
		cout << "Cannot open CUSP log file '" << logFileName
			<< "' for writing." << endl;
		exit(1);
	}
	return true;
}

template<class T>
inline T findMedian(vector<T>& numList)
{
	std::sort(numList.begin(), numList.end());
	size_t medIndex = (numList.size() + 1) / 2;
	size_t at = 0;
	if (medIndex >= numList.size()) {
		at += numList.size() - 1;
		return numList[at];
	}
	at += medIndex;
	return numList[at];
}

template<class T>
void merge(vector<T> &all, vector<T>another)
{
	all.insert(all.end(), another.begin(), another.end());
}

template<class T>
inline T findMin(vector<T>& numList)
{
	T min = std::numeric_limits<T>::max();
	for (const auto a : numList) {
		if (a < min) {
			min = a;
		}
	}
	return min;
}

/*
 * Add hash function for counting
 */
bool JaccardMC::AddHash(unsigned num_xor_cls, vector<Lit>& assumps, CMSat::SATSolver* solver)
{
	double ratio = xorRate;
	string randomBits = GenerateRandomBits_prob((independent_vars0.size()) * num_xor_cls, ratio);
	string randomBits_rhs = GenerateRandomBits(num_xor_cls);
	bool rhs = true;
	vector<unsigned> vars;
	if (ratio < 0.1) {
		std::cerr << "too low ratio... too many xor" << ratio << "num_xor_cls=" << num_xor_cls << "XorMax" << XorMax << "\n";
	}
	for (unsigned i = 0; i < num_xor_cls; i++) {
		//new activation variable
		solver->new_var();
		unsigned act_var = solver->nVars() - 1;
		assumps.push_back(Lit(act_var, true));

		vars.clear();
		vars.push_back(act_var);
		rhs = (randomBits_rhs[i] == '1');
		for (unsigned j = 0; j < independent_vars0.size(); j++) {
			if (randomBits[i * independent_vars0.size() + j] == '1')
				vars.push_back(independent_vars0[j]);
		}
		solver->add_xor_clause(vars, rhs);
		if (conf.verbosity || printXor) {
			print_xor(vars, rhs, "num_xor_cls=" + std::to_string(num_xor_cls) + "AddHash");
		}
	}
	return true;
}
/*
 * trim variables with deterministic assignment
 */
void JaccardMC::trimVar(vector<unsigned> &vars)
{
	vector<unsigned> new_vars;
	for (unsigned i = 0; i < vars.size(); ++i) {
		unsigned var = vars[i];
		vector<Lit>assume;
		std::cerr << "var=" << var;
		assume.clear();
		assume.push_back(Lit(var, true));
		double start = cpuTimeTotal();
		lbool ret0 = solver->solve(&assume);
		std::cout << "\ntime:" << cpuTimeTotal() - start;
		assume.clear();
		std::cerr << "!var=" << var;
		assume.push_back(Lit(var, false));
		lbool ret1 = solver->solve(&assume);
		if (ret0 != ret1) {
			std::cerr << "delete " << var << "\n";
		} else {
			std::cout << ((ret0 == l_True) ? "ret0=true" : "ret0!=true") << ((ret1 == l_True) ? "ret1=true" : "ret1!=true");
			new_vars.push_back(var);
		}
	}
	vars = new_vars;

}

int JaccardMC::SampledBoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps, CMSat::SATSolver* solver)
{
	size_t size = independent_vars.size();
	std::string sampleOne;

	lbool ret;
	int solutions = -2;

	unsigned samplelog = (size - assumps.size());
	if ((samplelog <= log2(maxSolutions))&&false && (notSampled == 0)) {

		unsigned sampleSize = (1 << (size - assumps.size()));
		while (independent_samples.size() < sampleSize) {
			sampleOne = GenerateRandomBits_prob(size, 0.5);
			independent_samples.insert(sampleOne);
		}
		std::set<string>::iterator sampleit = independent_samples.begin();
		solutions = 0;
		for (int i = 0; i < sampleSize; ++i) {
			sampleOne = *sampleit;
			vector<Lit> new_assumps(jassumps);
			for (int j = 0; j < size; ++j) {
				assert(sampleOne.size() > j);
				assert(independent_vars.size() > j);
				new_assumps.push_back(Lit(independent_vars[j], sampleOne[j] == '1'));
			}
			ret = solver->solve(&new_assumps);
			if (ret != l_True) {
				sampleit++;
				continue;
			}
			cachedSolutions.insert(sampleOne);
			solutions++;
			sampleit++;
		}
	}

	return solutions;
}

void pushlit2Sols(vector<string> &sols, string c)
{
	int len = sols.size();
	if (c == "*" && false) {
		for (int i = 0; i < len; i++) {
			sols.push_back(sols[i] + "0");
			sols[i] = sols[i] + "1";
		}
	} else {
		for (int i = 0; i < len; i++) {
			sols[i] = sols[i] + c;
		}
	}
}

lbool JaccardMC::solve_exclude(vector<Lit> assumps, int & count)
{
	assert(unset_vars == false);
	lbool ret;
	while (true) {
		ret = solver->solve(&assumps);
		count++;
		cout << "exclude count=" << count;
		if (ret != l_True)
			return ret;
		vector<Lit>lits;
		vector<Lit> sols;
		int var1, var2;
		for (auto var : independent_vars) {
			lits.push_back(Lit(var, solver->get_model()[var] == l_False));
			sols.push_back(Lit(var, solver->get_model()[var] == l_True));
		}
		for (unsigned index = 0; index < ob_vars.size(); ++index) {
			var1 = ob_vars[index];
			var2 = ob_vars[index];
			lits.push_back(Lit(var1, solver->get_model()[var2] == l_False));
			lits.push_back(Lit(var2, solver->get_model()[var1] == l_False));
		}
		if (solver->solve(&lits) == l_True) {
			solver->add_clause(sols);
		} else {
			break;
		}
	}
	return l_True;
}

int JaccardMC::BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps, int resultIndex, CMSat::SATSolver* solver = NULL)
{
	//    cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;
	//Set up things for adding clauses that can later be removed
#if PARALLEL 
	//	SATSolver *solver=solvers[omp_get_thread_num()];
#endif
	if (onlyLast && resultIndex < 2) {
		return 1;
	}
	cachedSubSolutions[resultIndex].clear();
	cachedFullSolutions[resultIndex].clear();
	cache_clear();
	solver->new_var();
	unsigned act_var = solver->nVars() - 1;
	vector<Lit> new_assumps(assumps);
	if (jassumps.size()) {
		new_assumps.insert(new_assumps.end(), jassumps.begin(), jassumps.end());
	}
	new_assumps.push_back(Lit(act_var, true));

	double start_time = cpuTime();
	unsigned solutions = 0;
	lbool ret;
	wsolution=0;
	int count_exclude = 0;
	while (solutions < maxSolutions) {
		double this_iter_timeout = loopTimeout - (cpuTime() - start_time);
		solver->set_timeout_all_calls(this_iter_timeout);
		if (exclude)
			ret = solve_exclude(new_assumps, count_exclude);
		else
			ret = solver->solve(&new_assumps);
		if (ret != l_True)
			break;
		size_t num_undef = 0;
		vector<string> sols = {""};
		vector<string >fullsols = {""};
		if (solutions < maxSolutions) {
			vector<Lit> lits;
			lits.push_back(Lit(act_var, false));
			if (test_func && (attack_vars.size() + ob_vars.size() > 0)) {
				for (unsigned i = 0; i < attack_vars.size(); ++i) {
					unsigned var = attack_vars[i];
					if (solver->get_model()[var] != l_Undef) {
						bool isTrue = (solver->get_model()[var] == l_True);
						lits.push_back(Lit(var, isTrue));
						pushlit2Sols(sols, isTrue ? "1" : "0");
					} else {
						num_undef++;
					}
				}
				for (unsigned i = 0; i < ob_vars.size(); ++i) {
					unsigned var = ob_vars[i];
					if (solver->get_model()[var] != l_Undef) {
						bool isTrue = (solver->get_model()[var] == l_True);
						lits.push_back(Lit(var, isTrue));
						pushlit2Sols(sols, isTrue ? "1" : "0");
					} else {
						num_undef++;
					}
				}
			} else {
				double addw=1;
				for (unsigned i = 0; i < independent_vars.size(); ++i) {
					unsigned var = independent_vars[i];
					if (solver->get_model()[var] != l_Undef) {
						bool isTrue = (solver->get_model()[var] == l_True);
						lits.push_back(Lit(var, isTrue));
						pushlit2Sols(sols, isTrue ? "1" : "0");
						pushlit2Sols(fullsols, isTrue ? "1" : "0");
						if (distribution.count(var)){
							addw=isTrue?distribution[var]:1;
							if(debug)
								cout<<"get a dis:"<<var<<",w="<<addw<<"\n:w";
						}
					} else {
						pushlit2Sols(sols, "*");
						num_undef++;
					}
					
				}
				wsolution+=addw;
			}
			if (nCounterExamples < MAX_EXAMPLES) {
				for (unsigned i = 0; i < jaccard_vars.size(); ++i) {
					unsigned var = jaccard_vars[i];
					bool isTrue=false;
					//std::cout<<"getmodel of "<<var;
					if (solver->get_model()[var] != l_Undef) {
						isTrue = (solver->get_model()[var] == l_True);
						pushlit2Sols(fullsols, isTrue ? "1" : "0");
					} else {
						pushlit2Sols(fullsols, "*");
						num_undef++;
					}
					
				}
			}
			if (lits.size() > 1)
				solver->add_clause(lits);
			if (debug >= 5)
				cout << "sol=\n";
			if (searchMode == 1) {
				for (auto one : sols) {
					//	cout<<one<<"\n";
					cachedSolutions.insert(one);
					cachedSubSolutions[resultIndex].push_back(one);

				}

				for (auto one : fullsols) {
					cachedFullSolutions[resultIndex].push_back(one);
				}
			}
		}
		if (num_undef) {
			cout << "here WOW Num undef:" << num_undef << endl;
		}

		//Try not to be crazy, 2**30 solutions is enough
		if (num_undef <= 20) {
			solutions += 1U << num_undef;
		} else {
			solutions += 1U << 20;
			cout << "WARNING, in this cut there are > 2**20 solutions indicated by the solver!" << endl;
			break;
		}
	}
	//Remove clauses added
	vector<Lit> cl_that_removes;
	cl_that_removes.push_back(Lit(act_var, false));
	solver->add_clause(cl_that_removes);

	//	cout<<"time in this loop :"<<(cpuTime()-start_time);
	if (solutions > maxSolutions) {
		solutions = maxSolutions;
	}
	//Timeout
	if (ret == l_Undef) {
		must_interrupt.store(false, std::memory_order_relaxed);
		CountOnOut = solutions;
		std::cout << "timeout,but explored count=" << solutions;
		return -1;
	}
	return solutions;
}

void JaccardMC::cache_clear()
{
	cachedSolutions.clear();
	//independent_samples.clear();
}

static void print_sol(std::vector<Lit> vars)
{
	for (size_t i = 1; i < vars.size(); i++) {
		cout << ((vars[i].sign()) ? "0" : "1");
	}
	cout << "\n";
}

int JaccardMC::BoundedSATCount_print(unsigned maxSolutions, const vector<Lit> assumps, CMSat::SATSolver * solver)
{
	// cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;
	//Set up things for adding clauses that can later be removed
#if PARALLEL 
	//	SATSolver *solver=solvers[omp_get_thread_num()];
#endif
	solver->new_var();
	unsigned act_var = solver->nVars() - 1;
	vector<Lit> new_assumps(assumps);
	new_assumps.push_back(Lit(act_var, true));

	double start_time = cpuTime();
	unsigned solutions = 0;
	lbool ret;

	int nAddedClause = 0;
	while (solutions < maxSolutions) {
		//solver->set_max_confl(10*1000*1000);
		double this_iter_timeout = loopTimeout - (cpuTime() - start_time);
		if (solutions > maxSolutions / 2 && this_iter_timeout < loopTimeout / 5) {
			this_iter_timeout = loopTimeout / 4;
		}
		solver->set_timeout_all_calls(this_iter_timeout);
		ret = solver->solve(&new_assumps);
		/*if(firstround){
			for (const unsigned i: dependent_vars) {
				vector<lit> eqlits;
				bool value=(rand()%2==1);
				eqlits.push_back(lit(act_var,false));
				eqlits.push_back(lit(i,solver->get_model()[i]==l_false));
				solver->add_clause(eqlits);
				naddedclause++;
			}
			firstround=false;
		}*/

		if (ret != l_True)
			break;

		size_t num_undef = 0;
		if (solutions < maxSolutions) {
			vector<Lit> lits;
			lits.push_back(Lit(act_var, false));
			for (const unsigned var : independent_vars) {
				if (solver->get_model()[var] != l_Undef) {
					lits.push_back(Lit(var, solver->get_model()[var] == l_True));
				} else {
					num_undef++;
				}
			}
			solver->add_clause(lits);
			nAddedClause++;
			if (debug)
				print_sol(lits);
		}

		if (num_undef) {
			cout << "WOW Num undef:" << num_undef << endl;
		}

		//Try not to be crazy, 2**30 solutions is enough
		if (num_undef <= 20) {
			solutions += (unsigned) (1U << num_undef);
		} else {
			solutions += (unsigned) (1U << 20);
			cout << "WARNING, in this cut there are > 2**20 solutions indicated by the solver!" << endl;
			break;
		}
	}
	//Remove clauses added
	vector<Lit> cl_that_removes;
	cl_that_removes.push_back(Lit(act_var, false));
	solver->add_clause(cl_that_removes);

	if (solutions > maxSolutions) {
		solutions = maxSolutions;
	}//Timeout
	else if (ret == l_Undef) {
		must_interrupt.store(false, std::memory_order_relaxed);
		std::cout << "explored count=" << solutions;
		return -1;
	}
	return solutions;
}

int JaccardMC::BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, CMSat::SATSolver * solver)
{
	vector<Lit> jassumps;
	return BoundedSATCount(maxSolutions, assumps, jassumps, 0, solver);
}

double getSTD(vector<double>cnt_list, vector<unsigned>list)
{
	auto cnt_it = cnt_list.begin();
	double std_error = 0;
	double avg = 0;

	auto minHash = findMin(list);
	int n = list.size();
	if (n <= 1)
		return 0;
	for (auto hash_it = list.begin()
		; hash_it != list.end() && cnt_it != cnt_list.end()
		; hash_it++, cnt_it++
		) {
		int this_cnt = pow(2, (*hash_it) - minHash);
		*cnt_it *= this_cnt;
		avg += (double) (1.0 * this_cnt) / n;
	}
	std_error = 0;
	for (auto cnt_it = cnt_list.begin()
		; cnt_it != cnt_list.end()
		; cnt_it++
		) {
		double x = (*cnt_it) - avg;
		if (x != 0)
			std_error += (x * x);
	}
	std_error = std_error / n;
	return std_error;

}

void SATCount::summarize()
{
	vector<unsigned>list = numHashList;
	vector<double>cnt_list = numCountList;

	auto minHash = findMin(list);
	if (list.size() <= 0) {
		return;
	}
	if (list.size() == 1) {
		cellSolCount = cnt_list[0];
		hashCount = list[0];
	}
	auto cnt_it = cnt_list.begin();
	for (auto hash_it = list.begin()
		; hash_it != list.end() && cnt_it != cnt_list.end()
		; hash_it++, cnt_it++
		) {
		int this_cnt = pow(2, (*hash_it) - minHash);
		*cnt_it *= this_cnt;
	}
	double medSolCount = findMedian(cnt_list);
	cellSolCount = medSolCount;
	hashCount = minHash;
}

int JaccardMC::OneRoundFor3NoHash(vector<vector<Lit>> jaccardAssumps, 
	vector<SATCount>& scounts, int resultIndex, CMSat::SATSolver * solver = NULL)
{
	double s[3];
	vector<Lit> assumps;
	int hashCount = 0;
	assumps.clear();
	double start_time = cpuTime();
	/*	int check= BoundedSATCount(pivotApproxMC+1,jaccardAssumps[0],solver);
		cout<<"check="<<check;*/
	if ((resultIndex == 0)&& !onlyOne) {
		int check = BoundedSATCount(pivotApproxMC + 1, assumps, jaccardAssumps[1], 1, solver);
		if (check <= 0) {
			if (debug)
				debug_info = "not found even when checking";
			return RETRY_JACCARD_HASH;
		}
	}
	int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, jaccardAssumps[resultIndex], resultIndex, solver);
	if (debug) {
		std::stringstream ss;
		for (auto cl : jaccardAssumps[resultIndex]) {
			ss << cl << " ";
		}
		cout << ss.str() << "\n";
		cout << "\ncost time:" << cpuTime() - start_time << "\n" << "count=" << currentNumSolutions;
	}
	//Din't find at least pivotApproxMC+1
	if (currentNumSolutions < pivotApproxMC + 1) {
		s[0] = useWeight?wsolution:currentNumSolutions;
		if (s[0] <= 0) {
			//unbalanced jaccard sampling, giveup
			if (debug)
				debug_info = "not found even no hash";
			return RETRY_JACCARD_HASH;
		}

		if (onlyOne) {
			s[1] = s[0];
			s[2] = s[0];
		} else {
			s[1] = useWeight?wsolution:BoundedSATCount(pivotApproxMC * 2 + 1, assumps, jaccardAssumps[1], 1, solver);
			cout << "solution s[0]" << s[0] << "s[1]" << s[1] << "\n";
			if ((s[1] <= 0 || s[0] <= 0)) {
				cout << "not found one solution" << s[0] << "\n";
				//unbalanced jaccard sampling, giveup
				return RETRY_JACCARD_HASH;
			}
			s[2] = cachedSolutions.size(); 
			if(useWeight){
				BoundedSATCount(s[1]+s[0],assumps,jaccardAssumps[2],2,solver);
				s[2]=wsolution;
			}
			cache_clear();
			if (s[2] <= 0 || s[2]>(s[1] + s[0])) {
				//impossible reach
				assert(0);
				return RETRY_JACCARD_HASH;
				//goto resample;
			}
		}
		scounts[resultIndex].numHashList.push_back(hashCount);
		scounts[resultIndex].numCountList.push_back(s[0]);
		scounts[resultIndex].summarize();
		return 0;
	} else
		hashCount++;
	return hashCount;
}

int JaccardMC::OneRoundFor3WithHash(bool readyPrev, bool readyNext, 
	std::set<std::string> nextCount, unsigned &hashCount, map<unsigned, 
	Lit>& hashVars, vector<Lit>assumps, vector<vector<Lit>> jaccardAssumps, 
	vector<SATCount>& scounts, int resultIndex, SATSolver * solver = NULL)
{
	int repeatTry = 0;
	int pivotApproxMC0 = pivotApproxMC;
	if (hashCount == 0) {
		int ret = OneRoundFor3NoHash(jaccardAssumps, scounts, resultIndex, solver);
		if (ret == 0)
			return GOT_RESULT_LOWER;
		if (ret < 0) {
			return RETRY_JACCARD_HASH;
		}

		hashCount = ret;
		return TOO_MUCH;
	}

	while (true) {
		SetHash(hashCount, hashVars, assumps, solver);
		double s[3];
		double myTime = cpuTimeTotal();
		if (resultIndex == 0)
			cache_clear();
		/*	if(printXor)
			exit(0);*/
		if (resultIndex > 1) {
			pivotApproxMC0 *= 2;
		}
		int currentNumSolutions = BoundedSATCount(pivotApproxMC0 + 1, assumps, jaccardAssumps[resultIndex], resultIndex, solver);


		s[0] = useWeight?wsolution:currentNumSolutions;
		if (debug)
			cout << "solver->nvar()=" << solver->nVars()
			<< "Number of XOR hashes active: " << hashCount << endl
			<< currentNumSolutions << ", " << pivotApproxMC0
			<< ",time=" << (cpuTimeTotal() - myTime) << endl;

		if (currentNumSolutions < 0) {
			//Remove all hashes
			if (repeatTry < 2) { /* Retry up to twice more */
				assert(hashCount > 0);
				//hashCount-=lower+repeatTry;
				if (debug)
					cout << "repeatTry=" << repeatTry << "Timeout, try again -- " << repeatTry << "hash=" << hashCount << endl;
				repeatTry += 1;
				return TIMEOUT;
				continue;
			} else {
				//this set of hashes does not work, go up
				//SetHash(hashCount + 1, hashVars, assumps,solver);
				if (debug)
					cout << "Timeout, moving up" << endl;
				return RETRY_JACCARD_HASH;
			}
			continue;
		}

		if (currentNumSolutions < pivotApproxMC0 + 1) {

			if (readyPrev || currentNumSolutions > (pivotApproxMC0 + 1)*4 / 7) {
				if ((currentNumSolutions == 0) && (hashCount == 0))
					return RETRY_JACCARD_HASH;
				if ((currentNumSolutions == 0)&& (hashCount > 0)) {
					return RETRY_IND_HASH;
				}
				//double myTime1 = cpuTimeTotal();
				if (onlyOne) {
					s[1] = s[0];
				} else {
					s[1] = BoundedSATCount(pivotApproxMC * 2 + 1, assumps, jaccardAssumps[1], 1, solver);
					s[1]=useWeight?wsolution:s[1];
					if (s[1] < 0 || s[1] > pivotApproxMC * 2) {
						//unbalanced sampling, giveup
						if (debug)
							cout << "s[1]=" << s[1] << "\n";
						assumps.clear();
						hashVars.clear();
						solver->simplify(&assumps);
						return RETRY_JACCARD_HASH;
						//return NEAR_RESULT;
					}
					double myTime2 = cpuTimeTotal();
					s[2] = cachedSolutions.size(); // BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);
					std::cout << "s[2]" << s[2] << ",time:" << cpuTimeTotal() - myTime2 << "\n";
					if (s[2] < 0 || s[2]>(s[1] + s[0])) {
						//impossible reach
						assumps.clear();
						hashVars.clear();
						solver->simplify(&assumps);
						return RETRY_JACCARD_HASH;
					}
				}
				scounts[resultIndex].numHashList.push_back(hashCount);
				scounts[resultIndex].numCountList.push_back(s[0]);
				return GOT_RESULT_LOWER;
			}
			//return NEAR_RESULT;
			return currentNumSolutions;
		} else {
			if (readyNext) {
				hashCount++;
				SetHash(hashCount, hashVars, assumps, solver);
				//	s[0]=nextCount;
				double myTime1 = cpuTimeTotal();
				cache_clear();
				cachedSolutions.insert(nextCount.begin(), nextCount.end());
				cachedSubSolutions[resultIndex].clear();

				cachedFullSolutions[resultIndex].clear();
				for (auto one : cachedSolutions) {
					cachedSubSolutions[resultIndex].push_back(one.substr(0, independent_vars.size()));
					cachedFullSolutions[resultIndex].push_back(one);
				}
				s[0] = nextCount.size();

				//s[0]= BoundedSATCount(pivotApproxMC*2+1,assumps,jaccardAssumps[0],solver);
				if (onlyOne) {
					s[1] = s[0];
				} else{
					s[1] = BoundedSATCount(pivotApproxMC0 * 2 + 1, assumps, jaccardAssumps[1], 1, solver);
					s[1]=useWeight?wsolution:s[1];
					std::cout << "s[1]" << s[1] << ",time:" << cpuTimeTotal() - myTime1 << "\n";
					cout << "s[0]=" << s[0] << "s[1]" << s[1];
					if (s[1] <= 0) {
					//unbalanced sampling, giveup
					assumps.clear();
					hashVars.clear();
					solver->simplify(&assumps);
					return RETRY_JACCARD_HASH;
					}
					if (s[1] > pivotApproxMC0 * 2 + 1) {
					return RETRY_JACCARD_HASH;
					}
				}
				myTime1 = cpuTimeTotal();
				for (auto one : cachedSolutions) {
					//		cout<<"one="<<one<<"\n";
				}
				s[2] = cachedSolutions.size();
				//s[2]= BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);

				if (s[2] <= 0 || s[2]>(s[1] + s[0])) {
					//impossible reach
					assert(0);
				}
				scounts[resultIndex].numHashList.push_back(hashCount);
				scounts[resultIndex].numCountList.push_back(s[0]);
				return GOT_RESULT_UPPER;
			}

			assert(currentNumSolutions == pivotApproxMC0 + 1);
			return TOO_MUCH;
		}
	}
}

void printFor3(int ret)
{
	string str;
	switch (ret) {
	case RETRY_IND_HASH:
		str = "RETRY_IND_HASH";
		break;

	case RETRY_JACCARD_HASH:
		str = "RETRY_JACCARD_HASh";
		break;
	case GOT_RESULT_UPPER:
		str = "GOT_RESULT_upper";
		break;

	case GOT_RESULT_LOWER:
		str = "GOT_RESULT";
		break;


	case TOO_MUCH:
		str = "TOO_MUCH";
		break;
	case TIMEOUT:
		str = "TIMEOUT";
		break;
	default:
		str = "NEAR_RESULT";
		break;
	}
	std::cout << str << ":" << debug_info;
	debug_info = "";
}

int getAttackNum(int nattack, vector<string>all)
{
	std::set<string> attack;
	for (auto one : all) {
		attack.insert(one.substr(0, nattack));
	}
	return attack.size();
}

vector<size_t> sort_indexes(const vector<string> &v)
{

	// initialize original index locations
	vector<size_t> idx(v.size());
	iota(idx.begin(), idx.end(), 0);

	//       // sort indexes based on comparing values in v
	sort(idx.begin(), idx.end(),
		[&v](size_t i1, size_t i2)
		{
			return v[i1] < v[i2];
		});

	return idx;
}

string str2hex(string s)
{
	char * end;

	std::stringstream ss("");
	for (int i = 0; i < s.size() / 8; ++i) {
		string sub = s.substr(i * 8, 8);
		std::reverse(sub.begin(), sub.end());
		long int value = strtol(sub.c_str(), &end, 2);
		char c = value;
		ss << value << "(" << c << ")";
	}
	return ss.str() + "\t" + s;
}

int JaccardMC::OneRoundForHatJ(unsigned jaccardHashCount, JaccardResult* result, 
	unsigned &mPrev, unsigned &hashPrev, vector<vector<Lit>> jaccardAssumps, 
	vector<std::pair<unsigned, double>>&scounts)
{
	unsigned pivot = pivotApproxMC;
	unsigned& hashCount = result->hashCount[jaccardHashCount];
	unsigned initialHashCount = 0;
	bool& searched = result->searched[jaccardHashCount];
	vector<Lit> assumps;
	map<unsigned, Lit> hashVars; //map assumption var to XOR hash
	double myTime = cpuTimeTotal();
	unsigned jaccardIndex = jaccardHashCount;
	bool less = false, more = false;
	int resultIndex = 0;
	assert(3 == jaccardAssumps.size());

	unsigned lower = LowerFib, upper = (UpperFib > 0) ? UpperFib : independent_vars.size() - ceil(log(pivot) / log(2)) + 2;
	// resultIndex : 0-> <C,O,I > for S, 1 -> <C,O,I> for S', and 2->  <C,O,I> intersection
	for (resultIndex = 0; resultIndex < jaccardAssumps.size(); resultIndex++) {
		if (resultIndex == 1 && 
					std::equal(jaccardAssumps[1].begin(), \
						jaccardAssumps[1].end(), jaccardAssumps[0].begin()))
		{// S and S' are the same, use <C,O> in S as <C,O> in S'
			scounts.push_back(scounts[0]);
			continue;
		}
retry:
		if (debug)
		  cout << "resultIndex=" << resultIndex << "\n";
		if (resultIndex == 0) {
			assumps.clear();
			hashVars.clear();
		}
		if (onlyLast && resultIndex < 2) {
			// Only compute when the resultIndex==2
			scounts.push_back(std::pair<unsigned, double>(0, 1));
			continue;
		}
		if (solver == NULL) {
			solver = this->solver;
		}
		hashCount = hashCount ? hashCount : initialHashCount;
		if (resultIndex == 2) {
			lower = LowerFib;
			//upper=(UpperFib>0)?UpperFib:independent_vars.size()-ceil(log(pivot)/log(2))+2;
		} else {
			lower = LowerFib;
			upper = (UpperFib > 0) ? UpperFib : independent_vars.size() - ceil(log(pivot) / log(2)) + 2;
		}

		double nSol = 0;
		if (debug > DEBUG_HASH_LEVEL)
			printVars(jaccardAssumps[resultIndex]);
		if (hashCount == 0) {
			SetHash(hashCount, hashVars, assumps, solver);
			int checksol = BoundedSATCount(pivot + 1, assumps, jaccardAssumps[resultIndex], resultIndex, solver);
			nSol=wsolution;
			if (checksol == 0) {
				scounts.push_back(std::pair<unsigned, double>(hashCount, useWeight?wsolution:nSol));
				if (debug > DEBUG_VAR_LEVEL)
					cout << "nSol=0\n";
				if (resultIndex < 2)
					return -1;
				else {
					continue;
				}
			}
			if (checksol > (int)pivot)
				hashCount = lower + 1;
			else {
				scounts.push_back(std::pair<unsigned, double>(hashCount, nSol));
				continue;
			}
		}
		unsigned prevHash = hashCount;
		int prevCount = 0;
		unsigned next = hashCount;
		map<unsigned, unsigned> nSols;
		bool notZero = false;
		int timeoutcount = 0;
		int checksol =1;
		while (upper - lower > 0) {
			if (next != hashCount) {
				hashCount = next;
			}
			if(hashCount>upper|| hashCount<lower){
				cerr<<"error hash count"<<hashCount;
				break;
			}
			if (nSols.find(hashCount) == nSols.end()) {
				SetHash(hashCount, hashVars, assumps, solver);
				double myTime = cpuTimeTotal();
				if (debug)
					cout << "hashCount" << hashCount << "assumps.size=" << assumps.size();
				checksol= BoundedSATCount(pivot + 1, assumps, jaccardAssumps[resultIndex], resultIndex, solver);
				nSol=wsolution;
				if (debug)
					cout << ",time=" << (cpuTimeTotal() - myTime) << endl;
			} else {
				nSol = nSols[hashCount];
				checksol=1;
			}
			if (debug > DEBUG_VAR_LEVEL)
				cout << "hashCount=" << hashCount << "nSol=" << nSol << "\n";
			if (checksol == -1) {
				if (debug)
					cout << "timeout";
				if (timeoutcount > 2 || CountOnOut < 1)//return -1 if timeout>=3 for one hashCount
					return -1;
				timeoutcount++;
				if (resultIndex == 2) {
					scounts.pop_back();
					scounts.pop_back();
					resultIndex = 0;
					assumps.clear();
					hashVars.clear();
					lower = LowerFib, upper = (UpperFib > 0) ? UpperFib : independent_vars.size() - ceil(log(pivot) / log(2)) + 2;
					goto retry;
				}
				assumps.clear();
				hashVars.clear();
				continue;
			}
			timeoutcount = 0;
			if (checksol > pivot) {
				notZero = true;
				lower = hashCount + 1;
				next = hashCount * 2;
				next = (next > upper) ? ceil(1.0 * lower + upper) / 2 : next;
				nSols.insert(std::pair<unsigned, unsigned>(hashCount, nSol));
			} else {
				if (checksol > 0)
					notZero = true;
				nSols.insert(std::pair<unsigned, unsigned>(hashCount, nSol));
				if (checksol * 1.3 > pivot) {
					lower = hashCount;
					upper = hashCount;
					break;
				}
				upper = hashCount;
				next = (lower + upper) / 2;
			}
		}
		hashCount = lower;
		nSol = nSols[hashCount];
		if (notZero && (nSol == 0)) {
			for (auto one : nSols) {
				if (one.second > 0) {
					if ((one.first > nSol)&&(one.second<hashCount)) {
						hashCount = one.second;
						nSol = one.first;
					}
				}
			}
		}
		if (nSol == 0 && resultIndex < 2) {
			cout << "get zero count, error!! retry\n" << "lower=" << lower << "higher=" << upper << "\n";
			resultIndex--;

			if (hashCount == 0) {
				return -1;
			}

			hashCount = lower + ceil(log(pivot) / log(2));
		}
		if (debug > DEBUG_VAR_LEVEL)
			cout << "get hashCount=" << hashCount << "nSol=" << nSol << "\n";

		if (nSol == 0 && (resultIndex < 2 || onlyLast)) {
			return -1;
		}
		scounts.push_back(std::pair<unsigned, double>(hashCount, nSol));
	}
	return 0;
}

int JaccardMC::OneRoundFor3(unsigned jaccardHashCount, JaccardResult* result, unsigned &mPrev, unsigned &hashPrev, vector<vector<Lit>> jaccardAssumps, vector<SATCount>& scounts, SATSolver * solver = NULL)
{
	//	solver->simplify(&jaccardAssumps);
	unsigned& hashCount = result->hashCount[jaccardHashCount];
	unsigned initialHashCount = 0;
	bool& searched = result->searched[jaccardHashCount];
	vector<Lit> assumps;

	map<unsigned, Lit> hashVars; //map assumption var to XOR hash
	double myTime = cpuTimeTotal();
	unsigned jaccardIndex = jaccardHashCount;
	bool less = false, more = false;
	if (solver == NULL) {
		solver = this->solver;
	}
	hashCount = hashCount ? hashCount : LowerFib;
	int resultIndex = 0;
	for (unsigned j = 0; j < tApproxMC * 3; j++) {
		map<unsigned, std::set<std::string> > countRecord;
		map<unsigned, unsigned> succRecord;
		unsigned repeatTry = 0;
		unsigned numExplored = 1;
		//	unsigned lowerFib = searched?(hashCount-2):0, upperFib = searched?(hashCount+2):independent_vars.size();
		//
		unsigned lowerFib = LowerFib, upperFib = UpperFib ? UpperFib : independent_vars.size();
		int oldResultIndex = 0;
		while (numExplored < independent_vars.size()) {
			myTime = cpuTimeTotal();
			unsigned swapVar = hashCount;
			//cout<<"change the size to "<<solver->get_Nclause();
			//solver->simp:lify(&assumps);
			oldResultIndex = resultIndex;
			bool readyPrev = ((succRecord.find(hashCount - 1) != succRecord.end())&&(succRecord[hashCount - 1] == 1));
			bool readyNext = ((succRecord.find(hashCount + 1) != succRecord.end())&&(succRecord[hashCount + 1] == 0));
			if (resultIndex == 2)
				readyPrev = true;
			std::set<std::string> nextCount;
			if (succRecord.find(hashCount + 1) != succRecord.end()) {
				nextCount = countRecord[hashCount + 1];
			}
			if (debug)
				std::cout << "\n------------------------resultIndex=" << resultIndex << "\n";
			int ret = OneRoundFor3WithHash(readyPrev, readyNext, nextCount, hashCount, hashVars, assumps, jaccardAssumps, scounts, resultIndex, solver);
			if (debug)
				printFor3(ret);
			int checkJaccard;
			switch (ret) {
			case TIMEOUT:
				assumps.clear();
				hashVars.clear();
				for (int i = 0; i < resultIndex; ++i) {
					scounts[i].pop_back();
				}
				resultIndex = 0;

				break;
			case RETRY_IND_HASH:
				assumps.clear();
				hashVars.clear();
				for (int i = 0; i < resultIndex; ++i) {
					scounts[i].pop_back();
				}
				resultIndex = 0;

				break;

			case RETRY_JACCARD_HASH:
				assumps.clear();
				hashVars.clear();
				for (int i = 0; i < resultIndex; ++i) {
					scounts[i].pop_back();
				}
				resultIndex = 0;

				return -1;
			case GOT_RESULT_LOWER:
				//	if(hashCount==0){
				numExplored = independent_vars.size() + 1;
				//	}else{
				//	numExplored = lowerFib+independent_vars.size()-hashCount;
				//	}
				mPrev = hashCount;
				goto reset_for_next_count;
				break;
			case GOT_RESULT_UPPER:
				//		numExplored= independent_vars.size()+1;
				numExplored = independent_vars.size() + hashCount - upperFib;

				mPrev = hashCount;
reset_for_next_count:
				if (!onlyOne)
					resultIndex = (resultIndex + 1) % 3;
				break;

			case TOO_MUCH:
				numExplored = hashCount + independent_vars.size() - upperFib;
				succRecord[hashCount] = 1;
				searched = false;
				if (searched || (abs((int)hashCount - (int)mPrev) < 2 && mPrev != 0)) {
					lowerFib = hashCount;
					hashCount++;
				} else //if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) 
				{
					lowerFib = hashCount;
					hashCount = (lowerFib + upperFib) / 2;
				}/* else {
						//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
						if(hashCount)
						  hashCount = lowerFib + (hashCount -lowerFib)*2;
						else
						  hashCount++;

					}*/
				hashPrev = swapVar;
				break;
			default:
				//case NEAR_RESULT:
				if (hashCount == 0) {
					numExplored = independent_vars.size() + 1;
					mPrev = hashCount;
					succRecord[hashCount] = 0;
					scounts[resultIndex].numHashList.push_back(hashCount);
					scounts[resultIndex].numCountList.push_back(ret);

					if (!onlyOne)
						resultIndex = (resultIndex + 1) % 3;
					//	assert(ret==cachedSolutions.size());
					std::set<std::string> s(cachedFullSolutions[resultIndex].begin(), cachedFullSolutions[resultIndex].end());
					countRecord[hashCount] = s;
				} else {
					numExplored = lowerFib + independent_vars.size() - hashCount;
					succRecord[hashCount] = 0;
					//	assert(ret==cachedSolutions.size());
					std::set<std::string> s(cachedFullSolutions[resultIndex].begin(), cachedFullSolutions[resultIndex].end());
					countRecord[hashCount] = s;

TOO_SMALL_ENTRY:
					if (searched || (abs((int)hashCount - (int)mPrev) <= 2 && mPrev != 0)) {
						upperFib = hashCount;
						hashCount--;
					} else {
						if (hashPrev > hashCount) {
							hashPrev = 0;
						}
						upperFib = hashCount;
						if (hashPrev > lowerFib) {
							lowerFib = hashPrev;
						}
						hashCount = (upperFib + lowerFib) / 2;
					}
				}
				break;
			}
			if (debug > DEBUG_VAR_LEVEL) {
				std::cout << "lowerFib=" << lowerFib << "upperFib=" << upperFib << "hashCount=" << hashCount;
				std::cout << "\n====================" << "\n";
			}
		}
		int nattack = attack_vars.size();
		if (resultIndex == 0) {
			std::ofstream f;
			std::ostringstream filename("");
					filename<<outPrefix<<"count_j"<<jaccardHashCount<<"_t0";
			f.open(filename.str(), std::ofstream::out | std::ofstream::app);
			unsigned i = scounts[0].size();
			if (i > 0) {
				i--;
				assert(scounts[0].size() == scounts[1].size());
				assert(scounts[2].size() == scounts[1].size());
				f << scounts[0].str(i) << "\t" << scounts[1].str(i) << "\t" << scounts[2].str(i) << "\n";
			}
			f.close();
		}
		if ((!onlyOne) && resultIndex == 0 && oldResultIndex == 2 && debug > 6) {
			assumps.clear();
			hashVars.clear();
			/*get count of attack */
			vector<string> l = cachedSubSolutions[0], r = cachedSubSolutions[1];
			std::vector<string>intersection(l.size() + r.size());
			std::vector<string>::iterator it;


			vector<size_t>oindexL = sort_indexes(l);
			vector<size_t>oindexR = sort_indexes(r);
			for (auto ll : l) {
				std::cout << "L=" << ll << "\n";
			}
			for (auto ll : r) {
				std::cout << "R=" << ll << "\n";
			}

			//	std::cout<<"r sorted:\n";
			//		for( const auto& str : l ) std::cout << str << '\n' ;

			std::vector<string>symmetric_diff(pivotApproxMC * 2);
			it = std::set_symmetric_difference(l.begin(), l.end(), r.begin(), r.end(), symmetric_diff.begin());
			if (it != symmetric_diff.begin()) {
				symmetric_diff.resize(it - symmetric_diff.begin());

				for (auto sym : symmetric_diff) {
					std::cout << "sym=" << sym << "\n";
				}
			} else {
				symmetric_diff.clear();
			}
			if (symmetric_diff.size() > 0 && nCounterExamples < MAX_EXAMPLES) {
				cout << "size of l=" << l.size() << "size of r" << r.size() << "\n";
				nCounterExamples += symmetric_diff.size();
				int lindex, rindex;
				lindex = rindex = 0;
				std::ostringstream filename("");
				filename << jaccardIndex << "_diff_examples.txt";
				std::ofstream f;
				f.open(filename.str(), std::ofstream::out | std::ofstream::app);
				f << "----\n";
				while (lindex < l.size() && rindex < r.size()) {
					if (l[lindex] == r[lindex]) {

						cout << "l:" << str2hex(l[lindex]) << "r:" << str2hex(r[lindex]) << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
						f << "c " << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
						lindex++;
						rindex++;
					} else if (l[lindex] < r[lindex]) {
						cout << "l:" << str2hex(l[lindex]) << "r:" << str2hex(r[lindex]) << "full l:" << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
						f << "l " << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
						lindex++;
					} else {
						cout << "l:" << str2hex(l[lindex]) << "r:" << str2hex(r[lindex]) << "full r:" << str2hex(cachedFullSolutions[1][oindexR[rindex]]) << "\n";
						f << "r " << str2hex(cachedFullSolutions[1][oindexR[rindex]]) << "\n";
						rindex++;
					}
				}
				while (lindex < l.size()) {
					cout << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
					f << "l " << str2hex(cachedFullSolutions[0][oindexL[lindex]]) << "\n";
					lindex++;
				}
				while (rindex < r.size()) {

					cout << str2hex(cachedFullSolutions[1][oindexR[rindex]]) << "\n";
					f << "r " << str2hex(cachedFullSolutions[1][oindexR[rindex]]) << "\n";
					rindex++;
				}
				f << "========\n";
				f.close();
			}
			/*	std::cout<<"inter sorted:\n";
			for( const auto& str : intersection ) std::cout << str << '\n' ;

				std::cout<<"diff sorted:\n";
			for( const auto& str : symmetric_diff ) std::cout << str << '\n' ;*/
			//		int ndiff=getAttackNum(nattack,symmetric_diff);

			//	scounts[3].numCountList.push_back(ninter);
			//	scounts[4].numCountList.push_back(ndiff);

			//	solver->simplify(&assumps);
		}
		if (hashCount == 0 && resultIndex == 0) {
			break;
		}
		hashCount = mPrev;
	}
	return 0;
}

int JaccardMC::OneRoundCount(unsigned jaccardHashCount, JaccardResult* result, unsigned &mPrev, unsigned &hashPrev, vector<Lit> jaccardAssumps, SATCount& count, SATSolver * solver = NULL)
{
	//	solver->simplify(&jaccardAssumps);
	unsigned& hashCount = result->hashCount[jaccardHashCount];
	bool& searched = result->searched[jaccardHashCount];
	vector<Lit> assumps;
	double myTime = cpuTimeTotal();

	vector<unsigned>numHashList0, *numHashList = &numHashList0;
	vector<double> numCountList0, * numCountList = &numCountList0;
	unsigned jaccardIndex = jaccardHashCount;
	bool less = false, more = false;
	if (solver == NULL) {
		solver = this->solver;
	}
	//	hashCount=startIteration;
	if (hashCount == 0) {
		int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, jaccardAssumps, 0, solver);
		//Din't find at least pivotApproxMC+1
		if (currentNumSolutions <= pivotApproxMC) {
			count.cellSolCount = currentNumSolutions;
			count.hashCount = 0;
			return 0;
		} else
			hashCount++;
	}
	//	hashCount=startIteration;
	for (unsigned j = 0; j < tApproxMC; j++) {
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		map<unsigned, Lit> hashVars; //map assumption var to XOR hash

		unsigned repeatTry = 0;
		unsigned numExplored = 1;
		unsigned lowerFib = 0, upperFib = independent_vars.size();
		while (numExplored < independent_vars.size()) {
			myTime = cpuTimeTotal();
			unsigned swapVar = hashCount;
			SetHash(hashCount, hashVars, assumps, solver);
			int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, jaccardAssumps, 0, solver);
			double currTime = cpuTimeTotal() - myTime;
			if (debug)
				cout << "Num Explored: " << numExplored
				<< "solver->nvar()=" << solver->nVars()
				<< "Number of XOR hashes active: " << hashCount << ",jaccard=" << jaccardHashCount << endl
				<< currentNumSolutions << ", " << pivotApproxMC
				<< ",time=" << (cpuTimeTotal() - myTime) << endl;
			/*	if(currTime>4*prevTime)
				pivotApproxMC*=2;
			 */
			//Timeout!
			if (currentNumSolutions < 0) {
				//Remove all hashes
				assumps.clear();
				hashVars.clear();
				if (repeatTry < 2) { /* Retry up to twice more */
					assert(hashCount > 0);
					hashCount -= 2;
					solver->simplify(&assumps);
					SetHash(hashCount, hashVars, assumps, solver);
					repeatTry += 1;
				} else {
					//this set of hashes does not work, go up
					//SetHash(hashCount + 1, hashVars, assumps,solver);
					return -1;
				}

				continue;
			}
			if (currentNumSolutions == 0) {
				return -1;
			}
			if (!searched) {
				if (currentNumSolutions < pivotApproxMC + 1) {
					numExplored = lowerFib + independent_vars.size() - hashCount;
					if (succRecord.find(hashCount - 1) != succRecord.end()
						&& succRecord[hashCount - 1] == 1
						) {
						numHashList->push_back(hashCount);
						numCountList->push_back(currentNumSolutions);
						mPrev = hashCount;
						//less than pivotApproxMC solutions
						break;
					}
					succRecord[hashCount] = 0;
					countRecord[hashCount] = currentNumSolutions;
					if (abs((int)hashCount - (int)mPrev) <= 2 && mPrev != 0) {
						upperFib = hashCount;
						hashCount--;
					} else {
						if (hashPrev > hashCount) {
							hashPrev = 0;
						}
						upperFib = hashCount;
						if (hashPrev > lowerFib) {
							lowerFib = hashPrev;
						}
						hashCount = (upperFib + lowerFib) / 2;
					}

				} else {
					assert(currentNumSolutions == pivotApproxMC + 1);
					numExplored = hashCount + independent_vars.size() - upperFib;
					if (succRecord.find(hashCount + 1) != succRecord.end()
						&& succRecord[hashCount + 1] == 0
						) {
						numHashList->push_back(hashCount + 1);
						numCountList->push_back(countRecord[hashCount + 1]);
						mPrev = hashCount + 1;
						break;
					}
					succRecord[hashCount] = 1;
					if (abs((int)hashCount - (int)mPrev) < 2 && mPrev != 0) {
						lowerFib = hashCount;
						hashCount++;
					} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib - 1) {
						lowerFib = hashCount;
						hashCount = (lowerFib + upperFib) / 2;
					} else {
						//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
						hashCount = lowerFib + (hashCount - lowerFib)*2;
					}
				}
				hashPrev = swapVar;
			} else {//already searched hashCount is precise enough
				if (currentNumSolutions == 0) {
					if (solver->solve(&jaccardAssumps) == l_False)
						return -1;
					if (solver->solve(&assumps) == l_False)
						return -1;
				}
				if (currentNumSolutions < pivotApproxMC + 1) {
					numExplored = lowerFib + independent_vars.size() - hashCount;
					mPrev = hashCount;
					numHashList->push_back(hashCount);
					numCountList->push_back(currentNumSolutions);
					hashCount = hashCount - 1;
					upperFib = hashCount;
				} else {
					numExplored = hashCount + independent_vars.size() - upperFib;
					lowerFib = hashCount;
					hashCount = hashCount + 1;
					mPrev = hashCount + 1;
				}
			}
		}
		assumps.clear();
		solver->simplify(&assumps);
		hashCount = mPrev;
	}
	if (numHashList->size() == 0) {
		count.cellSolCount = 0;
		count.hashCount = 0;
	} else {
		auto minHash = findMin(*numHashList);

		auto cnt_it = numCountList->begin();
		for (auto hash_it = numHashList->begin()
			; hash_it != numHashList->end() && cnt_it != numCountList->end()
			; hash_it++, cnt_it++
			) {
			*cnt_it *= pow(2, (*hash_it) - minHash);
		}

		int medSolCount = findMedian(*numCountList);
		count.cellSolCount = medSolCount;
		count.hashCount = minHash;
		count.numHashList = *numHashList;
		count.numCountList = *numCountList;
	}
	if (debug)
		cout << ",Avg[" << jaccardIndex << "]=" << count.cellSolCount << "*2^" << count.hashCount << endl;
	return 0;
}

void JaccardMC::addKey2Map(unsigned jaccardHashCount, map<unsigned, vector<unsigned>> &numHashList, map<unsigned, vector<double>>&numCountList, map<unsigned, SATCount>& count)
{
	if (numHashList.find(jaccardHashCount) == numHashList.end()) {
		vector<unsigned> oneHashList;
		vector<double> oneCountList;
		numHashList[jaccardHashCount] = (oneHashList);
		numCountList[jaccardHashCount] = (oneCountList);
		SATCount onecount;
		count[jaccardHashCount] = (onecount);
	}
}

void JaccardMC::JaccardOneRoundFor3(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, SATSolver* solver = NULL)
{
	if (solver == NULL)
		solver = solver;
	map<unsigned, vector<unsigned>> &numHashList = result->numHashList;
	map<unsigned, vector<double>>&numCountList = result->numCountList;
	map<unsigned, SATCount>& count = result->count;
	unsigned &hashCount = result->hashCount[jaccardHashCount];
	map<unsigned, Lit> jaccardHashVars;
	unsigned mPrev = 0;
	vector<Lit >jaccardAssumps, jaccardAssumps_lastZero, jaccardAssumps_two;
	int ret;
	vector<vector < Lit>> jaccard3Assumps;
	while (true) {
		jaccardAssumps.clear();
		jaccardAssumps_lastZero.clear();
		jaccardHashVars.clear();
		jaccardXorClause.clear();
		//jaccard_samples.clear();
		jaccard3Assumps.clear();
		//solver->simplify(&jaccardAssumps);
		if ((jaccard_vars.size() - jaccardHashCount) > 2 || notSampled) {
			if (jaccardHashCount) {
				SetJaccardHash(jaccardHashCount, jaccardHashVars, jaccardAssumps, jaccardAssumps_lastZero, solver);
				jaccardAssumps_two = jaccardAssumps_lastZero;
				jaccardAssumps_two.pop_back();
			}
			jaccard3Assumps.push_back(jaccardAssumps);
			jaccard3Assumps.push_back(jaccardAssumps_lastZero);
			jaccard3Assumps.push_back(jaccardAssumps_two);
		} else {
			jaccard3Assumps.push_back(jaccardAssumps);
			jaccard3Assumps.push_back(jaccardAssumps_lastZero);
			jaccard3Assumps.push_back(jaccardAssumps_two);
			SetSampledJaccardHash(jaccardHashCount, jaccardHashVars, jaccard3Assumps, solver);
		}
		//	solver->simplify(&jaccardAssumps);
		unsigned hashPrev = LowerFib;
		addKey2Map(jaccardHashCount, numHashList, numCountList, count);
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		map<unsigned, Lit> hashVars; //map assumption var to XOR hash

		//	int checkSAT = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps);
		lbool ret1 = solver->solve(&jaccardAssumps_lastZero);
		lbool ret2 = solver->solve(&jaccardAssumps);
		if (ret1 != l_True || ret2 != l_True){
			if(debug>DEBUG_HASH_LEVEL){
				cout<<"Unsatisfiable using this hash constraint";
			}
			continue;
		}

		SATCount scount0, scount1, scount2, scount3, scount4, scount5;
		JaccardResult result0, result1;
		vector<SATCount>scounts = {scount0, scount1, scount2, scount3, scount4, scount5};
		int ret = OneRoundFor3(jaccardHashCount, result, mPrev, hashPrev, jaccard3Assumps, scounts, solver);
		if (ret == -1) {

#if DELETE_SOLVER 
			cout << "delete solver due to ret==-1";
			delete solver;
			cout << "end delete";
			solver = new SATSolver((void*) &conf, &must_interrupt);
			this->solver = solver;
			solver_init();
			cout << "end delete";

#endif
			continue;
		}
		for (int j = 0; j < 2; ++j) {
			numHashList[jaccardHashCount].push_back(scounts[j].hashCount);
			numCountList[jaccardHashCount].push_back(scounts[j].cellSolCount);
		}
		numHashList[jaccardHashCount + 1].push_back(scounts[2].hashCount);
		numCountList[jaccardHashCount + 1].push_back(scounts[2].cellSolCount);
		result->searched[jaccardHashCount - 1] = true;
		break;
	}

#if DELETE_SOLVER 
	cout << "delete solver";
	delete solver;
	cout << "end delete";
	solver = new SATSolver((void*) &conf, &must_interrupt);
	this->solver = solver;
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	solver_init();
	cout << "end delete";
#endif
	//	cout<<"load to back, nVar="<<solver->nVars();
}

void separate(vector<Lit> all, vector<Lit> &one, vector<Lit>&another, bool single)
{
	Lit it;
	if (all.size() <= 0 || all.size() % 2 != 0) {
		one = all;
		another = all;
		return;
	}
	int i;
	for (i = 0; i < all.size() / 2; ++i) {
		one.push_back(all[i * 2]);
		if (!single)
			another.push_back(all[i * 2]);
		else
			another.push_back(all[i * 2 + 1]);
	}

	assert(another.size() == one.size());
}

void JaccardMC::JaccardHatOneRound(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, SATSolver* solver = NULL)
{
	if (solver == NULL)
		solver = solver;
	map<unsigned, vector<unsigned>> &numHashList = result->numHashList;
	map<unsigned, vector<double>>&numCountList = result->numCountList;
	map<unsigned, SATCount>& count = result->count;
	unsigned &hashCount = result->hashCount[jaccardHashCount];
	map<unsigned, Lit> jaccardHashVars;
	unsigned mPrev = 0;
	vector<vector < Lit>> inJaccardAssumps;
	vector<Lit >jaccardAssumps, leftAssumps, rightAssumps;
	int ret;
	while (true) {
		inJaccardAssumps.clear();
		jaccardAssumps.clear();
		jaccardHashVars.clear();
		leftAssumps.clear();
		rightAssumps.clear();
		SetJaccard2Hash(jaccardHashCount, jaccardHashVars, jaccardAssumps, solver);
		bool useConcreteSample = (jaccardHashCount == jaccard_vars.size()&&(!notSampled));
		// s in S and s' in S'=S
		separate(jaccardAssumps, leftAssumps, rightAssumps, useConcreteSample);
		lbool ret1 = solver->solve(&leftAssumps);
		unsigned x = (rightAssumps.back().toInt() - 1) / 2;
		if(!useConcreteSample){
			// Force S' and S =empty
			rightAssumps.pop_back();
			rightAssumps.push_back(Lit(x, false));
		}
		lbool ret2 = solver->solve(&rightAssumps);
		if (ret1 != l_True || ret2 != l_True)
		{
			if(debug>DEBUG_HASH_LEVEL){
				cout<<"Unsatisfiable using this hash constraint";
			}
			continue;
		}
		if (!useConcreteSample) {
			leftAssumps.pop_back();
			rightAssumps.pop_back();
		}
		inJaccardAssumps.push_back(leftAssumps);
		inJaccardAssumps.push_back(rightAssumps);
		inJaccardAssumps.push_back(jaccardAssumps);
		if (jaccardAssumps.size() == 0)
		  onlyLast = true;
		//	solver->simplify(&jaccardAssumps);
		unsigned hashPrev = LowerFib;
		addKey2Map(jaccardHashCount, numHashList, numCountList, count);
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		vector<std::pair<unsigned, double>>result3s;
		result3s.clear();
		int ret = OneRoundForHatJ(jaccardHashCount, result, mPrev, hashPrev, inJaccardAssumps, result3s);
		if (ret == -1) {
			continue;
		}
		if (result3s.size() < 3)
		  continue;
		assert(result3s.size() == 3);
		numHashList[jaccardHashCount].push_back(result3s[2].first);
		numCountList[jaccardHashCount].push_back(result3s[2].second);
		/*		merge(numHashList[jaccardHashCount],scount0.numHashList);
				merge(numCountList[jaccardHashCount],scount0.numCountList);*/
		std::ofstream f;
		std::ostringstream filename("");
		filename<<outPrefix<<"count_j"<<jaccardHashCount;
		f.open(filename.str(), std::ofstream::out | std::ofstream::app);
		for (int i = 0; i < result3s.size(); ++i) {
			f << result3s[i].second << "*2^" << result3s[i].first << "\t";
		}
		f << "\n";
		f.close();
		break;
	}
#if DELETE_SOLVER 
	cout << "delete solver";
	delete solver;
	cout << "end delete";
	solver = new SATSolver((void*) &conf, &must_interrupt);
	this->solver = solver;
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	solver_init();
	cout << "end delete";
#endif
//	cout<<"load to back, nVar="<<solver->nVars();
}

void JaccardMC::JaccardOneRound(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, SATSolver* solver = NULL)
{
	if (solver == NULL)
	  solver = solver;
	map<unsigned, vector<unsigned>> &numHashList = result->numHashList;
	map<unsigned, vector<double>>&numCountList = result->numCountList;
	map<unsigned, SATCount>& count = result->count;
	unsigned &hashCount = result->hashCount[jaccardHashCount];
	map<unsigned, Lit> jaccardHashVars;
	unsigned mPrev = 0;
	vector<Lit >jaccardAssumps, jaccardAssumps_lastZero;
	int ret;


	while (true) {
		jaccardAssumps.clear();
		jaccardAssumps_lastZero.clear();
		jaccardHashVars.clear();
		jaccardXorClause.clear();

		solver->simplify(&jaccardAssumps);
		if (jaccardHashCount > 0) {
			SetJaccardHash(jaccardHashCount, jaccardHashVars, jaccardAssumps, jaccardAssumps_lastZero, solver);
		}
		//	solver->simplify(&jaccardAssumps);
		unsigned hashPrev = 0;
		addKey2Map(jaccardHashCount, numHashList, numCountList, count);
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		map<unsigned, Lit> hashVars; //map assumption var to XOR hash

		//	int currentNumSolutions_lastZero = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps_lastZero);
		SATCount scount0, scount1, scount2;
		JaccardResult result0, result1;
		ret = OneRoundCount(jaccardHashCount, result, mPrev, hashPrev, jaccardAssumps, scount0, solver);
		if (ret < 0) {
			continue;
		}
		if (scount0.cellSolCount <= 0) {
			continue;
		}

		result->searched[jaccardHashCount] = true;
		ret = OneRoundCount(jaccardHashCount, result, mPrev, hashPrev, jaccardAssumps_lastZero, scount1, solver);
		if (scount1.cellSolCount <= 0) {
			continue;
		}
		if (ret < 0) {
			continue;
		}
		numHashList[jaccardHashCount].push_back(scount0.hashCount);
		numCountList[jaccardHashCount].push_back(scount0.cellSolCount);

		//if(scount1.cellSolCount>0){
		numHashList[jaccardHashCount].push_back(scount1.hashCount);
		numCountList[jaccardHashCount].push_back(scount1.cellSolCount);
		//}
		if (computePrev) {
			addKey2Map(jaccardHashCount - 1, numHashList, numCountList, count);
			jaccardAssumps_lastZero.pop_back();
			int trys = 0;
			while (true) {
				trys++;
				OneRoundCount(jaccardHashCount - 1, result, mPrev, hashPrev, jaccardAssumps_lastZero, scount2, solver);
				if (scount2.cellSolCount <= 0) {
					if (trys > 1) {
						break;
					}

					continue;
				}
				//	if(scount2.cellSolCount>0){
				numCountList[jaccardHashCount - 1].push_back(scount2.cellSolCount);
				numHashList[jaccardHashCount - 1].push_back(scount2.hashCount);
				break;
				//	}
			}
		}
		if (scount2.cellSolCount <= 0) {
			continue;
		}
		std::ofstream f;
		std::ostringstream filename("");
		filename<<outPrefix<<"count_j"<<jaccardHashCount<<"_t0";
		f.open(filename.str(), std::ofstream::out | std::ofstream::app);
		for (int i = 0; i < scount0.size() && i < scount1.size() && i < scount2.size(); ++i) {
			f << scount0.str(i) << "\t" << scount1.str(i) << "\t" << scount2.str(i) << "\n";
		}
		f << scount0.str() << "\t" << scount1.str() << "\t" << scount2.str() << "\n";
		f.close();


		result->searched[jaccardHashCount - 1] = true;

		break;
	}
#if DELETE_SOLVER 
	cout << "delete solver";
	delete solver;
	cout << "end delete";
	solver = new SATSolver((void*) &conf, &must_interrupt);
	this->solver = solver;
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	solver_init();
	cout << "end delete";
#endif
	//	cout<<"load to back, nVar="<<solver->nVars();
}

void JaccardMC::computeCountFromList(unsigned jaccardHashCount, map<unsigned, vector<unsigned>> &numHashList, map<unsigned, vector<double>>&numCountList, map<unsigned, SATCount>& count)
{
	if (numHashList[jaccardHashCount].size() == 0) {
		count[jaccardHashCount].cellSolCount = 0;
		count[jaccardHashCount].hashCount = 0;
	} else {

		vector<double> numCountL = numCountList[jaccardHashCount];
		vector<unsigned> numHashL = numHashList[jaccardHashCount];
		auto minHash = findMin(numHashL);
		auto cnt_it = numCountL.begin();
		for (auto hash_it = numHashL.begin()
			; hash_it != numHashL.end() && cnt_it != numCountL.end()
			; hash_it++, cnt_it++
			) {
			if (*hash_it - minHash)
				*cnt_it *= pow(2, (*hash_it) - minHash);
			else
				*cnt_it = 1;
		}
		int medSolCount = findMedian(numCountL);
		count[jaccardHashCount].hashCount = minHash;
		count[jaccardHashCount].cellSolCount = medSolCount;
		/*double all;
		int numC=0;
		for(auto hash_it = numCountList[jaccardHashCount].begin();hash_it!= numCountList[jaccardHashCount].end();++hash_it){
			++numC;
			all+= *hash_it;
		}

		count[jaccardHashCount].cellSolCount=all/numC;*/

	}
}

void JaccardMC::setDiffOb()
{
	vector<Lit> vars;
	vector<Lit> assumps;
	for (int i = 0; i < ob_vars.size(); i++) {
		solver->new_var();
		unsigned act_var = solver->nVars() - 1;
		assumps.push_back(Lit(act_var, true));
		vars.clear();
		vars.push_back(Lit(act_var, false));
		vars.push_back(Lit(ob_vars[i], true));
		solver->add_clause(vars);
		vars.clear();
		vars.push_back(Lit(act_var, false));
		vars.push_back(Lit(ob_vars[i], false));
		solver->add_clause(vars);
	}
	solver->add_clause(assumps);
}

bool JaccardMC::JaccardHatApproxMC(map<unsigned, SATCount>& count)
{
	count.clear();
	int currentNumSolutions = 0;
	map<unsigned, vector<unsigned>> numHashList;
	map<unsigned, vector<double>> numCountList;
	JaccardResult result;
	vector<Lit> assumps;
	vector<Lit >jaccardAssumps, jaccardAssumps_lastZero;
	unsigned hashCount = startIteration;
	unsigned hashPrev = 0;
	unsigned mPrev = 0;
	unsigned jaccardHashCount, jaccardPrev = 0;
	if (singleIndex < 0)
		singleIndex = jaccard_vars.size();
	assert(singleIndex <= jaccard_vars.size());
	jaccardHashCount = singleIndex;
	double myTime = cpuTimeTotal();
	lbool checkSAT = solver->solve();
	if (checkSAT != l_True) {
		cerr << "unsat, cannot counting";
		std::ofstream f;
		std::ostringstream filename("");
			filename<<outPrefix<<"count_j"<<jaccardHashCount<<"_t0";
		f.open(filename.str(), std::ofstream::out | std::ofstream::app);
		for (int i = 0; i < 3; ++i) {
			f << 0 << "*2^" << 0 << "\t";
		}
		f << "\n";
		f.close();
		return 0;
	}
	if (debug)
		cout << "sat, continue counting";
	int numCore = 1;
	JaccardResult * results = new JaccardResult[numCore];
	for (int i = 0; i < numCore; ++i) {
		for (int j = 0; j < singleIndex; ++j) {
			results->hashCount[j] = 0;
			results->searched[j] = false;
		}
	}

	if (trimOnly) {
		trimVar(independent_vars);
		std::ofstream ff;
		std::ostringstream filename("");
		filename << "trimed.txt";
		ff.open(filename.str(), std::ofstream::out | std::ofstream::app);
		ff << "c ind ";
		for (auto var : independent_vars) {
			ff << var + 1 << " ";
		}
		ff.close();
		exit(0);
	}
	//	trimVar(&jaccard_vars);
	double std_error = tStdError;
	for (unsigned j = 0; (j < tJaccardMC) || (std_error >= tStdError); j++) {
		/*	if(j==0)	{
			JaccardOneRound(0,&results[id],false,solvers[id]);
			results[id].searched[0]=true;
			computeCountFromList(0,results[id].numHashList,results[id].numCountList,results[id].count);
			}*/
		int retryJaccardSingle = 0;
		while (true) {
			if (singleIndex == 0) {
				onlyOne = true;
			}
			if (debug)
				std::cout << "j=" << j << "\n";
			JaccardHatOneRound(singleIndex, &results[0], true, solver);
			//	computeCountFromList(singleIndex,results[0].numHashList,results[0].numCountList,results[0].count);
			results[0].searched[singleIndex] = true;
			break;
			retryJaccardSingle++;
		}

		if (j % 10 == 0) {
			std_error = getSTD(results[0].numCountList[singleIndex], results[0].numHashList[singleIndex]);
		}
	}
	return true;
}

bool JaccardMC::JaccardApproxMC(map<unsigned, SATCount>& count)
{
	count.clear();
	int currentNumSolutions = 0;
	map<unsigned, vector<unsigned>> numHashList;
	map<unsigned, vector<double>> numCountList;
	JaccardResult result;
	vector<Lit> assumps;
	vector<Lit >jaccardAssumps, jaccardAssumps_lastZero;
	unsigned hashCount = startIteration;
	unsigned hashPrev = 0;
	unsigned mPrev = 0;
	unsigned jaccardHashCount, jaccardPrev = 0;
	if (singleIndex < 0)
		singleIndex = jaccard_vars.size();
	assert(singleIndex <= jaccard_vars.size());
	jaccardHashCount = singleIndex;
	double myTime = cpuTimeTotal();

	int checkSAT = BoundedSATCount(pivotApproxMC + 1, assumps, solver);
	if (checkSAT <= 0) {
		return 0;
	}
	//	cout<<"save_state to "<<conf.saved_state_file.c_str()<<endl;
	//	solver->save_state(conf.saved_state_file.c_str(), l_True);
	//	return true;



	int numCore = 1;
	JaccardResult * results = new JaccardResult[numCore];
	for (int i = 0; i < numCore; ++i) {
		for (int j = 0; j < singleIndex; ++j) {
			results->hashCount[j] = 0;
			results->searched[j] = false;
		}
	}
	//warn up
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	//after warm up

	if (trimOnly) {
		trimVar(independent_vars);
		std::ofstream ff;
		std::ostringstream filename("");
		filename << "trimed.txt";
		ff.open(filename.str(), std::ofstream::out | std::ofstream::app);
		ff << "c ind ";
		for (auto var : independent_vars) {
			ff << var + 1 << " ";
		}
		ff.close();
		exit(0);
	}
	//	trimVar(&jaccard_vars);
	for (unsigned j = 0; j < tJaccardMC; j++) {
		/*	if(j==0)	{
			JaccardOneRound(0,&results[id],false,solvers[id]);
			results[id].searched[0]=true;
			computeCountFromList(0,results[id].numHashList,results[id].numCountList,results[id].count);
			}*/
		cout << "Jaccard count=" << j;
		int retryJaccardSingle = 0;
		while (true) {
			std::ofstream f;
			std::ostringstream filename("");
			//filename<<"info_j"<<singleIndex<<"_t"<<omp_get_thread_num();
			if (singleIndex == 0) {
				onlyOne = true;
			}
			JaccardOneRoundFor3(singleIndex, &results[0], true, solver);
			computeCountFromList(singleIndex, results[0].numHashList, results[0].numCountList, results[0].count);
			computeCountFromList(singleIndex - 1, results[0].numHashList, results[0].numCountList, results[0].count);
			results[0].searched[singleIndex] = true;
			/*
			cout << "====0 retry singleIndex" << endl;
			if (retryJaccardSingle > 5) {
				retryJaccardSingle = 0;
				//	singleIndex--;
				j--;
				break;
			}
			retryJaccardSingle++;*/
		}
	}

	return true;
}

bool JaccardMC::ApproxMC(SATCount& count)
{
	count.clear();
	int currentNumSolutions = 0;
	vector<unsigned> numHashList;
	vector<double> numCountList;
	vector<Lit> assumps;
	for (unsigned j = 0; j < tApproxMC; j++) {
		unsigned hashCount;
		unsigned repeatTry = 0;
		for (hashCount = 0; hashCount < solver->nVars(); hashCount++) {
			cout << "-> Hash Count " << hashCount << endl;
			double myTime = cpuTimeTotal();
			currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, solver);

			//cout << currentNumSolutions << ", " << pivotApproxMC << endl;
			LOGF << "ApproxMC:" << searchMode << ":"
				<< j << ":" << hashCount << ":"
				<< std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
				<< (int) (currentNumSolutions == (pivotApproxMC + 1)) << ":"
				<< currentNumSolutions << endl;
			//Timeout!
			if (currentNumSolutions < 0) {
				//Remove all hashes
				assumps.clear();

				if (repeatTry < 2) { /* Retry up to twice more */
					assert(hashCount > 0);
					AddHash(hashCount, assumps, solver); //add new set of hashes
					solver->simplify(&assumps);
					hashCount--;
					repeatTry += 1;
					cout << "Timeout, try again -- " << repeatTry << endl;
				} else {
					//this set of hashes does not work, go up
					AddHash(hashCount + 1, assumps, solver);
					solver->simplify(&assumps);
					cout << "Timeout, moving up" << endl;
				}
				continue;
			}

			if (currentNumSolutions < pivotApproxMC + 1) {
				//less than pivotApproxMC solutions
				break;
			}

			//Found all solutions needed
			AddHash(1, assumps, solver);
		}
		assumps.clear();
		numHashList.push_back(hashCount);
		numCountList.push_back(currentNumSolutions);
	}
	if (numHashList.size() == 0) {
		//UNSAT
		return true;
	}

	auto minHash = findMin(numHashList);
	auto hash_it = numHashList.begin();
	auto cnt_it = numCountList.begin();
	for (; hash_it != numHashList.end() && cnt_it != numCountList.end()
		; hash_it++, cnt_it++
		) {
		*cnt_it *= pow(2, (*hash_it) - minHash);
	}
	int medSolCount = findMedian(numCountList);

	count.cellSolCount = medSolCount;
	count.hashCount = minHash;
	return true;
}

void JaccardMC::solver_init()
{
	if (dratf) {
		solver->set_drat(dratf, clause_ID_needed);
	}
	check_num_threads_sanity(num_threads);
	solver->set_num_threads(num_threads);
	if (unset_vars) {
		//solver->set_greedy_undef();
	}
	vector<unsigned> original_independent_vars = independent_vars;
	parseInAllFiles(solver);
	if (original_independent_vars.size() > 0)
		independent_vars = original_independent_vars;
	int pos = 0;
	if (is_diff) {
		ob_vars = jaccard_vars;
	}

	if (is_diff && ob_vars.size() > 0) {
		setDiffOb();
	}


}
void JaccardMC::readDFile(){
	std::ifstream dfile;
	dfile.open(dFilename);
	string line;
	int var;
	float weight=4;
	char weightstr[100];
	//distribution[89]=4;
	while(std::getline(dfile,line)){
		memset(weightstr,0,100);
		std::sscanf(line.c_str(),"%d,%s", &var,weightstr);
		weight=atof(weightstr);
		std::cout<<line.c_str()<<"->"<<var<<":"<<weight<<"\n";
		distribution[var]=weight;
		line.clear();
	}
	
	dfile.close();
}
int JaccardMC::solve()
{
	if (!gauss_manual) {
		uint32_t xor_cut = 4;
		conf.reconfigure_at = 0;
		conf.reconfigure_val = 15;
		conf.xor_var_per_cut = xor_cut-2;
		conf.varElimRatioPerIter = 1;
		conf.maple = 0;
        conf.do_simplify_problem = true;
		conf.global_multiplier_multiplier_max = 3;
		conf.global_timeout_multiplier_multiplier = 1.5;
		conf.gaussconf.max_matrix_rows = 3000;
		conf.gaussconf.decision_until = 3000;
		conf.gaussconf.max_num_matrixes = 4;
		conf.gaussconf.min_matrix_rows = 5;
		conf.gaussconf.autodisable = false;
	}

	//set seed
	assert(vm.count("random"));
	unsigned int seed = vm["random"].as<unsigned int>();
	randomEngine.seed(seed);
	readDFile();
	openLogFile();
	startTime = cpuTimeTotal();
	solver = new SATSolver((void*) &conf, &must_interrupt);
	//solver->log_to_file("mydump.cnf");
	solverToInterrupt = solver;
	if (dratf) {
		cout
			<< "ERROR: Gauss does NOT work with DRAT and Gauss is needed for CUSP. Exiting."
			<< endl;
		exit(-1);
	}
	solver_init();
	//printVersionInfo();


	if (startIteration > independent_vars.size()) {
		cout << "ERROR: Manually-specified startIteration"
			"is larger than the size of the independent set.\n" << endl;
		return -1;
	}



#if PARALLEL 
	int cores = omp_get_num_procs();
	cout << "max thread=" << cores;
	solvers.clear();
	for (int i = 0; i < cores; i++) {
		SATSolver* s = new SATSolver((void*) &conf, &must_interrupt);
		parseInAllFiles(s);
		solvers.push_back(s);
	}
	//	solver=solvers[omp_get_thread_num()];

	//	solverToInterrupt = solver;
#endif
	SATCount solCount;
	cerr << "Using start iteration " << startIteration << endl;

	bool finished = false;
	if (searchMode == 0) {
		finished = ApproxMC(solCount);
	} else if (searchMode == 1) {
		map<unsigned, SATCount> solCounts;
		finished = JaccardApproxMC(solCounts);
		if (!finished) {
			cout << " (TIMED OUT)" << endl;
			return 0;
		}
		for (auto it = solCounts.begin(); it != solCounts.end(); ++it) {
			cout << it->first << " of Number of solutions is: " << it->second.cellSolCount
				<< " x 2^" << it->second.hashCount << endl;
		}

		if (conf.verbosity) {
			solver->print_stats();
		}
	} else if (searchMode == 2) {
		finished = ScalApproxMC(solCount);
	} else if (searchMode == 3)//jaccard F(c,s,o) xor F'(c,s',o)
	{
		map<unsigned, SATCount> solCounts;
		finished = JaccardHatApproxMC(solCounts);
		if (!finished) {

			cout << " (TIMED OUT)" << endl;
			return 0;
		}
		for (auto it = solCounts.begin(); it != solCounts.end(); ++it) {
			cout << it->first << " of Number of solutions is: " << it->second.cellSolCount
				<< " x 2^" << it->second.hashCount << endl;
		}

		if (conf.verbosity) {
			solver->print_stats();
		}
	} else {
		vector<Lit>assume;
		assume.clear();
		unsigned max = 10000;
		BoundedSATCount_print(max, assume, solver);
	}
	cout << "ApproxMC finished in " << (cpuTimeTotal() - startTime) << " s" << endl;
	if (!finished) {
		cout << " (TIMED OUT)" << endl;
		return 0;
	}

	if (solCount.hashCount == 0 && solCount.cellSolCount == 0) {
		cout << "The input formula is unsatisfiable." << endl;
		return correctReturnValue(l_False);
	}

	if (conf.verbosity) {
		solver->print_stats();
	}

	cout << "Number of solutions is: " << solCount.cellSolCount
		<< " x 2^" << solCount.hashCount << endl;

	return correctReturnValue(l_True);
}

int main(int argc, char** argv)
{

#ifndef USE_GAUSS
	std::cerr << "CUSP only makes any sese to run if you have configured with:" << endl
		<< "*** cmake -DUSE_GAUSS=ON (.. or .)  ***" << endl
		<< "Refusing to run. Please reconfigure and then re-compile." << endl;
	exit(-1);
#else
	JaccardMC main(argc, argv);
	main.conf.verbStats = 1;
	main.parseCommandLine();
	return main.solve();
#endif
}

void JaccardMC::call_after_parse()
{
	if (independent_vars.empty()) {
		cout
			<< "c WARNING! No independent vars were set using 'c ind var1 [var2 var3 ..] 0'"
			"notation in the CNF." << endl
			<< " c ScalMC may work substantially worse!" << endl;
		for (size_t i = 0; i < solver->nVars(); i++) {
			independent_vars.push_back(i);
		}

		solver->set_independent_vars(&independent_vars);
	}

}
/*set concrete samples for s, s'*/
 void JaccardMC::SetSampledJaccardHatHash(unsigned clausNum, vector<vector<Lit>>&assumps, SATSolver* solver)
{
	//assumps[0]: constrain secret s in S
	//assumps[1]: constrain secret s' in S'
	//assumps[2]: constrain secret s in S and s' in S'
	string sampleOne;
	size_t var_size = jaccard_vars.size();
	int sampleSize = 1 << (jaccard_vars.size() - clausNum);
	sampleSize;
	std::set<string>jaccard_samples;
	while (jaccard_samples.size() < sampleSize * 2) {
		sampleOne = GenerateRandomBits_prob(var_size, 0.5);
		jaccard_samples.insert(sampleOne);
	}
	solver->new_var();
	unsigned two_var = solver->nVars() - 1;
	vector<Lit> out_var;
	vector<uint32_t> variables;
	while(assumps.size()<3){
		vector<Lit> tmp;
		assumps.push_back(tmp);
	}
	for (int i = 0; i < 3; ++i)
		assumps[i].push_back(Lit(two_var, false));
	out_var.push_back(Lit(two_var, true));
	std::set<string>::iterator sampleit = jaccard_samples.begin();
	for (int t = 0; t < 2; ++t) {
		switch (t){
			case 0:
				variables=jaccard_vars;
				break;
			case 1:
				variables=jaccard_vars2;
				break;
			default:
				variables=jaccard_vars;
				break;
		}
		
		// t=0 -> assign values to S
		// t=1 -> assign values to S'
		sampleOne = *sampleit;
		solver->new_var(); 
		unsigned act_var = solver->nVars() - 1;
		assumps[t].push_back(Lit(act_var, false));
		out_var.push_back(Lit(act_var, false));
		vector<Lit> orSols;
		orSols.push_back(Lit(act_var, true));
		orSols.push_back(Lit(two_var, true));
		for (int i = 0; i < sampleSize; ++i) {
			sampleOne = *sampleit;
			vector<Lit> vars;
			solver->new_var();
			unsigned sol_var = solver->nVars() - 1;
			vars.push_back(Lit(sol_var, true));
			vars.push_back(Lit(act_var, true));
			vars.push_back(Lit(two_var, true));
			orSols.push_back(Lit(sol_var, false));
			// Assign S to a concrete value sampelOne
			// by adding var_size constraints where each constraint one bit
			//
			for (int j = 0; j < var_size; ++j) {
				vars.push_back(Lit(variables[j], sampleOne[j] == '1'));
				printVars(vars);
				solver->add_clause(vars);
				vars.pop_back();
			}
			sampleit++;
		}
		printVars(orSols);
		solver->add_clause(orSols);
	}
	solver->add_clause(out_var);

}

bool JaccardMC::SSetTwoHashSample(unsigned num_xor_cls, vector<Lit>& assumps, SATSolver* solver)
{	// assumps[odd]-> constraint s using S
	// assumps[even] ->constraint s' using S'=S, to use this , please modify one bit from assumps[even] to make S' and S = empty
	int var_size = jaccard_vars.size();
	jaccardXorRate = (jaccardXorRate > 0.5) ? 0.5 : jaccardXorRate;

	string randomBits = GenerateRandomBits_prob((var_size) * num_xor_cls, jaccardXorRate);
	string randomBits_rhs = GenerateRandomBits(num_xor_cls);


	bool rhs = true;
	if (num_xor_cls == jaccard_vars.size()&&(!notSampled)) {//select one specific value
		string randomBits_rhs2 = GenerateRandomBits(num_xor_cls);
		while (randomBits_rhs2 == randomBits_rhs)
			randomBits_rhs2 = GenerateRandomBits(num_xor_cls);
		for (int i = 0; i < jaccard_vars.size(); ++i) {
			assumps.push_back(Lit(jaccard_vars[i], randomBits_rhs[i] == '1'));
			assumps.push_back(Lit(jaccard_vars2[i], randomBits_rhs2[i] == '1'));
		}
		return true;
	}
	/*elseif(!notSampled){
		vector<vector<Lit>>assumps3;
		SetSampledJaccardHatHash(num_xor_cls,assumps3,solver);
		for (int i=0;i<2;++i){
			assumps+=assumps3[i];
		}
	}*/
	vector<unsigned> vars, vars2;
	for (unsigned i = 0; i < num_xor_cls; i++) {
		//new activation variable
		solver->new_var();
		unsigned act_var = solver->nVars() - 1;

		solver->new_var();
		unsigned act_var2 = solver->nVars() - 1;
		assumps.push_back(Lit(act_var, true));
		assumps.push_back(Lit(act_var2, true));
		vars.clear();
		vars.push_back(act_var);
		vars2.clear();
		vars2.push_back(act_var2);
		rhs = (randomBits_rhs[i] == '1');
		//		cout<<"x ";

		for (unsigned k = 0; k < var_size; k++) {
			if (randomBits[var_size * i + k] == '1') {
				vars.push_back(jaccard_vars[k]);
				if (jaccard_vars2.size())
					vars2.push_back(jaccard_vars2[k]);
			}
		}
		if (conf.verbosity || printXor) {
			string text = "jaccard" + randomBits;
			print_xor(vars, rhs, text.c_str());
		}
		if (vars.size())
			solver->add_xor_clause(vars, rhs);
		if (debug > DEBUG_HASH_LEVEL) {
			cout << "vars1:" << rhs << "=";
			for (auto one : vars)
				cout << one << " ";
			cout << "\n";
		}
		if (i == num_xor_cls - 1 && (!same_set))
			rhs = !rhs;
		if (vars2.size())
			solver->add_xor_clause(vars2, rhs);
		if (debug > DEBUG_HASH_LEVEL) {
			cout << "x " << rhs << "=";
			for (auto one : vars2)
				cout << one << " ";
			cout << "0\n";
		}

	}
	return true;

}

	
bool JaccardMC::SSetHashSample(unsigned num_xor_cls, vector<Lit>& assumps, vector<XorClause>& jaccardXorClause, SATSolver* solver)
{
	int var_size = jaccard_vars.size();
	jaccardXorRate = (jaccardXorRate > 0.5) ? 0.5 : jaccardXorRate;

	string randomBits = GenerateRandomBits_prob((var_size) * num_xor_cls, jaccardXorRate);
	string randomBits_rhs = GenerateRandomBits(num_xor_cls);
	bool rhs = true;
	vector<unsigned> vars;
	for (unsigned i = 0; i < num_xor_cls; i++) {
		//new activation variable
		solver->new_var();
		unsigned act_var = solver->nVars() - 1;
		assumps.push_back(Lit(act_var, true));
		vars.clear();
		vars.push_back(act_var);
		rhs = (randomBits_rhs[i] == '1');
		cout<<"\nhash S:";
		for (unsigned k = 0; k < var_size; k++) {
			if (randomBits[var_size * i + k] == '1') {
				vars.push_back(jaccard_vars[k]);
				if (debug > DEBUG_VAR_LEVEL)
					cout << jaccard_vars[k] << " ";
			}
		}
		if (conf.verbosity || printXor) {
			string text = "jaccard" + randomBits;
			print_xor(vars, rhs, text.c_str());
		}
		if (vars.size())
			solver->add_xor_clause(vars, rhs);
		XorClause xc(vars, rhs);
		jaccardXorClause.push_back(xc);
	}
	return true;

}
/*set concrete samples to S, S' and SUS'*/
void JaccardMC::SetSampledJaccardHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<vector<Lit>>&assumps, SATSolver* solver)
{
	//assumps[0]: constrain secret in S
	//assumps[1]: constrain secret in S'
	//assumps[2]: constrain secret in S or S'
	string sampleOne;
	size_t var_size = jaccard_vars.size();
	int sampleSize = 1 << (jaccard_vars.size() - clausNum);
	sampleSize;
	std::set<string>jaccard_samples;
	while (jaccard_samples.size() < sampleSize * 2) {
		sampleOne = GenerateRandomBits_prob(var_size, 0.5);
		jaccard_samples.insert(sampleOne);
	}
	solver->new_var();
	unsigned two_var = solver->nVars() - 1;
	vector<Lit> out_var;
	for (int i = 0; i < 3; ++i)
		assumps[i].push_back(Lit(two_var, false));
	out_var.push_back(Lit(two_var, true));
	std::set<string>::iterator sampleit = jaccard_samples.begin();
	for (int t = 0; t < 2; ++t) {
		// t=0 -> assign values to S
		// t=1 -> assign values to S'
		sampleOne = *sampleit;
		solver->new_var(); 
		unsigned act_var = solver->nVars() - 1;
		assumps[t].push_back(Lit(act_var, false));
		out_var.push_back(Lit(act_var, false));
		vector<Lit> orSols;
		orSols.push_back(Lit(act_var, true));
		orSols.push_back(Lit(two_var, true));
		for (int i = 0; i < sampleSize; ++i) {
			sampleOne = *sampleit;
			vector<Lit> vars;
			solver->new_var();
			unsigned sol_var = solver->nVars() - 1;
			vars.push_back(Lit(sol_var, true));
			vars.push_back(Lit(act_var, true));
			vars.push_back(Lit(two_var, true));
			orSols.push_back(Lit(sol_var, false));
			// Assign S to a concrete value sampelOne
			// by adding var_size constraints where each constraint one bit
			//
			for (int j = 0; j < var_size; ++j) {
				vars.push_back(Lit(jaccard_vars[j], sampleOne[j] == '1'));
				printVars(vars);
				solver->add_clause(vars);
				vars.pop_back();
			}
			sampleit++;
		}
		printVars(orSols);
		solver->add_clause(orSols);
	}
	solver->add_clause(out_var);

}

void JaccardMC::SetJaccardHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, vector<Lit>& assumps2, SATSolver* solver)
{
	double originaljaccardXorRate = jaccardXorRate;
	if (jaccard_vars.size() / clausNum < 2) {
		jaccardXorRate = (float) (0.2 * jaccard_vars.size() / clausNum);
	}
	jaccardXorRate = (jaccardXorRate < 0.5) ? jaccardXorRate : 0.5;
	//if (conf.verbosity)
	if (debug)
		std::cout << "jaccardxorrate=" << jaccardXorRate << "\n";
	if (clausNum < assumps.size()) {//s1 for s
		unsigned numberToRemove = assumps.size() - clausNum;
		for (unsigned i = 0; i < numberToRemove; i++) {
			assumps.pop_back();
		}
	} else {
		if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
			for (unsigned i = assumps.size(); i < hashVars.size() && i < clausNum; i++) {
				assumps.push_back(hashVars[i]);
			}
		}
		if (clausNum > hashVars.size()) {

			SSetHashSample(clausNum - hashVars.size(), assumps, jaccardXorClause, solver);
			for (unsigned i = hashVars.size(); i < clausNum; i++) {
				hashVars[i] = assumps[i];
			}
		}
	}
	assumps2 = assumps;
	unsigned x = (assumps2[clausNum - 1].toInt() - 1) / 2;
	assumps2[clausNum - 1] = Lit(x, false);
	jaccardXorRate = originaljaccardXorRate;
}

void JaccardMC::SetJaccard2Hash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, SATSolver* solver)
{
	double originaljaccardXorRate = jaccardXorRate;
	hashVars.clear();
	assumps.clear();
	if (clausNum == 0)
		return;
	if (jaccard_vars.size() / clausNum < 2) {
		jaccardXorRate = (float) (0.2 * jaccard_vars.size() / clausNum);
	}
	jaccardXorRate = (jaccardXorRate < 0.5) ? jaccardXorRate : 0.5;
	//if (conf.verbosity)
	assumps.clear();
	if (debug > DEBUG_VAR_LEVEL)
		std::cout << "set jaccard2hash: jaccardxorrate=" << jaccardXorRate << "\n";
	SSetTwoHashSample(clausNum - hashVars.size(), assumps, solver);
	jaccardXorRate = originaljaccardXorRate;
}

//For ScalApproxMC only

void JaccardMC::SetHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, SATSolver* solver)
{
	double ratio = 0.5;
	if (test_func == 1 && (clausNum < attack_vars.size() - 1)) {
		independent_vars0 = attack_vars;
	} else {
		independent_vars0 = independent_vars;
	}
	int var_size = independent_vars0.size();
	if (XorMax>0 and unsigned(clausNum * var_size)>unsigned(XorMax)) {//don't allow too many xor
		ratio = (1.0 * XorMax) / (clausNum * var_size);
		//ratio=(ratio<XorRate)?XorRate:0.5;
	}
	xorRate = (ratio > xorRate) ? xorRate : ratio;


	if (clausNum < assumps.size()) {
		unsigned numberToRemove = assumps.size() - clausNum;
		for (unsigned i = 0; i < numberToRemove; i++) {
			assumps.pop_back();
		}
	} else {
		if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
			for (unsigned i = assumps.size(); i < hashVars.size() && i < clausNum; i++) {
				assumps.push_back(hashVars[i]);
			}
		}
		if (clausNum > hashVars.size()) {
			if (test_func == 1) {
				for (unsigned n = 1; n <= clausNum - hashVars.size(); n++) {
					if ((test_func == 1)&&(n + hashVars.size() < attack_vars.size() - 1)) {
						independent_vars0 = attack_vars;
					} else {
						independent_vars0 = ob_vars;
					}
					AddHash(1, assumps, solver);
				}
			} else {
				AddHash(clausNum - hashVars.size(), assumps, solver);
			}
			for (unsigned i = hashVars.size(); i < clausNum; i++) {
				hashVars[i] = assumps[i];
			}
		}
	}
}
//For ScalApproxMC only

bool JaccardMC::ScalApproxMC(SATCount& count)
{
	count.clear();
	vector<unsigned> numHashList;
	vector<double> numCountList;
	std::ofstream f;
	std::ostringstream filename("");

	filename<<outPrefix<<"count_"<<specifiedOb<<"_t0";



	unsigned hashCount = startIteration;
	unsigned hashPrev = 0;
	unsigned mPrev = 0;

	double myTime = cpuTimeTotal();
	if (hashCount == 0) {
		vector<Lit> assumps;
		int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, solver);
		LOGF << "ApproxMC:" << searchMode << ":" << "0:0:"
			<< std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
			<< (int) (currentNumSolutions == (pivotApproxMC + 1)) << ":"
			<< currentNumSolutions << endl;

		//Din't find at least pivotApproxMC+1
		if (currentNumSolutions <= (int)pivotApproxMC) {
			count.cellSolCount = currentNumSolutions;
			count.hashCount = 0;
			std::ofstream f;
			std::ostringstream filename("");

			f.open(filename.str(), std::ofstream::out | std::ofstream::app);
			f.open(filename.str(), std::ofstream::out | std::ofstream::app);
			f << currentNumSolutions << "*2^" << 0 << "\n";
			f.close();

			return true;
		}
		hashCount++;
	}
	for (unsigned j = 0; j < 1; j++) {

		vector<Lit> assumps;
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		map<unsigned, Lit> hashVars; //map assumption var to XOR hash
		unsigned repeatTry = 0;
		unsigned numExplored = 1;
		unsigned lowerFib = 0, upperFib = independent_vars.size();

		while (numExplored < independent_vars.size()) {
			cout << "Num Explored: " << numExplored
				<< " ind set size: " << independent_vars.size() << endl;
			myTime = cpuTimeTotal();
			unsigned swapVar = hashCount;

			cout << "start setting hash" << hashCount << "hashVar=" << hashVars.size() << "assumps" << assumps.size() << endl;
			SetHash(hashCount, hashVars, assumps, solver);
			cout << "Number of XOR hashes active: " << hashCount << endl;
			int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, solver);

			//   cout << currentNumSolutions << ", " << pivotApproxMC << endl;
			LOGF << "ApproxMC:" << searchMode << ":"
				<< j << ":" << hashCount << ":"
				<< std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
				<< (currentNumSolutions == (int)(pivotApproxMC + 1)) << ":"
				<< currentNumSolutions << endl;
			//Timeout!
			if (currentNumSolutions < 0) {
				//Remove all hashes
				assumps.clear();
				hashVars.clear();

				if (repeatTry < 2) { /* Retry up to twice more */
					assert(hashCount > 0);
					SetHash(hashCount, hashVars, assumps, solver);
					solver->simplify(&assumps);
					hashCount--;
					repeatTry += 1;
					cout << "Timeout, try again -- " << repeatTry << endl;
				} else {
					//this set of hashes does not work, go up
					SetHash(hashCount + 1, hashVars, assumps, solver);
					solver->simplify(&assumps);
					cout << "Timeout, moving up" << endl;
				}
				hashCount = swapVar;
				continue;
			}

			if (currentNumSolutions < (int)pivotApproxMC + 1) {
				numExplored = lowerFib + independent_vars.size() - hashCount;
				if (succRecord.find(hashCount - 1) != succRecord.end()
					&& succRecord[hashCount - 1] == 1
					) {
					numHashList.push_back(hashCount);
					numCountList.push_back(currentNumSolutions);
					mPrev = hashCount;
					//less than pivotApproxMC solutions
					break;
				}
				succRecord[hashCount] = 0;
				countRecord[hashCount] = currentNumSolutions;
				if (abs((int)hashCount - (int)mPrev) <= 2 && mPrev != 0) {
					upperFib = hashCount;
					hashCount--;
				} else {
					if (hashPrev > hashCount) {
						hashPrev = 0;
					}
					upperFib = hashCount;
					if (hashPrev > lowerFib) {
						lowerFib = hashPrev;
					}
					hashCount = (upperFib + lowerFib) / 2;
				}
			} else {
				assert(currentNumSolutions == pivotApproxMC + 1);

				numExplored = hashCount + independent_vars.size() - upperFib;
				if (succRecord.find(hashCount + 1) != succRecord.end()
					&& succRecord[hashCount + 1] == 0
					) {
					numHashList.push_back(hashCount + 1);
					numCountList.push_back(countRecord[hashCount + 1]);
					mPrev = hashCount + 1;
					break;
				}
				succRecord[hashCount] = 1;
				if (abs((int)hashCount - (int)mPrev) < 2 && mPrev != 0) {
					lowerFib = hashCount;
					hashCount++;
				} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib - 1) {
					lowerFib = hashCount;
					hashCount = (lowerFib + upperFib) / 2;
				} else {
					//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
					hashCount = lowerFib + (hashCount - lowerFib)*2;
				}
			}
			hashPrev = swapVar;
		}
		assumps.clear();
		solver->simplify(&assumps);
		hashCount = mPrev;
	}
	for (unsigned j = 0; j < tApproxMC; j++) {
		vector<Lit> assumps;
		map<unsigned, int> countRecord;
		map<unsigned, unsigned> succRecord;
		map<unsigned, Lit> hashVars; //map assumption var to XOR hash
		unsigned repeatTry = 0;
		unsigned numExplored = 1;
		unsigned lowerFib = 0, upperFib = independent_vars.size();

		while (numExplored < independent_vars.size()) {
			cout << "Num Explored: " << numExplored
				<< " ind set size: " << independent_vars.size() << endl;
			myTime = cpuTimeTotal();
			unsigned swapVar = hashCount;

			cout << "start setting hash" << hashCount << "hashVar=" << hashVars.size() << "assumps" << assumps.size() << endl;
			SetHash(hashCount, hashVars, assumps, solver);
			cout << "Number of XOR hashes active: " << hashCount << endl;
			int currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps, solver);

			cout << currentNumSolutions << ", " << pivotApproxMC << endl;
			LOGF << "ApproxMC:" << searchMode << ":"
				<< j << ":" << hashCount << ":"
				<< std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
				<< (unsigned) (currentNumSolutions == (pivotApproxMC + 1)) << ":"
				<< currentNumSolutions << endl;
			//Timeout!
			if (currentNumSolutions < 0) {
				//Remove all hashes
				assumps.clear();
				hashVars.clear();
				if (repeatTry < 2) { /* Retry up to twice more */
					assert(hashCount > 0);
					SetHash(hashCount, hashVars, assumps, solver);
					solver->simplify(&assumps);
					hashCount--;

					repeatTry += 1;
					cout << "Timeout, try again -- " << repeatTry << endl;
				} else {
					//this set of hashes does not work, go up
					SetHash(hashCount + 1, hashVars, assumps, solver);
					solver->simplify(&assumps);
					cout << "Timeout, moving up" << endl;
				}
				hashCount = swapVar;
				continue;
			}

			if (currentNumSolutions < pivotApproxMC + 1) {
				numExplored = lowerFib + independent_vars.size() - hashCount;
				if (succRecord.find(hashCount - 1) != succRecord.end()
					&& succRecord[hashCount - 1] == 1
					) {
					numHashList.push_back(hashCount);
					numCountList.push_back(currentNumSolutions);
					mPrev = hashCount;
					//less than pivotApproxMC solutions
					break;
				}
				succRecord[hashCount] = 0;
				countRecord[hashCount] = currentNumSolutions;
				if (abs((int)hashCount - (int)mPrev) <= 2 && mPrev != 0) {
					upperFib = hashCount;
					hashCount--;
				} else {
					if (hashPrev > hashCount) {
						hashPrev = 0;
					}
					upperFib = hashCount;
					if (hashPrev > lowerFib) {
						lowerFib = hashPrev;
					}
					hashCount = (upperFib + lowerFib) / 2;
				}
			} else {
				assert(currentNumSolutions == pivotApproxMC + 1);

				numExplored = hashCount + independent_vars.size() - upperFib;
				if (succRecord.find(hashCount + 1) != succRecord.end()
					&& succRecord[hashCount + 1] == 0
					) {
					numHashList.push_back(hashCount + 1);
					numCountList.push_back(countRecord[hashCount + 1]);
					mPrev = hashCount + 1;
					break;
				}
				succRecord[hashCount] = 1;
				if (abs((int)hashCount - (int)mPrev) < 2 && mPrev != 0) {
					lowerFib = hashCount;
					hashCount++;
				} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib - 1) {
					lowerFib = hashCount;
					hashCount = (lowerFib + upperFib) / 2;
				} else {
					//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
					hashCount = lowerFib + (hashCount - lowerFib)*2;
				}
			}
			hashPrev = swapVar;
		}
		assumps.clear();
		solver->simplify(&assumps);
		hashCount = mPrev;
		f.open(filename.str(), std::ofstream::out | std::ofstream::app);
		f << numCountList.back() << "*2^" << numHashList.back() << "\n";
		f.close();

	}
	if (numHashList.size() == 0) {
		//UNSAT
		return true;
	}

	auto minHash = findMin(numHashList);
	auto cnt_it = numCountList.begin();
	for (auto hash_it = numHashList.begin()
		; hash_it != numHashList.end() && cnt_it != numCountList.end()
		; hash_it++, cnt_it++
		) {
		f << *cnt_it << "*2^" << *hash_it << "\n";
		*cnt_it *= pow(2, (*hash_it) - minHash);
	}
	int medSolCount = findMedian(numCountList);
	f << medSolCount << "*2^" << minHash << "\n";
	f.close();
	count.cellSolCount = medSolCount;
	count.hashCount = minHash;
	return true;
}
