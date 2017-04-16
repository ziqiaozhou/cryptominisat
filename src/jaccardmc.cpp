/*ES

 * CUSP and ScalMC
 *
 * Copyright (c) 2009-2015, Mate Soos. All rights reserved.
 * Copyright (c) 2014, Supratik Chakraborty, Kuldeep S. Meel, Moshe Y. Vardi
 * Copyright (c) 2015, Supratik Chakraborty, Daniel J. Fremont,
 * Kuldeep S. Meel, Sanjit A. Seshia, Moshe Y. Vardi
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation
 * version 2.0 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
 */

#if defined(__GNUC__) && defined(__linux__)

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <fenv.h>
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
#include <fstream>
#include <sys/stat.h>
#include <string.h>
#include <list>
#include <vector>
#include<set>
#include<omp.h>
#include<pthread.h>
#include "jaccardmc.h"
#include "time_mem.h"
#include "dimacsparser.h"
#include "cryptominisat5/cryptominisat.h"
#include "signalcode.h"
#include "clausedumper.h"
using std::cout;
using std::cerr;
using std::endl;
using boost::lexical_cast;
using std::list;
using std::map;

#define PARALLEL 0
string binary(unsigned x, uint32_t length)
{
    uint32_t logSize = (x == 0 ? 1 : log2(x) + 1);
    string s;
    do {
        s.push_back('0' + (x & 1));
    } while (x >>= 1);
    for (uint32_t i = logSize; i < (uint32_t) length; i++) {
        s.push_back('0');
    }
    std::reverse(s.begin(), s.end());

    return s;

}



string CUSP::GenerateRandomBits(uint32_t size)
{
    string randomBits;
    std::uniform_int_distribution<unsigned> uid {0, 2147483647U};
    uint32_t i = 0;
    while (i < size) {
        i += 31;
        randomBits += binary(uid(random_dev), 31);
    }
    return randomBits;
}
string CUSP::GenerateRandomBits_prob(uint32_t size,double prob)
{
    string randomBits="";
    std::uniform_int_distribution<unsigned> uid(0, 1000);
    uint32_t i = 0;
    while (i < size) {
        i += 1;
        char x[2]="";
		x[0]='0'+((uid(random_dev)<=prob*1000)?1:0);
		randomBits+=x;
    }
	std::reverse(randomBits.begin(), randomBits.end());
    return randomBits;
}

void CUSP::add_approxmc_options()
{
    approxMCOptions.add_options()
    ("pivotAC", po::value(&pivotApproxMC)->default_value(pivotApproxMC)
        , "Number of solutions to check for")
	("mode", po::value(&searchMode)->default_value(searchMode)
	 ,"Seach mode. ApproxMX = 0, JaccardMC=1,ScalMC = 2")
	("JaccardXorMax", po::value(&jaccardXorMax)->default_value(jaccardXorMax)
	 ,"default =600, if xor is eceed this value, trim the xor by change the ratio for randombits")
	("XorMax", po::value(&XorMax)->default_value(XorMax)
	 ,"default =1000, if xor is eceed this value, trim the xor by change the ratio for randombits")
	("JaccardXorRate", po::value(&jaccardXorRate)->default_value(jaccardXorRate)
	 ,"default =1(0-1), sparse xor can speed up, but may lose precision.VarXorRate * jaccard_size() ")
	
	("printXor",po::value(&printXor)->default_value(0),"default(false)")
	("trimOnly",po::value(&trimOnly)->default_value(0),"default(false)")
    ("tApproxMC", po::value(&tApproxMC)->default_value(tApproxMC)
        , "Number of measurements")
  ("tJaccardMC", po::value(&tJaccardMC)->default_value(tJaccardMC)
        , "Number of measurements for jaccard hash")
    ("startIteration", po::value(&startIteration)->default_value(startIteration), "")
	("lowerFib",po::value(&LowerFib)->default_value(0),"")

	("UpperFib",po::value(&UpperFib)->default_value(0),"")
    ("lowest Jaccard Index ", po::value(&endJaccardIndex)->default_value(1), "")
    ("looptout", po::value(&loopTimeout)->default_value(loopTimeout)
        , "Timeout for one measurement, consisting of finding pivotAC solutions")
    ("cuspLogFile", po::value(&cuspLogFile)->default_value(cuspLogFile),"")
    ("unset", po::value(&unset_vars)->default_value(unset_vars),
     "Try to ask the solver to unset some independent variables, thereby"
     "finding more than one solution at a time")
 ("Parallel", po::value(&Parallel)->default_value(Parallel),
     "parallel"
     "findingmore than one solution at a time")
 ("parity", po::value(&Parity)->default_value(Parity),
     "parity"
     "hsh parity for counting")
 ("JaccardIndex",po::value(&singleIndex)->default_value(singleIndex),
  "jaccard index"
  "choose one otherwise use max")

    ;

    help_options_simple.add(approxMCOptions);
    help_options_complicated.add(approxMCOptions);
}

void CUSP::add_supported_options()
{
    Main::add_supported_options();
    add_approxmc_options();
}

void print_xor(const vector<uint32_t>& vars, const uint32_t rhs)
{
	std::ofstream  ff;
	std::ostringstream filename("");
	filename<<"xor.txt";
	ff.open(filename.str(),std::ofstream::out|std::ofstream::app);
	
	ff<<"x";
	ff<< (rhs ?"":"-")<< vars[0]+1 << " ";
	for (size_t i = 1; i < vars.size(); i++) {
		ff<< vars[i]+1;
        if (i < vars.size()-1) {
			ff << " ";
        }
    }
	ff<<"0\n";

	ff.close();
}

bool CUSP::openLogFile()
{
    cusp_logf.open(cuspLogFile.c_str());
    if (!cusp_logf.is_open()) {
        cout << "Cannot open CUSP log file '" << cuspLogFile
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
inline T findMin(vector<T>& numList)
{
    T min = std::numeric_limits<T>::max();
    for (const auto a: numList) {
        if (a < min) {
            min = a;
        }
    }
    return min;
}
 bool CUSP::checkParity(int parity,string randomBits,int num_xor_cls,int size,int i,int j){
	for(int k=0;k<parity;++k){
		if(randomBits[ size * i + j+ size*k*num_xor_cls]!='1'){
			cout<<size * i + j+ size*k*num_xor_cls;
			return false;
		}
	}
	return true;
}
bool CUSP::AddHash(uint32_t num_xor_cls, vector<Lit>& assumps,SATSolver* solver)
{
	cout<<"solver="<<solver;
	double ratio=xorRate;
	string randomBits = GenerateRandomBits_prob((independent_vars.size()) * num_xor_cls,ratio);
	string randomBits_rhs=GenerateRandomBits(num_xor_cls);
	bool rhs = true;
	vector<uint32_t> vars;

	for (uint32_t i = 0; i < num_xor_cls; i++) {
		//new activation variable
		solver->new_var();
		uint32_t act_var = solver->nVars()-1;
        assumps.push_back(Lit(act_var, true));

		vars.clear();
		vars.push_back(act_var);
		rhs = (randomBits_rhs[i] == '1');
		for (uint32_t j = 0; j < independent_vars.size(); j++) {
			if(randomBits[i*independent_vars.size()+j]=='1')    
			  vars.push_back(independent_vars[j]);
	}
	solver->add_xor_clause(vars, rhs);
	if (conf.verbosity||printXor) {
		print_xor(vars, rhs);
	}
}
return true;
}

void CUSP::trimVar(vector<uint32_t> &vars){
	vector<uint32_t> new_vars;
	for(int i=0;i<vars.size();++i){
		uint32_t var=vars[i];
		vector<Lit>assume;
		std::cerr<<"var="<<var;
		assume.clear();
		assume.push_back(Lit(var,true));
		double start=cpuTimeTotal();
		lbool ret0=solver->solve(&assume);
		std::cout<<"\ntime:"<<cpuTimeTotal()-start;
		assume.clear();
		std::cerr<<"!var="<<var;
		assume.push_back(Lit(var,false));
		lbool ret1=solver->solve(&assume);
		if(ret0!=ret1){
			  std::cerr<<"delete "<<var<<"\n";
		}else{
			std::cout<<((ret0==l_True)?"ret0=true":"ret0!=true")<<((ret1==l_True)?"ret1=true":"ret1!=true");
			new_vars.push_back(var);
		}
	}
	vars=new_vars;

}

int64_t CUSP::SampledBoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps, const vector<Lit>& jassumps,SATSolver* solver){
	size_t size=independent_vars.size();
	cout<<"size of ind="<<size<<"\n";
	std::string sampleOne;

	lbool ret;
	int64_t solutions=-2;

	uint64_t samplelog=(size-assumps.size());
	if(samplelog<=log2(maxSolutions)){

	uint64_t sampleSize=(1<<(size-assumps.size()));
		while(independent_samples.size()<sampleSize){
			sampleOne=GenerateRandomBits_prob(size,0.5);
			independent_samples.insert(sampleOne);
		}
		std::set<string>::iterator sampleit=independent_samples.begin();
		solutions=0;
		for(int i=0;i<sampleSize;++i){
			sampleOne=*sampleit;
			vector<Lit> new_assumps(jassumps);
			for(int j=0;j<size;++j){
				assert(sampleOne.size()>j);
				assert(independent_vars.size()>j);
				new_assumps.push_back(Lit(independent_vars[j],sampleOne[j]=='1'));
			}
			ret = solver->solve(&new_assumps);
			if (ret != l_True){
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
int64_t CUSP::BoundedSATCount(uint32_t maxSolutions,uint64_t hashCount, LitStr * jaccardAssumpStr,LitStr * assumpStr ,SATSolver* solver)
{
//    cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;
    //Set up things for adding clauses that can later be removed
#if PARALLEL 
	//	SATSolver *solver=solvers[omp_get_thread_num()];
#endif
	double start_time = cpuTime();
	uint64_t solutions = 0;
	lbool ret;
	bool firstRound=true;

	if(jaccardAssumpStr){
	//	jaccardAssumpStr->print();
		SetHashByString(singleIndex,jaccard_vars,jaccardAssumpStr->randomBits,jaccardAssumpStr->randomBits_rhs,solver);
	}
	if(assumpStr){
	//	assumpStr->print();
		SetHashByString(hashCount,independent_vars,assumpStr->randomBits,assumpStr->randomBits_rhs,solver);
	}
	if(printXor==1&& assumpStr){
		exit(0);
	}
	while (solutions < maxSolutions) {
		//solver->set_max_confl(10*1000*1000);
		double this_iter_timeout = loopTimeout-(cpuTime()-start_time);

		solver->set_timeout_all_calls(this_iter_timeout);
		ret = solver->solve();
		if (ret != l_True)
		  break;

		size_t num_undef = 0;
		if (solutions < maxSolutions) {
			vector<Lit> lits;
			for (int i=0;i<independent_vars.size();++i) {
				uint32_t var=independent_vars[i];
				if (solver->get_model()[var] != l_Undef) {
					lits.push_back(Lit(var, solver->get_model()[var] == l_True));
				} else {
					num_undef++;
				}
			}
			solver->add_clause(lits);
			string sol="";
			for(int i=1;i<lits.size();i++){
				sol+=lits[i].sign()?"1":"0";
			}
			if(cachedSolutions.count(sol)==0)
			  cachedSolutions.insert(sol);
		}
		if (num_undef) {
			cout << "WOW Num undef:" << num_undef << endl;
		}

		//Try not to be crazy, 2**30 solutions is enough
		if (num_undef <= 30) {
			solutions += 1U << num_undef;
		} else {
			solutions += 1U << 30;
            cout << "WARNING, in this cut there are > 2**30 solutions indicated by the solver!" << endl;
        }
    }

//	cout<<"time in this loop :"<<(cpuTime()-start_time);
    if (solutions > maxSolutions) {
        solutions = maxSolutions;
    }

	reset_solver();
    if (ret == l_Undef) {
        must_interrupt.store(false, std::memory_order_relaxed);
        
		std::cout<<"timeout,but explored count="<<solutions;
		return -1;
    }
    return solutions;
}

int64_t CUSP::BoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps, const vector<Lit>& jassumps,SATSolver* solver)
{
//    cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;
    //Set up things for adding clauses that can later be removed
#if PARALLEL 
//	SATSolver *solver=solvers[omp_get_thread_num()];
#endif
		solver->new_var();
    uint32_t act_var = solver->nVars()-1;
    vector<Lit> new_assumps(assumps);
	new_assumps.insert(new_assumps.end(),jassumps.begin(),jassumps.end());
    new_assumps.push_back(Lit(act_var, true));

    double start_time = cpuTime();
    uint64_t solutions = 0;
	lbool ret;
	bool firstRound=true;
	solutions=SampledBoundedSATCount(maxSolutions,assumps,jassumps,solver);
	if(solutions==-2)
	  solutions=0;
	else{
		std::cout<<"sampled solu:"<<solutions<<"\n";
		return solutions;
	}
	while (solutions < maxSolutions) {
		//solver->set_max_confl(10*1000*1000);
		double this_iter_timeout = loopTimeout-(cpuTime()-start_time);

		solver->set_timeout_all_calls(this_iter_timeout);
		ret = solver->solve(&new_assumps);
		if (ret != l_True)
		  break;

		size_t num_undef = 0;
		if (solutions < maxSolutions) {
			vector<Lit> lits;
			lits.push_back(Lit(act_var, false));
			for (int i=0;i<independent_vars.size();++i) {
				uint32_t var=independent_vars[i];
				if (solver->get_model()[var] != l_Undef) {
					lits.push_back(Lit(var, solver->get_model()[var] == l_True));
				} else {
					num_undef++;
				}
			}

			solver->add_clause(lits);
			string sol="";
			for(int i=1;i<lits.size();i++){
				sol+=lits[i].sign()?"1":"0";
			}
			if(cachedSolutions.count(sol)==0)
			  cachedSolutions.insert(sol);
		}
		if (num_undef) {
			cout << "WOW Num undef:" << num_undef << endl;
		}

		//Try not to be crazy, 2**30 solutions is enough
		if (num_undef <= 30) {
			solutions += 1U << num_undef;
		} else {
			solutions += 1U << 30;
            cout << "WARNING, in this cut there are > 2**30 solutions indicated by the solver!" << endl;
        }
    }

//	cout<<"time in this loop :"<<(cpuTime()-start_time);
    if (solutions > maxSolutions) {
        solutions = maxSolutions;
    }

    //Remove clauses added
    vector<Lit> cl_that_removes;
    cl_that_removes.push_back(Lit(act_var, false));
    solver->add_clause(cl_that_removes);

    //Timeout
    if (ret == l_Undef) {
        must_interrupt.store(false, std::memory_order_relaxed);
        
		std::cout<<"timeout,but explored count="<<solutions;
		return -1;
    }
    return solutions;
}
void CUSP::cache_clear(){
	cachedSolutions.clear();
	independent_samples.clear();

}
int64_t CUSP::BoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps,SATSolver * solver)
{
	// cout << "BoundedSATCount looking for " << maxSolutions << " solutions" << endl;
	//Set up things for adding clauses that can later be removed
#if PARALLEL 
//	SATSolver *solver=solvers[omp_get_thread_num()];
#endif
	solver->new_var();
    uint32_t act_var = solver->nVars()-1;
    vector<Lit> new_assumps(assumps);
    new_assumps.push_back(Lit(act_var, true));

    double start_time = cpuTime();
    uint64_t solutions = 0;
	lbool ret;
	bool firstRound=true;
	int nAddedClause=0;
	while (solutions < maxSolutions) {
		//solver->set_max_confl(10*1000*1000);
		double this_iter_timeout = loopTimeout-(cpuTime()-start_time);
		if(solutions>maxSolutions/2 && this_iter_timeout<loopTimeout/5){
				this_iter_timeout=loopTimeout/4;
		}
		solver->set_timeout_all_calls(this_iter_timeout);
		ret = solver->solve(&new_assumps);
		/*if(firstround){
			for (const uint32_t i: dependent_vars) {
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
			for (const uint32_t var: independent_vars) {
				if (solver->get_model()[var] != l_Undef) {
					lits.push_back(Lit(var, solver->get_model()[var] == l_True));
				} else {
					num_undef++;
				}
			}
			solver->add_clause(lits);
			nAddedClause++;
		}
		if (num_undef) {
			cout << "WOW Num undef:" << num_undef << endl;
		}

		//Try not to be crazy, 2**30 solutions is enough
		if (num_undef <= 30) {
			solutions += 1U << num_undef;
		} else {
			solutions += 1U << 30;
            cout << "WARNING, in this cut there are > 2**30 solutions indicated by the solver!" << endl;
        }
    }
    if (solutions > maxSolutions) {
        solutions = maxSolutions;
    }
    //Remove clauses added
    vector<Lit> cl_that_removes;
    cl_that_removes.push_back(Lit(act_var, false));
    solver->add_clause(cl_that_removes);
    //Timeout
    if (ret == l_Undef) {
        must_interrupt.store(false, std::memory_order_relaxed);
		std::cout<<"explored count="<<solutions;
		return -1;
    }
	return solutions;
}
void SATCount::summarize(){
	vector<uint64_t>list=numHashList;
	vector<int64_t>cnt_list=numCountList;
	auto minHash = findMin(list);
	if(list.size()<=0){
		return;
	}
	if(list.size()==1){
		cellSolCount=cnt_list[0];
		hashCount=list[0];
	}
	auto cnt_it = cnt_list.begin();
	for (auto hash_it = list.begin()
				; hash_it != list.end() && cnt_it != cnt_list.end()
				; hash_it++, cnt_it++
		) {
		*cnt_it *= pow(2, (*hash_it) - minHash);
	}

	int medSolCount = findMedian(cnt_list);
	cellSolCount = medSolCount;
	hashCount = minHash;
}
int CUSP::OneRoundFor3NoHash_slow(vector<LitStr> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL){
	int64_t s[3];
	int64_t hashCount=0;
	cache_clear();
	double start_time = cpuTime();
	int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC+1,0,&jaccardAssumps[0],NULL,solver);

	cout<<"\ncost time:"<<cpuTime()-start_time<<"\n"<<"count="<<currentNumSolutions;
	//Din't find at least pivotApproxMC+1
	if(currentNumSolutions==0){
		return -1;
	}
	if(currentNumSolutions<pivotApproxMC+1){
		s[0]=currentNumSolutions;
		std::set<std::basic_string<char> > cachedSolutions_tmp=cachedSolutions;
		int pos=1;
		s[1]=0;
		while(s[1]==0&& pos<10){		
			cachedSolutions= cachedSolutions_tmp;
			s[1] = BoundedSATCount(pivotApproxMC*2+1,0,&jaccardAssumps[1], NULL,solver);
			jaccardAssumps[1].random_rhs(pos);
			pos++;
		}

		pos--;
		jaccardAssumps[1].random_rhs(pos);
		//s[1] = BoundedSATCount(pivotApproxMC*2+1,0,&jaccardAssumps[1],NULL,solver);
		if(s[1]<=0||s[1]>pivotApproxMC*2){
			//unbalanced jaccard sampling, giveup
			return -1;
		}
		s[2]=cachedSolutions.size();// BoundedSATCount(s[1]+s[0],assumps,jaccardAssumps[2],solver);
		cache_clear();
		if(s[2]<=0|| s[2]>(s[1]+s[0])){
			//impossible reach
			assert(0);
			return -1;
			//goto resample;
		}
		for(int k=0;k<scounts.size();++k)
		{
			scounts[k].numHashList.push_back(hashCount);
			scounts[k].numCountList.push_back(s[k]);
			std::cout<<"s["<<k<<"]="<<s[k]<<"\n";
			scounts[k].summarize();
		}

		return 0;
	}else
	  hashCount++;
	return hashCount;
}

 int CUSP::OneRoundFor3NoHash(vector<vector<Lit>> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL){
	int64_t s[3];
		vector<Lit> assumps;
		int64_t hashCount=0;
		cache_clear();

    double start_time = cpuTime();
	int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps[0],solver);
	
    cout<<"\ncost time:"<<cpuTime()-start_time<<"\n"<<"count="<<currentNumSolutions;
	//Din't find at least pivotApproxMC+1
	if(currentNumSolutions<pivotApproxMC+1){
		s[0]=currentNumSolutions;
		s[1] = BoundedSATCount(pivotApproxMC*2+1, assumps,jaccardAssumps[1],solver);
		if(s[1]<=0||s[1]>pivotApproxMC*2){
			//unbalanced jaccard sampling, giveup
			return -1;
		}
		s[2]=cachedSolutions.size();// BoundedSATCount(s[1]+s[0],assumps,jaccardAssumps[2],solver);
		cache_clear();
		if(s[2]<=0|| s[2]>(s[1]+s[0])){
			//impossible reach
			assert(0);
			return -1;
			//goto resample;
		}
		for(int k=0;k<scounts.size();++k)
		{
			scounts[k].numHashList.push_back(hashCount);
			scounts[k].numCountList.push_back(s[k]);
		
		scounts[k].summarize();
		}

		return 0;
	}else
	  hashCount++;
	return hashCount;
}
int CUSP::OneRoundFor3WithHash_slow(bool readyPrev,bool readyNext,std::set<std::string> nextCount,uint64_t &hashCount,LitStr& assumps ,std::vector<LitStr> jaccardAssumps,std::vector<SATCount>& scounts,SATSolver * solver=NULL){
	int repeatTry=0;
	while(true){
		std::cout<<"hashCount="<<hashCount;
		genHashForAssump(independent_vars,hashCount,assumps);
		//SetHash(hashCount,hashVars,assumps,solver);
		int64_t s[3];
		double myTime = cpuTimeTotal();
		cache_clear();
		int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1,hashCount, &jaccardAssumps[0],&assumps,solver);
		s[0]=currentNumSolutions;
		cout	<<"solver->nvar()="<<solver->nVars()
			<< "Number of XOR hashes active: " << hashCount << endl
			<< currentNumSolutions << ", " << pivotApproxMC
			<<",time="<<(cpuTimeTotal() - myTime) <<endl;

		if (currentNumSolutions < 0) {
			//Remove all hashes
			if (repeatTry < 2) {    /* Retry up to twice more */
				assert(hashCount > 0);
				//hashCount-=lower+repeatTry;
				cout <<"repeatTry="<< repeatTry<<"Timeout, try again -- " <<repeatTry<<"hash="<<hashCount<< endl;
				repeatTry +=1;
				return TIMEOUT;
			} else {
				//this set of hashes does not work, go up
				//SetHash(hashCount + 1, hashVars, assumps,solver);
				cout << "Timeout, moving up" << endl;
				return RETRY_JACCARD_HASH;
			}
			continue;
		}
	/*	if(currentNumSolutions==0){
			lbool ret=solver->solve(&assumps);
			if(ret=lTrue){
				return RETRY_JACCARD_HASH;
			}

		}*/
		if (currentNumSolutions < pivotApproxMC + 1) {

			if (readyPrev) {
				double myTime1 = cpuTimeTotal();
				s[1]=0;
				int pos=1;
				std::set<std::basic_string<char> > cachedSolutions_tmp=cachedSolutions;
				while(s[1]==0&& pos<10){		
					cachedSolutions= cachedSolutions_tmp;
					s[1] = BoundedSATCount(pivotApproxMC*2+1,hashCount,&jaccardAssumps[1], &assumps,solver);
					jaccardAssumps[1].random_rhs(pos);
					pos++;
				}
				pos--;
				jaccardAssumps[1].random_rhs(pos);
				std::cout<<"s[1]"<<s[1]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";
				if(s[1]<0||s[1]>pivotApproxMC*2){
					//unbalanced sampling, giveup
withhashresample:
					cout<<"s[1]="<<s[1]<<"\n";
					return RETRY_JACCARD_HASH;
					//return NEAR_RESULT;
				}
				double myTime2=cpuTimeTotal();
				s[2]=cachedSolutions.size();// BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);
				std::cout<<"s[2]"<<s[2]<<",time:"<<cpuTimeTotal()-myTime2<<"\n";
				if(s[2]<0|| s[2]>(s[1]+s[0])){
					//impossible reach
					assumps.clear();
					return RETRY_JACCARD_HASH;
				}
				for(int k=0;k<scounts.size();++k)
				{
					scounts[k].numHashList.push_back(hashCount);
					scounts[k].numCountList.push_back(s[k]);
				}
				return GOT_RESULT_LOWER;
			}
			//return NEAR_RESULT;
			return currentNumSolutions;
		}else{
			if(readyNext){
				hashCount++;
				genHashForAssump(independent_vars,hashCount,assumps);
				s[0]=nextCount.size();
				double myTime1=cpuTimeTotal();
				cache_clear();
				//	s[0]= BoundedSATCount(pivotApproxMC*2+1,assumps,jaccardAssumps[0],solver);
				s[1]=0;
				int pos=1;
				while(s[1]==0&& pos<10){		
					cachedSolutions.clear();
					s[1] = BoundedSATCount(pivotApproxMC*2+1,hashCount,&jaccardAssumps[1], &assumps,solver);
					jaccardAssumps[1].random_rhs(pos);
					pos++;
				}
				pos--;
				jaccardAssumps[1].random_rhs(pos);
				cachedSolutions.insert(nextCount.begin(),nextCount.end());
			//	s[1] = BoundedSATCount(pivotApproxMC*2+1,hashCount, &jaccardAssumps[1], &assumps,solver);				
				std::cout<<"s[1]"<<s[1]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";
					cout<<"s[0]="<<s[0]<<"s[1]"<<s[1];
				if(s[1]<=0){
					//unbalanced sampling, giveup
					assumps.clear();
					return RETRY_JACCARD_HASH;
				}
				if(s[1]>pivotApproxMC*2+1){
					return RETRY_JACCARD_HASH;
				}
				myTime1=cpuTimeTotal();
				for(auto one : cachedSolutions){
			//		cout<<"one="<<one<<"\n";
				}
				s[2]=cachedSolutions.size();
				//s[2]= BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);
				std::cout<<"s[2]"<<s[2]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";

				if(s[2]<=0|| s[2]>(s[1]+s[0])){
					//impossible reach
					assert(0);
				}
				for(int k=0;k<scounts.size();++k)
				{
					scounts[k].numHashList.push_back(hashCount);
					scounts[k].numCountList.push_back(s[k]);
				}
				return GOT_RESULT_UPPER;
			}

			assert(currentNumSolutions == pivotApproxMC+1);
			return TOO_MUCH;
		}
	}
}


int CUSP::OneRoundFor3WithHash(bool readyPrev,bool readyNext,uint64_t nextCount,uint64_t &hashCount,map<uint64_t,Lit>& hashVars,vector<Lit>assumps ,vector<vector<Lit>> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL){
	int repeatTry=0;
	while(true){
		std::cout<<"hashCount="<<hashCount;
		SetHash(hashCount,hashVars,assumps,solver);
		int64_t s[3];
		double myTime = cpuTimeTotal();
		cache_clear();

		int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,jaccardAssumps[0],solver);
		s[0]=currentNumSolutions;
		cout	<<"solver->nvar()="<<solver->nVars()
			<< "Number of XOR hashes active: " << hashCount << endl
			<< currentNumSolutions << ", " << pivotApproxMC
			<<",time="<<(cpuTimeTotal() - myTime) <<endl;

		if (currentNumSolutions < 0) {
			//Remove all hashes
			if (repeatTry < 2) {    /* Retry up to twice more */
				assert(hashCount > 0);
				//hashCount-=lower+repeatTry;
				cout <<"repeatTry="<< repeatTry<<"Timeout, try again -- " <<repeatTry<<"hash="<<hashCount<< endl;
				repeatTry +=1;
				return TIMEOUT;
				continue;
			} else {
				//this set of hashes does not work, go up
				//SetHash(hashCount + 1, hashVars, assumps,solver);
				cout << "Timeout, moving up" << endl;
				return RETRY_JACCARD_HASH;
			}
			continue;
		}
	/*	if(currentNumSolutions==0){
			lbool ret=solver->solve(&assumps);
			if(ret=lTrue){
				return RETRY_JACCARD_HASH;
			}

		}*/
		if (currentNumSolutions < pivotApproxMC + 1) {

			if (readyPrev) {
				double myTime1 = cpuTimeTotal();
				s[1] = BoundedSATCount(pivotApproxMC*2+1, assumps,jaccardAssumps[1],solver);
				std::cout<<"s[1]"<<s[1]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";
				if(s[1]<0||s[1]>pivotApproxMC*2){
					//unbalanced sampling, giveup
withhashresample:
					cout<<"s[1]="<<s[1]<<"\n";
					assumps.clear();
					hashVars.clear();
					solver->simplify(&assumps);
					return RETRY_JACCARD_HASH;
					//return NEAR_RESULT;
				}
				
				double myTime2=cpuTimeTotal();
				for(auto one : cachedSolutions){
					//cout<<"one="<<one<<"\n";
				}

				s[2]=cachedSolutions.size();// BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);
				std::cout<<"s[2]"<<s[2]<<",time:"<<cpuTimeTotal()-myTime2<<"\n";
				if(s[2]<0|| s[2]>(s[1]+s[0])){
					//impossible reach
					assumps.clear();
					hashVars.clear();
					solver->simplify(&assumps);
					return RETRY_JACCARD_HASH;
				}
				for(int k=0;k<scounts.size();++k)
				{
					scounts[k].numHashList.push_back(hashCount);
					scounts[k].numCountList.push_back(s[k]);
				}
				return GOT_RESULT_LOWER;
			}
			//return NEAR_RESULT;
			return currentNumSolutions;
		}else{
			if(readyNext){
				hashCount++;
				SetHash(hashCount,hashVars,assumps,solver);
				s[0]=nextCount;
				double myTime1=cpuTimeTotal();
				cache_clear();
				s[0]= BoundedSATCount(pivotApproxMC*2+1,assumps,jaccardAssumps[0],solver);
				s[1] = BoundedSATCount(pivotApproxMC*2+1, assumps,jaccardAssumps[1],solver);				
				std::cout<<"s[1]"<<s[1]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";
					cout<<"s[0]="<<s[0]<<"s[1]"<<s[1];
				if(s[1]<=0){
					//unbalanced sampling, giveup
					assumps.clear();
					hashVars.clear();
					solver->simplify(&assumps);
					return RETRY_JACCARD_HASH;
				}
				if(s[1]>pivotApproxMC*2+1){
					return RETRY_JACCARD_HASH;
				}
				myTime1=cpuTimeTotal();
				for(auto one : cachedSolutions){
			//		cout<<"one="<<one<<"\n";
				}
				s[2]=cachedSolutions.size();
				//s[2]= BoundedSATCount(s[1]+s[0]+1,assumps,jaccardAssumps[2],solver);
				std::cout<<"s[2]"<<s[2]<<",time:"<<cpuTimeTotal()-myTime1<<"\n";

				if(s[2]<=0|| s[2]>(s[1]+s[0])){
					//impossible reach
					assert(0);
				}
				for(int k=0;k<scounts.size();++k)
				{
					scounts[k].numHashList.push_back(hashCount);
					scounts[k].numCountList.push_back(s[k]);
				}
				return GOT_RESULT_UPPER;
			}

			assert(currentNumSolutions == pivotApproxMC+1);
			return TOO_MUCH;
		}
	}
}
void printFor3(int ret){
	string str;
	switch(ret){
		case RETRY_IND_HASH:
			str="RETRY_IND_HASH";
			break;

		case RETRY_JACCARD_HASH:
			str="RETRY_JACCARD_HASh";
			break;
		case GOT_RESULT_UPPER:
			str="GOT_RESULT_upper";
			break;

		case GOT_RESULT_LOWER:
			str="GOT_RESULT";
			break;


		case TOO_MUCH:
			str="TOO_MUCH";
			break;
		case TIMEOUT:
			str="TIMEOUT";
			break;
		default:
			str="NEAR_RESULT";
			break;
	}
	std::cout<<str;
}

int CUSP::OneRoundFor3_slow(uint64_t jaccardHashCount,JaccardResult* result, uint64_t &mPrev,uint64_t &hashPrev  ,vector<LitStr> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL)
{
	//	solver->simplify(&jaccardAssumps);
	uint64_t& hashCount=result->hashCount[jaccardHashCount];
	bool& searched=result->searched[jaccardHashCount];
	LitStr assumps;
	double myTime = cpuTimeTotal();
	uint64_t jaccardIndex=jaccardHashCount;
	bool less=false,more=false;
	if(solver==NULL){
		solver=this->solver;
	}
	//	hashCount=startIteration;
	if (hashCount == 0) {
		int ret=OneRoundFor3NoHash_slow(jaccardAssumps,scounts,solver);
		if(ret==0)
		  return 0;
		if(ret<0){
			return -1;
		}
		hashCount=ret;
		UpperFib=UpperFib?UpperFib:independent_vars.size();
		hashCount=(LowerFib+UpperFib)/2;
		std::cout<<"starter hashcount="<<hashCount<<"\n";
	}

	//	hashCount=startIteration;
	for (uint32_t j = 0; j < tApproxMC; j++) {
		map<uint64_t,std::set<std::string> > countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		uint32_t repeatTry = 0;
		uint64_t numExplored = 1;
	//	uint64_t lowerFib = searched?(hashCount-2):0, upperFib = searched?(hashCount+2):independent_vars.size();
	//
		uint64_t lowerFib = LowerFib, upperFib = UpperFib?UpperFib:independent_vars.size();
		while (numExplored < independent_vars.size()) {
			myTime = cpuTimeTotal();
			uint64_t swapVar = hashCount;
			//cout<<"change the size to "<<solver->get_Nclause();
			//solver->simp:lify(&assumps);

			bool readyPrev=((succRecord.find(hashCount-1)!=succRecord.end())&&(succRecord[hashCount-1] ==0));
			//	bool readyPrev=searched?true:((succRecord.find(hashCount-1)!=succRecord.end())&&(succRecord[hashCount-1] ==0));
			bool readyNext=((succRecord.find(hashCount+1) != succRecord.end())&&(succRecord[hashCount+1]==0));
			//bool readyNext=searched?true:((succRecord.find(hashCount+1) != succRecord.end())&&(succRecord[hashCount+1]==0));
			std::set<std::string> nextCount;
			if(succRecord.find(hashCount+1) != succRecord.end()){
				nextCount=countRecord[hashCount+1];
			}
			std::cout<<"\n------------------------\n";
			int ret=OneRoundFor3WithHash_slow(readyPrev,readyNext,nextCount,hashCount,assumps,jaccardAssumps,scounts,solver);
			printFor3(ret);
			int64_t checkJaccard;
			switch(ret){
				case TIMEOUT:
					assumps.clear();
					break;
				case RETRY_IND_HASH:
					assumps.clear();
					break;
				case RETRY_JACCARD_HASH:
				/*	 checkJaccard= BoundedSATCount(2,0,&jaccardAssumps[0],NULL,solver);
					if(checkJaccard>0){
						std::cout<<"there is solutions, but hashCount too large to find one";
						assumps.clear();
						goto TOO_SMALL_ENTRY;
						break;
					}*/
					assumps.clear();
					hashVars.clear();
					return -1;
				case GOT_RESULT_LOWER:
					numExplored = lowerFib+independent_vars.size()-hashCount;
					std::cout<<"numExplored="<<numExplored<<" lowerFib="<<lowerFib;
					mPrev = hashCount;
					break;
				case GOT_RESULT_UPPER:
					numExplored = independent_vars.size()+hashCount-upperFib;
					std::cout<<"numExplored="<<numExplored<<" lowerFib="<<lowerFib;
					mPrev = hashCount;
					break;

				case TOO_MUCH:
					numExplored = hashCount + independent_vars.size()-upperFib;
					succRecord[hashCount] = 1;
					if (searched||(abs(hashCount - mPrev) < 2 && mPrev!=0)) {
						lowerFib = hashCount;
						hashCount ++;
					} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
						lowerFib = hashCount;
						hashCount = (lowerFib+upperFib)/2;
					} else {
						//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
						hashCount = lowerFib + (hashCount -lowerFib)*2;
					}
					hashPrev = swapVar;
					break;
				default:
				//case NEAR_RESULT:
					numExplored = lowerFib+independent_vars.size()-hashCount;
					succRecord[hashCount] = 0;
					countRecord[hashCount] =cachedSolutions;
TOO_SMALL_ENTRY:
					if (searched||(abs(hashCount-mPrev) <= 2 && mPrev != 0)) {
						upperFib = hashCount;
						hashCount--;
					} else {
						if (hashPrev > hashCount) {
							hashPrev = 0;
						}
						//int delta=log2((pivotApproxMC+1)/ret);
						upperFib = hashCount;
						if (hashPrev > lowerFib) {
							lowerFib = hashPrev;
						}
					//	uint64_t tmp=hashCount-2*delta;
					//	lowerFib=(lowerFib>tmp)?lowerFib:tmp;
						hashCount = (upperFib+lowerFib)/2;
						std::cout<<"lowerFib="<<lowerFib<<"upperFib="<<upperFib<<"hashCount="<<hashCount;
					}
					break;
			}
			std::cout<<"lowerFib="<<lowerFib<<"upperFib="<<upperFib<<"hashCount="<<hashCount;
			std::cout<<"\n===================="<<"\n";
		}
		assumps.clear();
		hashCount =mPrev;
	}
	std::cout<<"return from OneRoundFor3";
	return 0;
}

int CUSP::OneRoundFor3(uint64_t jaccardHashCount,JaccardResult* result, uint64_t &mPrev,uint64_t &hashPrev  ,vector<vector<Lit>> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL)
{
	//	solver->simplify(&jaccardAssumps);
	uint64_t& hashCount=result->hashCount[jaccardHashCount];
	bool& searched=result->searched[jaccardHashCount];
	vector<Lit> assumps;
	double myTime = cpuTimeTotal();
	uint64_t jaccardIndex=jaccardHashCount;
	bool less=false,more=false;
	if(solver==NULL){
		solver=this->solver;
	}
	//	hashCount=startIteration;
	if (hashCount == 0) {
		int ret=OneRoundFor3NoHash(jaccardAssumps,scounts,solver);
		if(ret==0)
		  return 0;
		if(ret<0){
			return -1;
		}
		hashCount=ret;
		UpperFib=UpperFib?UpperFib:independent_vars.size();
		if(LowerFib)	
		  hashCount=(LowerFib+UpperFib)/2;
		else
		  hashCount=1;
		std::cout<<"starter hashcount="<<hashCount<<"\n";
	}

	//	hashCount=startIteration;
	for (uint32_t j = 0; j < tApproxMC; j++) {
		map<uint64_t,uint32_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		uint32_t repeatTry = 0;
		uint64_t numExplored = 1;
	//	uint64_t lowerFib = searched?(hashCount-2):0, upperFib = searched?(hashCount+2):independent_vars.size();
	//
		uint64_t lowerFib = LowerFib, upperFib = UpperFib?UpperFib:independent_vars.size();
		while (numExplored < independent_vars.size()) {
			myTime = cpuTimeTotal();
			uint64_t swapVar = hashCount;
			//cout<<"change the size to "<<solver->get_Nclause();
			//solver->simp:lify(&assumps);
			
			bool readyPrev=((succRecord.find(hashCount-1)!=succRecord.end())&&(succRecord[hashCount-1] ==0));
		//	bool readyPrev=searched?true:((succRecord.find(hashCount-1)!=succRecord.end())&&(succRecord[hashCount-1] ==0));
			bool readyNext=((succRecord.find(hashCount+1) != succRecord.end())&&(succRecord[hashCount+1]==0));
			//bool readyNext=searched?true:((succRecord.find(hashCount+1) != succRecord.end())&&(succRecord[hashCount+1]==0));
			uint32_t nextCount=-1;
			if(succRecord.find(hashCount+1) != succRecord.end()){
				nextCount=countRecord[hashCount+1];
			}
			std::cout<<"\n------------------------\n";
			int ret=OneRoundFor3WithHash(readyPrev,readyNext,nextCount,hashCount,hashVars,assumps,jaccardAssumps,scounts,solver);
			printFor3(ret);
int64_t checkJaccard;
			switch(ret){
				case TIMEOUT:
					assumps.clear();
					hashVars.clear();
					break;
				case RETRY_IND_HASH:
					assumps.clear();
					hashVars.clear();
					solver->simplify(&assumps);
					break;

				case RETRY_JACCARD_HASH:

					 checkJaccard= BoundedSATCount(2,assumps,jaccardAssumps[0],solver);
					if(checkJaccard>0){
						std::cout<<"there is solutions, but hashCount too large to find one";
						assumps.clear();
						hashVars.clear();
						goto TOO_SMALL_ENTRY;
						break;
					}
					assumps.clear();
					hashVars.clear();
					return -1;
				case GOT_RESULT_LOWER:
					numExplored = lowerFib+independent_vars.size()-hashCount;
					std::cout<<"numExplored="<<numExplored<<" lowerFib="<<lowerFib;
					mPrev = hashCount;
					break;
				case GOT_RESULT_UPPER:
					numExplored = independent_vars.size()+hashCount-upperFib;
					std::cout<<"numExplored="<<numExplored<<" lowerFib="<<lowerFib;
					mPrev = hashCount;
					break;

				case TOO_MUCH:
					numExplored = hashCount + independent_vars.size()-upperFib;
					succRecord[hashCount] = 1;
					if (searched||(abs(hashCount - mPrev) < 2 && mPrev!=0)) {
						lowerFib = hashCount;
						hashCount ++;
					} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
						lowerFib = hashCount;
						hashCount = (lowerFib+upperFib)/2;
					} else {
						//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
						hashCount = lowerFib + (hashCount -lowerFib)*2;
					}
					hashPrev = swapVar;
					break;
				default:
				//case NEAR_RESULT:
					numExplored = lowerFib+independent_vars.size()-hashCount;
					succRecord[hashCount] = 0;
					countRecord[hashCount] = ret;
					
TOO_SMALL_ENTRY:
					if (searched||(abs(hashCount-mPrev) <= 2 && mPrev != 0)) {
						upperFib = hashCount;
						hashCount--;
					} else {
						if (hashPrev > hashCount) {
							hashPrev = 0;
						}
						//int delta=log2((pivotApproxMC+1)/ret);
						upperFib = hashCount;
						if (hashPrev > lowerFib) {
							lowerFib = hashPrev;
						}
					//	uint64_t tmp=hashCount-2*delta;
					//	lowerFib=(lowerFib>tmp)?lowerFib:tmp;
						hashCount = (upperFib+lowerFib)/2;
						std::cout<<"lowerFib="<<lowerFib<<"upperFib="<<upperFib<<"hashCount="<<hashCount;
					}
					break;
			}
			std::cout<<"lowerFib="<<lowerFib<<"upperFib="<<upperFib<<"hashCount="<<hashCount;
			std::cout<<"\n===================="<<"\n";
		}
		assumps.clear();
		solver->simplify(&assumps);
		hashCount =mPrev;
	}
	std::cout<<"return from OneRoundFor3";
	return 0;
}
int CUSP::OneRoundCount(uint64_t jaccardHashCount,JaccardResult* result, uint64_t &mPrev,uint64_t &hashPrev  ,vector<Lit> jaccardAssumps,SATCount& count,SATSolver * solver=NULL)
{
	//	solver->simplify(&jaccardAssumps);
	uint64_t& hashCount=result->hashCount[jaccardHashCount];
	bool& searched=result->searched[jaccardHashCount];
	vector<Lit> assumps;
	double myTime = cpuTimeTotal();

	vector<uint64_t>numHashList0,*numHashList=&numHashList0;
	vector<int64_t> numCountList0,* numCountList=&numCountList0;
	uint64_t jaccardIndex=jaccardHashCount;
	bool less=false,more=false;
	if(solver==NULL){
		solver=this->solver;
	}
	//	hashCount=startIteration;
	if (hashCount == 0) {
		int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps,solver);
		//Din't find at least pivotApproxMC+1
		if (currentNumSolutions <= pivotApproxMC ) {
			count.cellSolCount = currentNumSolutions;
			count.hashCount = 0;
			cout<<"Avg["<<jaccardIndex<<"]="<<count.cellSolCount<<"*2^"<<count.hashCount<<endl;
			return 0;
		}else
		  hashCount++;
	}
	//	hashCount=startIteration;
	for (uint32_t j = 0; j < tApproxMC; j++) {
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		uint32_t repeatTry = 0;
		uint64_t numExplored = 1;
		uint64_t lowerFib = 0, upperFib = independent_vars.size();
		while (numExplored < independent_vars.size()) {
			myTime = cpuTimeTotal();
			uint64_t swapVar = hashCount;
			SetHash(hashCount,hashVars,assumps,solver);
			//cout<<"change the size to "<<solver->get_Nclause();
			//solver->simplify(&assumps);
			int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,jaccardAssumps,solver);
			double currTime=cpuTimeTotal()-myTime;
			cout << "Num Explored: " << numExplored
				<<"solver->nvar()="<<solver->nVars()
				<< "Number of XOR hashes active: " << hashCount<<",jaccard="<<jaccardHashCount << endl
				<< currentNumSolutions << ", " << pivotApproxMC
				<<",time="<<(cpuTimeTotal() - myTime) <<endl;
			/*	if(currTime>4*prevTime)
				pivotApproxMC*=2;
				*/
			//Timeout!
			if (currentNumSolutions < 0) {
				//Remove all hashes
				assumps.clear();
				hashVars.clear();
				if (repeatTry < 2) {    /* Retry up to twice more */
					assert(hashCount > 0);
					hashCount-=2;
					solver->simplify(&assumps);
					cout <<"jaccard="<<jaccardHashCount<<"repeatTry="<< repeatTry<<"Timeout, try again -- " <<repeatTry<<"prev="<<mPrev <<"hash="<<hashCount<< endl;
					SetHash(hashCount,hashVars,assumps,solver);
					repeatTry +=1;
				} else {
					//this set of hashes does not work, go up
					//SetHash(hashCount + 1, hashVars, assumps,solver);
					cout << "Timeout, moving up" << endl;
					return -1;
				}

				continue;
			}
			if(currentNumSolutions==0){
				return -1;
			}
			if(!searched){
				if (currentNumSolutions < pivotApproxMC + 1) {
					numExplored = lowerFib+independent_vars.size()-hashCount;
					if (succRecord.find(hashCount-1) != succRecord.end()
								&& succRecord[hashCount-1] == 1
					   ) {
						numHashList->push_back(hashCount);
						numCountList->push_back(currentNumSolutions);
						mPrev = hashCount;
						//less than pivotApproxMC solutions
						break;
					}
					succRecord[hashCount] = 0;
					countRecord[hashCount] = currentNumSolutions;
					if (abs(hashCount-mPrev) <= 2 && mPrev != 0) {
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
						hashCount = (upperFib+lowerFib)/2;
					}

				} else {
					assert(currentNumSolutions == pivotApproxMC+1);
					numExplored = hashCount + independent_vars.size()-upperFib;
					if (succRecord.find(hashCount+1) != succRecord.end()
								&& succRecord[hashCount+1] == 0
					   ) {
						numHashList->push_back(hashCount+1);
						numCountList->push_back(countRecord[hashCount+1]);
						mPrev = hashCount+1;
						break;
					}
					succRecord[hashCount] = 1;
					if (abs(hashCount - mPrev) < 2 && mPrev!=0) {
						lowerFib = hashCount;
						hashCount ++;
					} else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
						lowerFib = hashCount;
						hashCount = (lowerFib+upperFib)/2;
					} else {
						//printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
						hashCount = lowerFib + (hashCount -lowerFib)*2;
					}
				}
				hashPrev = swapVar;
			}else{//already searched hashCount is precise enough
				if(currentNumSolutions==0){
					if(solver->solve(&jaccardAssumps)==l_False)
					  return -1;
					if(solver->solve(&assumps)==l_False)
					  return -1;
				}
				if (currentNumSolutions < pivotApproxMC + 1) {
					numExplored = lowerFib+independent_vars.size()-hashCount;
					mPrev=hashCount;
					numHashList->push_back(hashCount);
					numCountList->push_back(currentNumSolutions);
					hashCount=hashCount-1;
					upperFib=hashCount;
				}else{
					numExplored = hashCount + independent_vars.size()-upperFib;
					lowerFib=hashCount;	
					hashCount=hashCount+1;
					mPrev=hashCount+1;
				}
			}
		}
		assumps.clear();
		solver->simplify(&assumps);
		hashCount =mPrev;
	/*	cout<<"delete solver";
		delete solver;
		solver = new SATSolver((void*)&conf, &must_interrupt);
		if (unset_vars) {
			solver->set_greedy_undef();
		}
		parseInAllFiles(solver);
		uint32_t maxvar=0;
		for(auto key : jaccardAssumps){
			uint32_t var=abs(key.toInt());
			maxvar=(maxvar>var)?maxvar:var;
		}
		int newVar=maxvar+1-solver->nVars();
		if(newVar>0)
		  solver->new_vars(newVar);
		for(auto xorclause : jaccardXorClause){
			solver->add_xor_clause(xorclause.vars,xorclause.rhs);
		}
		*/
	}
	if (numHashList->size() == 0) {
		count.cellSolCount = 0;
		count.hashCount = 0;
	}else{
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
		count.numHashList=*numHashList;
		count.numCountList= *numCountList;
	}
	cout<<"thread:"<<omp_get_thread_num()<<",Avg["<<jaccardIndex<<"]="<<count.cellSolCount<<"*2^"<<count.hashCount<<endl;
	return 0;
}
void CUSP::addKey2Map(uint64_t jaccardHashCount,map<uint64_t,vector<uint64_t>> &numHashList,map<uint64_t,vector<int64_t>>& numCountList,map<uint64_t,SATCount>& count){
	if(numHashList.find(jaccardHashCount)==numHashList.end()){
		vector<uint64_t> oneHashList;
		vector<int64_t> oneCountList;
		numHashList[jaccardHashCount]=(oneHashList);
		numCountList[jaccardHashCount]=(oneCountList);
		SATCount onecount;
		count[jaccardHashCount]=(onecount);
	}
}

void CUSP::JaccardOneRoundFor3_slow(uint64_t jaccardHashCount,JaccardResult* result ,bool computePrev,SATSolver* solver=NULL){
	if(solver==NULL)
	  solver=solver;
	map<uint64_t,vector<uint64_t>> &numHashList=result->numHashList;
	map<uint64_t,vector<int64_t>>& numCountList=result->numCountList;
	map<uint64_t,SATCount>& count=result->count;
	uint64_t &hashCount=result->hashCount[jaccardHashCount];
	uint64_t mPrev = 0;
	int ret;
	vector<LitStr> jaccard3Assumps;
	while(true){
		//solver->simplify(&jaccardAssumps);
		jaccard3Assumps.clear();
		genHashForJaccard(jaccardHashCount,jaccard3Assumps);
	//	cout<<"sampled jaccard";
		//	solver->simplify(&jaccardAssumps);
		uint64_t hashPrev = LowerFib;
		addKey2Map(jaccardHashCount,numHashList,numCountList,count);
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		//	int64_t currentNumSolutions_lastZero = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps_lastZero);
		SATCount scount0,scount1,scount2;
		JaccardResult result0,result1;
		vector<SATCount>scounts={scount0,scount1,scount2};
		int ret=OneRoundFor3_slow( jaccardHashCount,result,mPrev,hashPrev  ,jaccard3Assumps, scounts,solver);
		if(ret==-1){
			continue;
		}
		std::ofstream  f;
		std::ostringstream filename("");
		filename<<"count_j"<<jaccardHashCount<<"_t"<<omp_get_thread_num();
		f.open(filename.str(),std::ofstream::out|std::ofstream::app);
		for(int j=0;j<3;++j)
		  scounts[j].summarize();
		for(int i=0;i<scounts[0].size()&& i<scounts[1].size()&& i<scounts[2].size();++i){
			f<<scounts[0].str(i)<<"\t"<<scounts[1].str(i)<<"\t"<<scounts[2].str(i)<<"\n";
		}
		//	f<<scount0.str()<<"\t"<<scount1.str()<<"\t"<<scount2.str()<<"\n";
		f.close();
		if(scounts[0].cellSolCount<=0){
			cout<<"cellSolCount<=0,cntinue";
			continue;
		}else{
			for(int j=0;j<2;++j){
				numHashList[jaccardHashCount].push_back(scounts[j].hashCount);
				numCountList[jaccardHashCount].push_back(scounts[j].cellSolCount);
			}
			numHashList[jaccardHashCount+1].push_back(scounts[2].hashCount);
			numCountList[jaccardHashCount+1].push_back(scounts[2].cellSolCount);

			break;
		}

		result->searched[jaccardHashCount-1]=true;
		break;
	}
}



void CUSP::JaccardOneRoundFor3(uint64_t jaccardHashCount,JaccardResult* result ,bool computePrev,SATSolver* solver=NULL){
	if(solver==NULL)
	  solver=solver;
	map<uint64_t,vector<uint64_t>> &numHashList=result->numHashList;
	map<uint64_t,vector<int64_t>>& numCountList=result->numCountList;
	map<uint64_t,SATCount>& count=result->count;
	uint64_t &hashCount=result->hashCount[jaccardHashCount];
	map<uint64_t,Lit> jaccardHashVars;
	uint64_t mPrev = 0;
	vector<Lit >jaccardAssumps,jaccardAssumps_lastZero,jaccardAssumps_two;
	int ret;
	vector<vector<Lit>> jaccard3Assumps;
	vector<string> randomBits3,randomBits_rhs3;
	while(true){
		jaccardAssumps.clear();
		jaccardAssumps_lastZero.clear();
		jaccardHashVars.clear();
		jaccardXorClause.clear();
		jaccard_samples.clear();
		//solver->simplify(&jaccardAssumps);
		if((jaccard_vars.size()-jaccardHashCount)>4){	
			SetJaccardHash(jaccardHashCount,jaccardHashVars,jaccardAssumps,jaccardAssumps_lastZero,solver);
			jaccardAssumps_two= jaccardAssumps_lastZero;
			jaccardAssumps_two.pop_back();
			jaccard3Assumps.push_back(jaccardAssumps);
			jaccard3Assumps.push_back(jaccardAssumps_lastZero);
			jaccard3Assumps.push_back(jaccardAssumps_two);
		}else{
			jaccard3Assumps.push_back(jaccardAssumps);
			jaccard3Assumps.push_back(jaccardAssumps_lastZero);
			jaccard3Assumps.push_back(jaccardAssumps_two);
			SetSampledJaccardHash(jaccardHashCount,jaccardHashVars,jaccard3Assumps,solver);
			cout<<"sampled jaccard";
		}
		//	solver->simplify(&jaccardAssumps);
		uint64_t hashPrev = LowerFib;
		addKey2Map(jaccardHashCount,numHashList,numCountList,count);
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		//	int64_t currentNumSolutions_lastZero = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps_lastZero);
		SATCount scount0,scount1,scount2;
		JaccardResult result0,result1;
		vector<SATCount>scounts={scount0,scount1,scount2};
		int ret=OneRoundFor3( jaccardHashCount,result,mPrev,hashPrev  ,jaccard3Assumps, scounts,solver);
		if(ret==-1){
			cout<<"delete solver";
			delete solver;
			cout<<"end delete";
			solver = new SATSolver((void*)&conf, &must_interrupt);
			this->solver=solver;
			solver_init();
			cout<<"end delete";

			continue;
		}
		std::ofstream  f;
		std::ostringstream filename("");
		filename<<"count_j"<<jaccardHashCount<<"_t"<<omp_get_thread_num();
		f.open(filename.str(),std::ofstream::out|std::ofstream::app);
		for(int j=0;j<3;++j)
		  scounts[j].summarize();
		for(int i=0;i<scounts[0].size()&& i<scounts[1].size()&& i<scounts[2].size();++i){
			f<<scounts[0].str(i)<<"\t"<<scounts[1].str(i)<<"\t"<<scounts[2].str(i)<<"\n";
		}
		//	f<<scount0.str()<<"\t"<<scount1.str()<<"\t"<<scount2.str()<<"\n";
		f.close();
		if(scounts[0].cellSolCount<=0){
			cout<<"cellSolCount<=0,cntinue";
			continue;
		}else{
			for(int j=0;j<2;++j){
				numHashList[jaccardHashCount].push_back(scounts[j].hashCount);
				numCountList[jaccardHashCount].push_back(scounts[j].cellSolCount);
			}
			numHashList[jaccardHashCount+1].push_back(scounts[2].hashCount);
			numCountList[jaccardHashCount+1].push_back(scounts[2].cellSolCount);

			break;
		}



		/*	cout<<"--------------------------"<<jaccardHashCount<<"\n"<<endl;
			for(int k=0;k<numCountList[jaccardHashCount].size();k++){
			cout<<"("<<numCountList[jaccardHashCount][k]<<"*2^"<< numHashList[jaccardHashCount][k]<<"),";
			}
			cout<<"\n";
			*/
		result->searched[jaccardHashCount-1]=true;
		/*vector<Lit> cl_that_removes;
		  cl_that_removes.push_back(Lit(act_var, false));
		  solver->add_clause(cl_that_removes);
		  */
	
		break;
	}
	cout<<"delete solver";
	delete solver;
	cout<<"end delete";
	solver = new SATSolver((void*)&conf, &must_interrupt);
	this->solver=solver;
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
solver_init();
	cout<<"end delete";
	//	cout<<"load to back, nVar="<<solver->nVars();
}


void CUSP::JaccardOneRound(uint64_t jaccardHashCount,JaccardResult* result ,bool computePrev,SATSolver* solver=NULL){
	if(solver==NULL)
	  solver=solver;
	map<uint64_t,vector<uint64_t>> &numHashList=result->numHashList;
	map<uint64_t,vector<int64_t>>& numCountList=result->numCountList;
	map<uint64_t,SATCount>& count=result->count;
	uint64_t &hashCount=result->hashCount[jaccardHashCount];
	map<uint64_t,Lit> jaccardHashVars;
	uint64_t mPrev = 0;
	vector<Lit >jaccardAssumps,jaccardAssumps_lastZero;
	int ret;
	while(true){
		jaccardAssumps.clear();
		jaccardAssumps_lastZero.clear();
		jaccardHashVars.clear();
		jaccardXorClause.clear();
		solver->simplify(&jaccardAssumps);
		if(jaccardHashCount>0){	
			SetJaccardHash(jaccardHashCount,jaccardHashVars,jaccardAssumps,jaccardAssumps_lastZero,solver);
		}
	//	solver->simplify(&jaccardAssumps);
		uint64_t hashPrev = 0;
		addKey2Map(jaccardHashCount,numHashList,numCountList,count);
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash

		//	int64_t currentNumSolutions_lastZero = BoundedSATCount(pivotApproxMC+1,assumps,jaccardAssumps_lastZero);
		SATCount scount0,scount1,scount2;
		JaccardResult result0,result1;
		ret=OneRoundCount( jaccardHashCount, result,mPrev,hashPrev, jaccardAssumps, scount0,solver);
		if(ret<0){
			continue;
		}
		if(scount0.cellSolCount<=0){
			continue;
		}

		result->searched[jaccardHashCount]=true;
		ret=OneRoundCount(jaccardHashCount, result,mPrev,hashPrev, jaccardAssumps_lastZero,scount1,solver);
		if(scount1.cellSolCount<=0){
			continue;
		}
		if(ret<0){
			continue;
		}
		numHashList[jaccardHashCount].push_back(scount0.hashCount);
		numCountList[jaccardHashCount].push_back(scount0.cellSolCount);

		//if(scount1.cellSolCount>0){
		numHashList[jaccardHashCount].push_back(scount1.hashCount);
		numCountList[jaccardHashCount].push_back(scount1.cellSolCount);
		//}
		if(computePrev){
			addKey2Map(jaccardHashCount-1,numHashList,numCountList,count);
			jaccardAssumps_lastZero.pop_back();
			int trys=0;
			while(true){
				trys++;
				OneRoundCount( jaccardHashCount-1, result,mPrev,hashPrev, jaccardAssumps_lastZero, scount2,solver);
				if(scount2.cellSolCount<=0){
					if(trys>1){
						break;
					}

					continue;
				}
				//	if(scount2.cellSolCount>0){
				numCountList[jaccardHashCount-1].push_back(scount2.cellSolCount);
				numHashList[jaccardHashCount-1].push_back(scount2.hashCount);
				break;
				//	}
			}
		}
		if(scount2.cellSolCount<=0){
			continue;
		}
		std::ofstream  f;
		std::ostringstream filename("");
		filename<<"count_j"<<jaccardHashCount<<"_t"<<omp_get_thread_num();
		f.open(filename.str(),std::ofstream::out|std::ofstream::app);
		for(int i=0;i<scount0.size()&& i<scount1.size()&& i<scount2.size();++i){
			f<<scount0.str(i)<<"\t"<<scount1.str(i)<<"\t"<<scount2.str(i)<<"\n";
		}
		f<<scount0.str()<<"\t"<<scount1.str()<<"\t"<<scount2.str()<<"\n";
		f.close();


		/*	cout<<"--------------------------"<<jaccardHashCount<<"\n"<<endl;
			for(int k=0;k<numCountList[jaccardHashCount].size();k++){
			cout<<"("<<numCountList[jaccardHashCount][k]<<"*2^"<< numHashList[jaccardHashCount][k]<<"),";
			}
			cout<<"\n";
			*/
		result->searched[jaccardHashCount-1]=true;
		/*vector<Lit> cl_that_removes;
		  cl_that_removes.push_back(Lit(act_var, false));
		  solver->add_clause(cl_that_removes);
		  */
	
		break;
	}
	cout<<"delete solver";
	delete solver;
	cout<<"end delete";
	solver = new SATSolver((void*)&conf, &must_interrupt);
	this->solver=solver;
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	solver_init();
	cout<<"end delete";
	//	cout<<"load to back, nVar="<<solver->nVars();
}
void CUSP::computeCountFromList(uint64_t jaccardHashCount, map<uint64_t,vector<uint64_t>> &numHashList,map<uint64_t,vector<int64_t>>& numCountList,map<uint64_t,SATCount>& count){
	if (numHashList[jaccardHashCount].size() == 0) {
		count[jaccardHashCount].cellSolCount = 0;
		count[jaccardHashCount].hashCount = 0;
	}else{
		std::ofstream  f;
		std::ostringstream filename("");
		filename<<"count_j"<<jaccardHashCount<<"_t"<<omp_get_thread_num();
	//	f.open(filename.str(),std::ofstream::out|std::ofstream::app);
		auto minHash = findMin(numHashList[jaccardHashCount]);
		vector<int64_t> numCountL=numCountList[jaccardHashCount];
		vector<uint64_t> numHashL=numHashList[jaccardHashCount];
		auto cnt_it = numCountL.begin();
		for (auto hash_it = numHashL.begin()
					; hash_it != numHashL.end() && cnt_it != numCountL.end()
					; hash_it++, cnt_it++
			) {
		//	f<<*cnt_it<<"\t2^"<<*hash_it<<"\n";
			*cnt_it *= pow(2, (*hash_it) - minHash);
		}
	//	f.close();
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
void * CUSP::JaccardOneThread(){
/*	JaccardPara * jaccardPara=para;
	int loop=para->loop;
	uint64_t jaccardHashCount=jaccardPara->jaccardHashCount;
	uint64_t hashCount =jaccardPara->id+jaccardPara->hashCount; //different thread try different hash count
	bool computePrev=jaccardPara->computePrev;
	int retryJaccardSingle=0;
	SATSolver* solver=solvers[jaccardPara->id];
	JaccardPara * result=new JaccardPara();

	for(int i=0;i<loop;++i){
		while(true){
			JaccardOneRound(jaccardHashCount,&result,computePrev,solver);
			pthread_mutex_lock(jaccardPara->hashCount_lock);
			jaccardPara->hashCount=max(hashCount,jaccardPara->hashCount);
			pthread_mutex_unlock(jaccardPara->hashCount_lock);
			computeCountFromList(jaccardHashCount,numHashList,numCountList,count);
			if(count[singleIndex].cellSolCount>0)
			  break;
			cout<<"====0 retry singleIndex"<<endl;
			if(retryJaccardSingle>5){
				retryJaccardSingle=0;
				singleIndex--;
			}
			retryJaccardSingle++;
		}
	}

	return (void*)result;*/
	return NULL;
}

bool CUSP::JaccardApproxMC(map<uint64_t,SATCount>& count)
{
	count.clear();
	int64_t currentNumSolutions = 0;
	map<uint64_t,vector<uint64_t>> numHashList;
	map<uint64_t,vector<int64_t>> numCountList;
	JaccardResult result;
	vector<Lit> assumps;
	vector<Lit >jaccardAssumps,jaccardAssumps_lastZero;
	uint64_t hashCount = startIteration;
	uint64_t hashPrev = 0;
	uint64_t mPrev = 0;
	uint64_t jaccardHashCount,jaccardPrev=0;
	if(singleIndex<0)
	  singleIndex=jaccard_vars.size();
	jaccardHashCount=singleIndex;
	double myTime = cpuTimeTotal();

	//	cout<<"save_state to "<<conf.saved_state_file.c_str()<<endl;
	//	solver->save_state(conf.saved_state_file.c_str(), l_True);
	//	return true;

	int numCore=1;
	JaccardResult * results=new JaccardResult[numCore];
	for(int i=0;i<numCore;++i){
		for(int j=0;j<singleIndex;++j){
			results->hashCount[j]=0;
			results->searched[j]=false;
		}
	}
	if(trimOnly){
		trimVar(independent_vars);
		std::ofstream  ff;
		std::ostringstream filename("");
		filename<<"trimed.txt";
		ff.open(filename.str(),std::ofstream::out|std::ofstream::app);
		ff<<"c ind ";
		for(auto var : independent_vars){
			ff<<var<<" ";
		}
		ff.close();
		exit(0);
	}
	//trimVar(&jaccard_vars);
	for(unsigned j = 0; j < tJaccardMC; j++) {
		/*	if(j==0)	{
			JaccardOneRound(0,&results[id],false,solvers[id]);
			results[id].searched[0]=true;
			computeCountFromList(0,results[id].numHashList,results[id].numCountList,results[id].count);
			}*/
		cout<<"Jaccard count="<<j;
		int retryJaccardSingle=0;
		while(true){
			std::ofstream  f;
			std::ostringstream filename("");
			filename<<"info_j"<<singleIndex<<"_t"<<omp_get_thread_num();
			JaccardOneRoundFor3_slow(singleIndex,&results[0],true,solver);
			computeCountFromList(singleIndex,results[0].numHashList,results[0].numCountList,results[0].count);
			computeCountFromList(singleIndex-1,results[0].numHashList,results[0].numCountList,results[0].count);
			results[0].searched[singleIndex]=true;
			if(results[0].count[singleIndex].cellSolCount>0){
				cout<<"break";
				break;
			}
			cout<<"====0 retry singleIndex"<<endl;
			if(retryJaccardSingle>5){
				retryJaccardSingle=0;
				//	singleIndex--;
				j--;
				break;
			}
			retryJaccardSingle++;
		}
	}


	return true;
}


bool CUSP::ApproxMC(SATCount& count)
{
    count.clear();
    int64_t currentNumSolutions = 0;
    vector<uint64_t> numHashList;
    vector<int64_t> numCountList;
    vector<Lit> assumps;
    for (uint32_t j = 0; j < tApproxMC; j++) {
        uint64_t hashCount;
        uint32_t repeatTry = 0;
        for (hashCount = 0; hashCount < solver->nVars(); hashCount++) {
            cout << "-> Hash Count " << hashCount << endl;
            double myTime = cpuTimeTotal();
            currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,solver);

            //cout << currentNumSolutions << ", " << pivotApproxMC << endl;
            cusp_logf << "ApproxMC:" << searchMode << ":"
                      << j << ":" << hashCount << ":"
                      << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                      << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                      << currentNumSolutions << endl;
            //Timeout!
            if (currentNumSolutions < 0) {
                //Remove all hashes
                assumps.clear();

                if (repeatTry < 2) {    /* Retry up to twice more */
                    assert(hashCount > 0);
                    AddHash(hashCount, assumps,solver); //add new set of hashes
                    solver->simplify(&assumps);
                    hashCount --;
                    repeatTry += 1;
                    cout << "Timeout, try again -- " << repeatTry << endl;
                } else {
                    //this set of hashes does not work, go up
                    AddHash(hashCount + 1, assumps,solver);
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
            AddHash(1, assumps,solver);
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

void CUSP::reset_solver(){
	cout<<"delete solver";
	delete solver;
	cout<<"end delete";
	solver = new SATSolver((void*)&conf);
	this->solver=solver;
	solver_init();
}

void CUSP::solver_init(){
	solverToInterrupt = solver;
	if (dratf) {
		solver->set_drat(dratf, clause_ID_needed);
	}
	check_num_threads_sanity(num_threads);
	solver->set_num_threads(num_threads);
	if (sql == 1) {
		solver->set_mysql(sqlServer
					, sqlUser
					, sqlPass
					, sqlDatabase);
	} else if (sql == 2) {
		solver->set_sqlite(sqlite_filename);
	}

	solver->add_sql_tag("commandline", commandLine);
	solver->add_sql_tag("verbosity", lexical_cast<string>(conf.verbosity));
	solver->add_sql_tag("threads", lexical_cast<string>(num_threads));
	solver->add_sql_tag("version", solver->get_version());
	solver->add_sql_tag("SHA-revision", solver->get_version_sha1());
	solver->add_sql_tag("env", solver->get_compilation_env());
#ifdef __GNUC__
	solver->add_sql_tag("compiler", "gcc-" __VERSION__);
#else
							    solver->add_sql_tag("compiler", "non-gcc");
#endif
	if (unset_vars) {
		solver->set_greedy_undef();
	}
	vector<uint32_t> original_independent_vars=independent_vars;
	parseInAllFiles(solver);
	std::cout<<"finished parsing\n";
	if(original_independent_vars.size()>0)
	  independent_vars=original_independent_vars;
}
int CUSP::solve()
{
   /* conf.reconfigure_at = 0;
    conf.reconfigure_val = 15;
    conf.gaussconf.max_matrix_rows = 3000;
    conf.gaussconf.decision_until = 3000;
    conf.gaussconf.max_num_matrixes = 1;
    conf.gaussconf.min_matrix_rows = 5;
    conf.gaussconf.autodisable = false;
*/
    //set seed
    assert(vm.count("random"));
    unsigned int seed = vm["random"].as<unsigned int>();
	randomEngine.seed(seed);

	openLogFile();
	startTime = cpuTimeTotal();
	solver = new SATSolver((void*)&conf, &must_interrupt);
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


	originalPC_size=solver->get_Nclause();
	if (startIteration > independent_vars.size()) {
		cout << "ERROR: Manually-specified startIteration"
			"is larger than the size of the independent set.\n" << endl;
		return -1;
	}



#if PARALLEL	
	int cores=omp_get_num_procs();
	cout<<"max thread="<<cores;
	solvers.clear();
	for(int i=0;i<cores;i++){
		SATSolver* s=new SATSolver((void*)&conf, &must_interrupt);
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
	} else if (searchMode==1)
	{
		map<uint64_t,SATCount> solCounts;
		finished = JaccardApproxMC(solCounts);
		if (!finished) {
			cout << " (TIMED OUT)" << endl;
			return 0;
		}
		for(auto it=solCounts.begin();it!=solCounts.end();++it){
			cout <<it->first<< " of Number of solutions is: " << it->second.cellSolCount
				<< " x 2^" << it->second.hashCount << endl;
		}

		if (conf.verbosity) {
			solver->print_stats();
		}
	}else{
		finished = ScalApproxMC(solCount);
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
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
                  );
    #endif

    #ifndef USE_GAUSS
    std::cerr << "CUSP only makes any sese to run if you have configured with:" << endl
              << "*** cmake -DUSE_GAUSS=ON (.. or .)  ***" << endl
              << "Refusing to run. Please reconfigure and then re-compile." << endl;
    exit(-1);
    #else

    CUSP main(argc, argv);
    main.conf.verbStats = 1;
    main.parseCommandLine();
    return main.solve();
    #endif
}

void CUSP::call_after_parse()
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
bool  CUSP::genHashForAssump(vector<uint32_t> vars, uint32_t num_xor_cls,LitStr& assumps){
	int var_size=vars.size();
	jaccardXorRate=(jaccardXorRate>0.5)?0.5:jaccardXorRate;
	int original_size=assumps.randomBits_rhs.size();
	if(original_size<num_xor_cls){
		assumps.randomBits += GenerateRandomBits_prob((var_size ) *( num_xor_cls-original_size),jaccardXorRate);
		assumps.randomBits_rhs += GenerateRandomBits( num_xor_cls-original_size);
	}
}

bool  CUSP::genHashForJaccard( uint32_t num_xor_cls,vector<LitStr>& jaccardHash){
	int var_size=jaccard_vars.size();
	LitStr oneHash,anotherHash;
		genHashForAssump(jaccard_vars,num_xor_cls,oneHash);
		jaccardHash.push_back(oneHash);
	anotherHash.randomBits=oneHash.randomBits;
	anotherHash.randomBits_rhs=oneHash.randomBits_rhs;
	anotherHash.randomBits_rhs[num_xor_cls-1]=(oneHash.randomBits_rhs[num_xor_cls-1]=='1')?'0':'1';
	jaccardHash.push_back(anotherHash);
}
bool  CUSP::SetHashByString( uint32_t num_xor_cls,vector<uint32_t> input_vars,const string randomBits,const string randomBits_rhs,  SATSolver* solver){
	int var_size=input_vars.size();
	if(randomBits.size()==0){
		assert(0);
	}
	bool rhs = true;
	vector<uint32_t> vars;
	for (uint32_t i = 0; i < num_xor_cls; i++) {
		//new activation variable
	//	solver->new_var();
	//	uint32_t act_var = solver->nVars()-1;
	//	assumps.push_back(Lit(act_var, true));
		vars.clear();
	//	vars.push_back(act_var);
		rhs = (randomBits_rhs[i]== '1');
		//		cout<<"x ";
		for (uint32_t k = 0; k < var_size; k++) {
			if (randomBits[var_size * i + k] == '1') {
				vars.push_back(input_vars[k]);
			}
		}
		solver->add_xor_clause(vars, rhs);
		if (conf.verbosity||printXor ) {
			std::cout<<"printXor=";
			print_xor(vars, rhs);
		}

	}
	return true;

}
void printVars(vector<Lit>& vars){
	std::stringstream ss;
	for(auto cl: vars) {
		ss << cl << " ";
	}
	std::cout<<"added clause=" <<ss.str()<<"\n";

}
void CUSP::SetSampledJaccardHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars,vector<vector<Lit>>& assumps,SATSolver* solver ){
	string sampleOne;
	size_t size= jaccard_vars.size();
	int sampleSize=1<<(jaccard_vars.size()-clausNum);
	sampleSize;
	while(jaccard_samples.size()<sampleSize*2){
			sampleOne=GenerateRandomBits_prob(size,0.5);
			jaccard_samples.insert(sampleOne);
	}
	std::set<string>::iterator sampleit=jaccard_samples.begin();
	for(int t=0;t<2;++t){
		sampleOne=*sampleit;
		solver->new_var();
		uint32_t act_var = solver->nVars()-1;
		assumps[t].push_back(Lit(act_var,false));
		assumps[2].push_back(Lit(act_var,false));
		vector<Lit> orVars;
		orVars.push_back(Lit(act_var,true));
		for(int i=0;i<sampleSize;++i){
			sampleOne=*sampleit;
			vector<Lit> vars;
			solver->new_var();
			uint32_t sol_var = solver->nVars()-1;
			vars.push_back(Lit(sol_var,true));
			vars.push_back(Lit(act_var,true));
			orVars.push_back(Lit(sol_var,false));
			for(int j=0;j<size;++j){
				vars.push_back(Lit(jaccard_vars[j],sampleOne[j]=='1'));
				printVars(vars);	
				solver->add_clause(vars);
				vars.pop_back();
			}
			sampleit++;
		}

		printVars(orVars);	
		solver->add_clause(orVars);
	}

}
bool  CUSP::AddJaccardHash( uint32_t num_xor_cls,vector<Lit>& assumps,vector<XorClause>& jaccardXorClause, SATSolver* solver){
	int var_size=jaccard_vars.size();
	jaccardXorRate=(jaccardXorRate>0.5)?0.5:jaccardXorRate;

	string randomBits = GenerateRandomBits_prob((var_size ) * num_xor_cls,jaccardXorRate);
	string randomBits_rhs = GenerateRandomBits( num_xor_cls);
	bool rhs = true;
	vector<uint32_t> vars;
	for (uint32_t i = 0; i < num_xor_cls; i++) {
		//new activation variable
		solver->new_var();
		uint32_t act_var = solver->nVars()-1;
		assumps.push_back(Lit(act_var, true));
		vars.clear();
		vars.push_back(act_var);
		rhs = (randomBits_rhs[i]== '1');
		//		cout<<"x ";
		for (uint32_t k = 0; k < var_size; k++) {
			if (randomBits[var_size * i + k] == '1') {
				vars.push_back(jaccard_vars[k]);
				//	cout<<jaccard_vars[j]<<" ";
			}
		}
		/*		if(rhs){
				cout<<act_var<<" 0"<<endl;
				}else{
				cout<<"-"<<act_var<<" 0"<<endl;
				}
				*/
		solver->add_xor_clause(vars, rhs);
		if (conf.verbosity||printXor ) {
			print_xor(vars, rhs);
		}
		XorClause xc(vars, rhs);
		jaccardXorClause.push_back(xc);

	}
	return true;

}

void CUSP::SetJaccardHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars,vector<Lit>& assumps,vector<Lit>& assumps2,SATSolver* solver )
{
	double originaljaccardXorRate=jaccardXorRate;
	if (jaccard_vars.size()/clausNum<2){
		jaccardXorRate=(float)(0.2*jaccard_vars.size()/clausNum);
	}
	jaccardXorRate=(jaccardXorRate<0.5)?jaccardXorRate:0.5;
	//if (conf.verbosity)
	std::cout<<"jaccardxorrate="<<jaccardXorRate<<"\n";
	if (clausNum < assumps.size()) {
		uint64_t numberToRemove = assumps.size()- clausNum;
		for (uint64_t i = 0; i<numberToRemove; i++) {
			assumps.pop_back();
		}
	} else {
		if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
			for (uint32_t i = assumps.size(); i< hashVars.size() && i < clausNum; i++) {
				assumps.push_back(hashVars[i]);
			}
		}
		if (clausNum > hashVars.size()) {
			AddJaccardHash(clausNum-hashVars.size(),assumps,jaccardXorClause,solver);
			for (uint64_t i = hashVars.size(); i < clausNum; i++) {
				hashVars[i] = assumps[i];
			}
		}
	}
	assumps2=assumps;
	uint32_t x =(assumps2[clausNum-1].toInt()-1)/2;
	assumps2[clausNum-1]=Lit(x, false);
	jaccardXorRate=originaljaccardXorRate;
}

//For ScalApproxMC only
void CUSP::SetHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, vector<Lit>& assumps,SATSolver* solver)
{
	double ratio=0.5;
	int parity=Parity;
	int var_size=independent_vars.size();
	if(parity<=1){
		if(clausNum*var_size>(XorMax)){//don't allow too many xor
			ratio=(1.0*XorMax)/(clausNum*var_size);
			//ratio=(ratio<XorRate)?XorRate:0.5;
			if(ratio<0.1){
				std::cerr<<"too low ratio... too many xor"<<ratio<<"num_xor_cls="<<clausNum<<"var_size="<<var_size<<"jaccardXorMax"<<jaccardXorMax;
			}
		}
	}else if(parity<var_size/2)
	  ratio=(double)(parity)/var_size;
	xorRate=(ratio>0.5)?0.5:ratio;
	std::cout<<"xor ratio="<<ratio;

    if (clausNum < assumps.size()) {
        uint64_t numberToRemove = assumps.size()- clausNum;
        for (uint64_t i = 0; i<numberToRemove; i++) {
            assumps.pop_back();
        }
    } else {
        if (clausNum > assumps.size() && assumps.size() < hashVars.size()) {
            for (uint32_t i = assumps.size(); i< hashVars.size() && i < clausNum; i++) {
                assumps.push_back(hashVars[i]);
            }
        }
        if (clausNum > hashVars.size()) {
            AddHash(clausNum-hashVars.size(),assumps,solver);
            for (uint64_t i = hashVars.size(); i < clausNum; i++) {
                hashVars[i] = assumps[i];
            }
        }
    }
}
//For ScalApproxMC only
bool CUSP::ScalApproxMC(SATCount& count)
{
    count.clear();
    vector<uint64_t> numHashList;
    vector<int64_t> numCountList;


    uint64_t hashCount = startIteration;
    uint64_t hashPrev = 0;
    uint64_t mPrev = 0;

    double myTime = cpuTimeTotal();
    if (hashCount == 0) {
		vector<Lit> assumps;
        int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC+1,assumps,solver);
        cusp_logf << "ApproxMC:"<< searchMode<<":"<<"0:0:"
                  << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                  << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                  << currentNumSolutions << endl;

        //Din't find at least pivotApproxMC+1
        if (currentNumSolutions <= pivotApproxMC) {
            count.cellSolCount = currentNumSolutions;
            count.hashCount = 0;
            return true;
        }
        hashCount++;
	}
	for (uint32_t j = 0; j < 1; j++) {

		vector<Lit> assumps;
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash
		uint32_t repeatTry = 0;
		uint64_t numExplored = 1;
        uint64_t lowerFib = 0, upperFib = independent_vars.size();

        while (numExplored < independent_vars.size()) {
            cout << "Num Explored: " << numExplored
                 << " ind set size: " << independent_vars.size() << endl;
            myTime = cpuTimeTotal();
            uint64_t swapVar = hashCount;

				cout<<"start setting hash"<<hashCount<<"hashVar="<<hashVars.size()<<"assumps"<<assumps.size()<<endl;
            SetHash(hashCount,hashVars,assumps,solver);
            cout << "Number of XOR hashes active: " << hashCount << endl;
            int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,solver);

         //   cout << currentNumSolutions << ", " << pivotApproxMC << endl;
            cusp_logf << "ApproxMC:" << searchMode<<":"
                      << j << ":" << hashCount << ":"
                      << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                      << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                      << currentNumSolutions << endl;
            //Timeout!
            if (currentNumSolutions < 0) {
                //Remove all hashes
                assumps.clear();
                hashVars.clear();

                if (repeatTry < 2) {    /* Retry up to twice more */
                    assert(hashCount > 0);
                    SetHash(hashCount,hashVars,assumps,solver);
                    solver->simplify(&assumps);
                    hashCount --;
                    repeatTry += 1;
                    cout << "Timeout, try again -- " << repeatTry << endl;
                } else {
                    //this set of hashes does not work, go up
                    SetHash(hashCount + 1, hashVars, assumps,solver);
                    solver->simplify(&assumps);
                    cout << "Timeout, moving up" << endl;
                }
                hashCount = swapVar;
                continue;
            }

            if (currentNumSolutions < pivotApproxMC + 1) {
                numExplored = lowerFib+independent_vars.size()-hashCount;
                if (succRecord.find(hashCount-1) != succRecord.end()
                    && succRecord[hashCount-1] == 1
                ) {
                    numHashList.push_back(hashCount);
                    numCountList.push_back(currentNumSolutions);
                    mPrev = hashCount;
                    //less than pivotApproxMC solutions
                    break;
                }
                succRecord[hashCount] = 0;
                countRecord[hashCount] = currentNumSolutions;
                if (abs(hashCount-mPrev) <= 2 && mPrev != 0) {
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
                    hashCount = (upperFib+lowerFib)/2;
                }
            } else {
                assert(currentNumSolutions == pivotApproxMC+1);

                numExplored = hashCount + independent_vars.size()-upperFib;
                if (succRecord.find(hashCount+1) != succRecord.end()
                    && succRecord[hashCount+1] == 0
                ) {
                    numHashList.push_back(hashCount+1);
                    numCountList.push_back(countRecord[hashCount+1]);
                    mPrev = hashCount+1;
                    break;
                }
                succRecord[hashCount] = 1;
                if (abs(hashCount - mPrev) < 2 && mPrev!=0) {
                    lowerFib = hashCount;
                    hashCount ++;
                } else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
                    lowerFib = hashCount;
                    hashCount = (lowerFib+upperFib)/2;
                } else {
                    //printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
                    hashCount = lowerFib + (hashCount -lowerFib)*2;
                }
            }
            hashPrev = swapVar;
        }
        assumps.clear();
		solver->simplify(&assumps);
		hashCount =mPrev;
	}
	for (uint32_t j = 0; j < tApproxMC; j++) {
		vector<Lit> assumps;
		map<uint64_t,int64_t> countRecord;
		map<uint64_t,uint32_t> succRecord;
		map<uint64_t,Lit> hashVars; //map assumption var to XOR hash
		uint32_t repeatTry = 0;
		uint64_t numExplored = 1;
		uint64_t lowerFib = 0, upperFib = independent_vars.size();

		while (numExplored < independent_vars.size()) {
            cout << "Num Explored: " << numExplored
                 << " ind set size: " << independent_vars.size() << endl;
            myTime = cpuTimeTotal();
            uint64_t swapVar = hashCount;

			cout<<"start setting hash"<<hashCount<<"hashVar="<<hashVars.size()<<"assumps"<<assumps.size()<<endl;
            SetHash(hashCount,hashVars,assumps,solver);
            cout << "Number of XOR hashes active: " << hashCount << endl;
            int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,solver);

            cout << currentNumSolutions << ", " << pivotApproxMC << endl;
            cusp_logf << "ApproxMC:" << searchMode<<":"
                      << j << ":" << hashCount << ":"
                      << std::fixed << std::setprecision(2) << (cpuTimeTotal() - myTime) << ":"
                      << (int)(currentNumSolutions == (pivotApproxMC + 1)) << ":"
                      << currentNumSolutions << endl;
            //Timeout!
            if (currentNumSolutions < 0) {
                //Remove all hashes
                assumps.clear();
                hashVars.clear();
                if (repeatTry < 2) {    /* Retry up to twice more */
                    assert(hashCount > 0);
                    SetHash(hashCount,hashVars,assumps,solver);
                    solver->simplify(&assumps);
                    hashCount --;
					
                    repeatTry += 1;
                    cout << "Timeout, try again -- " << repeatTry << endl;
                } else {
                    //this set of hashes does not work, go up
                    SetHash(hashCount + 1, hashVars, assumps,solver);
                    solver->simplify(&assumps);
                    cout << "Timeout, moving up" << endl;
                }
                hashCount = swapVar;
                continue;
            }

            if (currentNumSolutions < pivotApproxMC + 1) {
                numExplored = lowerFib+independent_vars.size()-hashCount;
                if (succRecord.find(hashCount-1) != succRecord.end()
                    && succRecord[hashCount-1] == 1
                ) {
                    numHashList.push_back(hashCount);
                    numCountList.push_back(currentNumSolutions);
                    mPrev = hashCount;
                    //less than pivotApproxMC solutions
                    break;
                }
                succRecord[hashCount] = 0;
                countRecord[hashCount] = currentNumSolutions;
                if (abs(hashCount-mPrev) <= 2 && mPrev != 0) {
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
                    hashCount = (upperFib+lowerFib)/2;
                }
            } else {
                assert(currentNumSolutions == pivotApproxMC+1);

                numExplored = hashCount + independent_vars.size()-upperFib;
                if (succRecord.find(hashCount+1) != succRecord.end()
                    && succRecord[hashCount+1] == 0
                ) {
                    numHashList.push_back(hashCount+1);
                    numCountList.push_back(countRecord[hashCount+1]);
                    mPrev = hashCount+1;
                    break;
                }
                succRecord[hashCount] = 1;
                if (abs(hashCount - mPrev) < 2 && mPrev!=0) {
                    lowerFib = hashCount;
                    hashCount ++;
                } else if (lowerFib + (hashCount - lowerFib)*2 >= upperFib-1) {
                    lowerFib = hashCount;
                    hashCount = (lowerFib+upperFib)/2;
                } else {
                    //printf("hashPrev:%d hashCount:%d\n",hashPrev, hashCount);
                    hashCount = lowerFib + (hashCount -lowerFib)*2;
                }
            }
            hashPrev = swapVar;
        }
        assumps.clear();
        solver->simplify(&assumps);
		hashCount =mPrev;
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
        *cnt_it *= pow(2, (*hash_it) - minHash);
    }
    int medSolCount = findMedian(numCountList);

    count.cellSolCount = medSolCount;
    count.hashCount = minHash;
    return true;
}