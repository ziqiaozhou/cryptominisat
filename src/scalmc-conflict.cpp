/*
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
#include <set>
#include <fstream>
#include <sys/stat.h>
#include <string.h>
#include <list>
#include <vector>
#include<omp.h>
#include<pthread.h>
#include "scalmc.h"
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


	("JaccardXorRate", po::value(&jaccardXorRate)->default_value(jaccardXorRate)
	 ,"default =1(0-1), sparse xor can speed up, but may lose precision.VarXorRate * jaccard_size() ")

    ("tApproxMC", po::value(&tApproxMC)->default_value(tApproxMC)
        , "Number of measurements")
  ("tJaccardMC", po::value(&tJaccardMC)->default_value(tJaccardMC)
        , "Number of measurements for jaccard hash")
    ("startIteration", po::value(&startIteration)->default_value(startIteration), "")

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
    cout << "Added XOR ";
    for (size_t i = 0; i < vars.size(); i++) {
        cout << vars[i]+1;
        if (i < vars.size()-1) {
            cout << " + ";
        }
    }
    cout << " = " << (rhs ? "True" : "False") << endl;
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
	int parity=Parity;
	int var_size=independent_vars.size();
	double ratio=0.5;
	if(parity<=1){
		if(num_xor_cls*var_size>(jaccardXorMax)){//don't allow too many xor
			ratio=(1.0*jaccardXorMax)/(num_xor_cls*var_size);
			ratio=(ratio<jaccardXorRate)?ratio:jaccardXorRate;
			if(ratio<0.1){
				std::cerr<<"too low ratio... too many xor"<<ratio;
			}
		}
	}else if(parity<var_size/2)
	  ratio=(double)(parity)/var_size;
	std::cout<<"xor ratio="<<ratio;

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
		rhs = (randomBits_rhs[i] == 1);
		for (uint32_t j = 0; j < independent_vars.size(); j++) {
			if(randomBits[i*independent_vars.size()+j]=='1')    
			  vars.push_back(independent_vars[j]);
	}
	solver->add_xor_clause(vars, rhs);
	if (conf.verbosity) {
		print_xor(vars, rhs);
	}
}
return true;
}

void CUSP::trimVar(vector<uint32_t>*vars){
	for(int i=0;i<vars->size();++i){
		uint32_t var=(*vars)[i];
		vector<Lit>assume;
		assume.push_back(Lit(var,true));
		lbool ret0=solver->solve(&assume);
		assume.clear();
		assume.push_back(Lit(var,false));
		lbool ret1=solver->solve(&assume);
		if(ret0!=ret1){
			vars->erase(vars->begin()+i);
			if (conf.verbosity )
			  std::cout<<"delete "<<var<<"\n";
			i--;
		}		
	}

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
			for (const uint32_t var: independent_vars) {
				if (solver->get_model()[var] != l_Undef) {
					lits.push_back(Lit(var, solver->get_model()[var] == l_True));
				} else {
					num_undef++;
				}
			}
			solver->add_clause(lits);
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
        return -1;
    }
    return solutions;
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
		solver->set_timeout_all_calls(this_iter_timeout);
		ret = solver->solve(&new_assumps);
		if(firstRound){
			for (const uint32_t i: dependent_vars) {
				vector<Lit> Eqlits;
				bool value=(rand()%2==1);
				Eqlits.push_back(Lit(act_var,false));
				Eqlits.push_back(Lit(i,solver->get_model()[i]==l_False));
				solver->add_clause(Eqlits);
				nAddedClause++;
			}
			firstRound=false;
		}

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
        return -1;
    }
	return solutions;
}

int CUSP::OneRound(uint64_t jaccardHashCount,JaccardResult* result, uint64_t &mPrev,uint64_t &hashPrev  ,vector<Lit> jaccardAssumps,vector<SATCount>& scounts,SATSolver * solver=NULL)
{
	//	solver->simplify(&jaccardAssumps);
	uint64_t& hashCount=result->hashCount[jaccardHashCount];
	bool& searched=result->searched[jaccardHashCount];
	vector<Lit> assumps;
	double myTime = cpuTimeTotal();
	SATCount count1,count2,count3;
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
			int64_t s[3];
			int64_t currentNumSolutions = BoundedSATCount(pivotApproxMC + 1, assumps,jaccardAssumps,solver);
			s[0]=currentNumSolutions;
			double currTime=cpuTimeTotal()-myTime;
			cout << "Num Explored: " << numExplored
				<<"solver->nvar()="<<solver->nVars()
				<< "Number of XOR hashes active: " << hashCount<<",jaccard="<<jaccardHashCount << endl
				<< currentNumSolutions << ", " << pivotApproxMC
				<<",time="<<(cpuTimeTotal() - myTime) <<endl;
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
						s[1] = BoundedSATCount(pivotApproxMC*2-1, assumps,jaccardAssumps[1],solver);
						if(s[1]<=0||s[1]>pivotApproxMC*2){
							//unbalanced sampling, giveup
resample:
							assumps.clear();
							hashVars.clear();
							solver->simplify(&assumps);
							continue;
						}
						s[2]= BoundedSATCount(s2[1]+s[0],assumps,jaccardAssumps[2],solver);
						if(s[2]<=0|| s[2]>(s[1]+s[0])){
							//impossible reach
							assert(0);
							goto resample;
						}
						for(int k=0;k<scounts.size();++k)
						{
							scounts[k].numHashList.push_back(hashCount);
							scounts[k].numCountList.push_back(s[k])
						}
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
	}
	cout<<"thread:"<<omp_get_thread_num()<<",Avg["<<jaccardIndex<<"]="<<count.cellSolCount<<"*2^"<<count.hashCount<<endl;
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
		ret=OneRoundCount( jaccardHashCount, result,mPrev,hashPrev, jaccardAssumps_lastZero,scount1,solver);
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
	//solver->log_to_file("mydump.cnf");
	//check_num_threads_sanity(num_threads);
	if (unset_vars) {
		solver->set_greedy_undef();
	}
	parseInAllFiles(solver);
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

#if PARALLEL==1 
		pthread_t threads[NUM_THREADS];
		pthread_mutex_lock hashCount_lock;
		pthread_mutex_init(&hashCount_lock,NULL);
		for(int i=0;i<NUM_THREADS;++i){
			JaccardPara jaccardPara;
			jaccardPara.index=singleIndex;
			/*	jaccardPara.numHashList=&numHashList;
				jaccardPara.numCountList=&numCountList;
				jaccardPara.cout=&count;
				*/	
			jaccardPara.hashCount=&hashCount;
			jaccardPara.computePrev=false;
			jaccardPara->id=i;
			pthread_create(&threads[i],NULL,JaccardOneThread,&Jaccardpara);
		}
#elif PARALLEL==2
		int numCore=omp_get_max_threads();
		JaccardResult * results=new JaccardResult[numCore];
		for(int i=0;i<numCore;++i){
			for(int j=0;j<singleIndex;++j){
				results->hashCount[j]=0;
				results->searched[j]=false;
			}
		}
		//warn up
		SATCount warmcount;
		//solver=solvers[omp_get_thread_num()];
		map<uint64_t,Lit> jaccardHashVars;
		jaccardAssumps.clear();
		jaccardAssumps_lastZero.clear();
		jaccardHashVars.clear();
		jaccardXorClause.clear();
		solver->simplify(&jaccardAssumps);
		if(jaccardHashCount>0){	
			SetJaccardHash(jaccardHashCount,jaccardHashVars,jaccardAssumps,jaccardAssumps_lastZero,solver);
		}
		cout<<"jaccard index="<<jaccardHashCount<<"\n";
		solver->add_clause(jaccardAssumps);
		int tApproxMC0=tApproxMC;
		tApproxMC=1;
		ScalApproxMC(warmcount);
		cout<<"end of warmup";
//		delete solver;
//		solver = new SATSolver((void*)&conf, &must_interrupt);
//		solvers[omp_get_thread_num()]=solver;
		//solver->log_to_file("mydump.cnf");
		//check_num_threads_sanity(num_threads);
//		if (unset_vars) {
//			solver->set_greedy_undef();
//		}
//		parseInAllFiles(solver);
		//after warm up
		tApproxMC=tApproxMC0;
		for(int i=0;i<numCore;++i){
			for(int j=singleIndex-1;j<singleIndex+1;++j){
				if(warmcount.cellSolCount>pivotApproxMC)
				  results->hashCount[j]=log2(warmcount.cellSolCount/pivotApproxMC+1)+warmcount.hashCount;
				else
				  results->hashCount[j]=warmcount.hashCount;
				results->searched[j]=true;
			}
		}

#pragma omp parallel for
		for(unsigned j = 0; j < tJaccardMC; j++) {
			int id=omp_get_thread_num();
			/*	if(j==0)	{
				JaccardOneRound(0,&results[id],false,solvers[id]);
				results[id].searched[0]=true;
				computeCountFromList(0,results[id].numHashList,results[id].numCountList,results[id].count);
				}*/
			int retryJaccardSingle=0;
			while(true){
				std::ofstream  f;
				std::ostringstream filename("");
				filename<<"info_j"<<singleIndex<<"_t"<<omp_get_thread_num();
				JaccardOneRound(singleIndex,&results[id],true,solvers[id]);
			//	computeCountFromList(singleIndex,results[id].numHashList,results[id].numCountList,results[id].count);
			//	computeCountFromList(singleIndex-1,results[id].numHashList,results[id].numCountList,results[id].count);
				results[id].searched[singleIndex]=true;
				if(results[id].count[singleIndex].cellSolCount>0){
					cout<<"break";
					break;
				}
				cout<<"====0 retry singleIndex"<<endl;
				if(retryJaccardSingle>5){
					retryJaccardSingle=0;
					singleIndex--;
					j--;
				}
				retryJaccardSingle++;
			}
		}
/*	uint64_t diff=log2(count[0].cellSolCount/count[singleIndex].cellSolCount)+count[0].hashCount- count[singleIndex].hashCount;
	if(diff<1)
	return true;
	cout<<"diff="<<diff<<endl;*/
#if 0
		hashCount=16;
		//		jaccardHashCount=singleIndex-diff;
		int originaltApproxMC=tApproxMC;
#pragma omp parallel for schedule(dynamic,16) 
		for(unsigned jaccardHashCount=10;jaccardHashCount<singleIndex/2+4;jaccardHashCount+=2){
			std::ofstream  f;
			std::ostringstream filename("");
			filename<<"info_j"<<jaccardHashCount<<"_t"<<omp_get_thread_num();
			f.open(filename.str(),std::ofstream::out|std::ofstream::app);

			f<<"changed jaccard index "<<jaccardHashCount<<endl;
			f.close();
			for (uint32_t j = 0; j < tApproxMC; ++j) {
				int id=omp_get_thread_num();
				uint32_t repeatTry = 0;
				jaccardAssumps.clear();
				bool prevComputed=false;
				uint32_t single_index=jaccard_vars.size();
				bool gotNonZeroConjunction=false;
				uint64_t lowerJaccard=1,upperJaccard= jaccard_vars.size(),prevJaccard=0;
				//map assumption var to XOR hash
				JaccardOneRound(jaccardHashCount,&results[id],false,solvers[id]);			
				//prevJaccard=jaccardHashCount;
				//computeCountFromList(jaccardHashCount,numHashList,numCountList,count);
				solvers[id]->simplify(&assumps);
				solvers[id]->simplify(&jaccardAssumps);
			}

			int id=omp_get_thread_num();
			computeCountFromList(jaccardHashCount,results[id].numHashList,results[id].numCountList,results[id].count);
		}
cout<<"======================start oganization\n";
		for(int id=0;id<numCore;++id){
			for(auto one : results[id].numHashList){
				if(numHashList.find(one.first)==numHashList.end()){
					vector<uint64_t> tmp;
					vector<int64_t> tmp2;
					numHashList[one.first]=tmp;
					numCountList[one.first]=tmp2;
				}
				numHashList[one.first].insert(numHashList[one.first].end(),one.second.begin(),one.second.end());
				numCountList[one.first].insert(numCountList[one.first].end(),results[id].numCountList[one.first].begin(),results[id].numCountList[one.first].end());
			}
		}
		computeCountFromList(jaccardHashCount,numHashList,numCountList,count);
cout<<"================end computation\n";
#endif
#else
		int numCore=1;
		JaccardResult * results=new JaccardResult[numCore];
		for(int i=0;i<numCore;++i){
			for(int j=0;j<singleIndex;++j){
				results->hashCount[j]=0;
				results->searched[j]=false;
			}
		}
		//warn up
			//solver->log_to_file("mydump.cnf");
		//check_num_threads_sanity(num_threads);
		//after warm up
		trimVar(&independent_vars);
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
				JaccardOneRound(singleIndex,&results[0],true,solver);
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

#endif

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
	if (dratf) {
		solver->set_drat(dratf, clause_ID_needed);
	}
//	check_num_threads_sanity(num_threads);
//	solver->set_num_threads(num_threads);
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
	printVersionInfo();
	parseInAllFiles(solver);

	originalPC_size=solver->get_Nclause();
	cout<<"original size="<<originalPC_size<<"\n";
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
		
	if(num_xor_cls==var_size)
	{
		vars.push_back(jaccard_vars[i]);
	}else{
		for (uint32_t k = 0; k < var_size; k++) {
			if (randomBits[var_size * i + k] == '1') {
				vars.push_back(jaccard_vars[k]);
				//	cout<<jaccard_vars[j]<<" ";
			}
		}
	}
		/*		if(rhs){
			cout<<act_var<<" 0"<<endl;
		}else{
		cout<<"-"<<act_var<<" 0"<<endl;
		}
*/
		solver->add_xor_clause(vars, rhs);
		if (conf.verbosity ) {
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
	jaccardXorRate=(jaccardXorRate<0.4)?jaccardXorRate:0.4;
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