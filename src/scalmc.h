/*
 * CUSP
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

#ifndef CUSP_H_
#define CUSP_H_

#include "main.h"
#include <fstream>
#include <random>
#include <map>
#include <array>
#include "cryptominisat5/cryptominisat.h"
#define PARALLEL 0
#define TIMEOUT -64
#define RETRY_IND_HASH -2
#define RETRY_JACCARD_HASH -1
#define NEAR_RESULT -4
#define GOT_RESULT_UPPER -16
#define GOT_RESULT_LOWER -32
#define TOO_MUCH -8
#define DEBUG_VAR_LEVEL 2

#define DEBUG_HASH_LEVEL 3
#define VAR_MESSAGE(s) if(debug>DEBUG_VAR_LEVEL)std::cout<<s;
class XorClause{
	public:
		std::vector<unsigned> vars;
		bool rhs;
		XorClause(std::vector<unsigned> vars0,bool rhs0){
			vars=vars0;
			rhs=rhs0;
		}
		~XorClause(){
			vars.clear();
		}
};

class SATCount {
	public:
		void summarize();
    void clear()
    {
        SATCount tmp;
        *this = tmp;
		numHashList.clear();
		numCountList.clear();
	}
	
	int size(){
		return numHashList.size();
	}
	std::string str(int i){
		std::ostringstream out("");
		if(i<numHashList.size())
		  out<<numCountList[i]<<"*2^"<<numHashList[i];
		return out.str();
	}
	std::string str(){
		std::ostringstream out("");
		out<<cellSolCount<<"*2^"<<hashCount;
		return out.str();
	}
	void pop_back(){
		numHashList.pop_back();
		numCountList.pop_back();
	}
	unsigned hashCount = 0;
	double cellSolCount = 0;

	vector<unsigned> numHashList;//for output
	vector<int> numCountList;//for outpur

};
class JaccardResult{
	public:
		std::map<unsigned,vector<unsigned>> numHashList;//for output
		std::map<unsigned,vector<int>> numCountList;//for outpur
		std::map<unsigned,SATCount> count;//for outpur
		std::map<unsigned,unsigned> hashCount;
		std::map<unsigned,bool> searched;
		JaccardResult(){
		};
		~JaccardResult(){
		};

};
struct JaccardPara{
	bool computePrev;
	unsigned jaccardHashCount;
	std::map<unsigned,vector<unsigned>> numHashList;//for output
	std::map<unsigned,vector<int>> numCountList;//for outpur
	std::map<unsigned,SATCount> count;//for outpur
	unsigned *hashCount;
	int loop;
	int id;
};
class CUSP: public Main {
	public:

	std::vector<CMSat::SATSolver*> solvers;
		int solve() override;
		void add_supported_options() override;

		po::options_description approxMCOptions;
		CUSP(int argc, char** argv):
			Main(argc, argv)
			, approxMCOptions("ApproxMC options")
	{
		must_interrupt.store(false, std::memory_order_relaxed);
	}

	private:

		std::set<std::string> cachedSolutions;
		std::vector<std::string> cachedSubSolutions[3];

		std::vector<std::string> cachedFullSolutions[3];
		std::vector<unsigned> independent_vars0;
		std::set<std::string> independent_samples;
		std::set<std::string> jaccard_samples;
		void add_approxmc_options();
		void solver_init();
		bool checkParity(int,string randomBits,int num_xor_cls,int size,int i,int j);
		bool JaccardApproxMC(std::map<unsigned,SATCount>& count);

		bool Jaccard2ApproxMC(std::map<unsigned,SATCount>& count);
		bool ScalApproxMC(SATCount& count);
		bool ApproxMC(SATCount& count);
		bool AddJaccardHash(unsigned num_xor_cls, vector<Lit>& assumps,std::vector<XorClause>&, CMSat::SATSolver* solver);
		bool  AddJaccard2Hash( unsigned num_xor_cls,std::vector<Lit>& assumps,CMSat::SATSolver* solver);
		bool AddHash(unsigned num_xor_cls, vector<Lit>& assumps,CMSat::SATSolver* solver);
		void SetHash(unsigned clausNum, std::map<unsigned,Lit>& hashVars, vector<Lit>& assumps,CMSat::SATSolver* solver);

		int SampledBoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps,SATSolver* solver);
		void SetSampledJaccardHash(unsigned clausNum, std::map<unsigned,Lit>& hashVars,vector<vector<Lit>>& assumps,SATSolver* solver );
		void cache_clear();
		void SetJaccardHash(unsigned clausNum, std::map<unsigned,Lit>& hashVars, vector<Lit>& assumps, vector<Lit>& assumps2, CMSat::SATSolver* solver);
		void SetJaccard2Hash(unsigned clausNum, std::map<unsigned,Lit>& hashVars, vector<Lit>& assumps, CMSat::SATSolver* solver);

		int BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps,int resultIndex,CMSat::SATSolver * solver);

		int BoundedSATCount_print(unsigned maxSolutions, const vector<Lit> assumps,CMSat::SATSolver * solver);
		int BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps,CMSat::SATSolver * solver);
		int OneRoundCount(unsigned jaccardHashCount,JaccardResult *result,unsigned & mPrev,unsigned& hashPrev,vector<Lit> jaccardAssumps,SATCount& count,CMSat::SATSolver* solver);

int OneRoundFor3_simple(unsigned jaccardHashCount,JaccardResult* result, unsigned &mPrev,unsigned &hashPrev  ,std::vector<std::vector<Lit>> jaccardAssumps,std::vector<std::pair<unsigned,unsigned>>& scounts,SATSolver * solver);
		int OneRoundFor3(unsigned jaccardHashCount,JaccardResult* result, unsigned &mPrev,unsigned &hashPrev  ,std::vector<std::vector<Lit>> jaccardAssumps,std::vector<SATCount>& scounts,SATSolver * solver);
		int OneRoundFor3NoHash(std::vector<std::vector<CMSat::Lit> >, std::vector<SATCount>&,int rindex, CMSat::SATSolver*);

		int OneRoundFor3WithHash(bool readyPrev,bool readyNext,std::set<std::string> nextCount,unsigned &hashCount,std::map<unsigned,Lit>& hashVars,vector<Lit>assumps ,std::vector<std::vector<Lit>> jaccardAssumps,vector<SATCount>& scounts,int rindex,SATSolver * solver);
		//int OneRoundFor3WithHash(bool readyPrev,bool readyNext,unsigned nextCount,unsigned &hashCount,std::map<unsigned,Lit>& hashVars,std::vector<Lit>assumps ,std::vector<std::vector<Lit>> jaccardAssumps,std::vector<SATCount>& scounts,SATSolver * solver);
		void JaccardOneRoundFor3(unsigned jaccardHashCount,JaccardResult* result ,bool computePrev,SATSolver* solver);

		void Jaccard2OneRoundFor3(unsigned jaccardHashCount,JaccardResult* result ,bool computePrev,SATSolver* solver);
		void Jaccard2OneRound(unsigned jaccardHashCount, JaccardResult* result,bool computePrev,CMSat::SATSolver* solver0);
		void JaccardOneRound(unsigned jaccardHashCount, JaccardResult* result,bool computePrev,CMSat::SATSolver* solver0);
		void* JaccardOneThread();
		void computeCountFromList(unsigned jaccardHashCount, std::map<unsigned,vector<unsigned>> &numHashList,std::map<unsigned,vector<int>>& numCountList,std::map<unsigned,SATCount>& count);
		void addKey2Map(unsigned jaccardHashCount,std::map<unsigned,vector<unsigned>> &numHashList,std::map<unsigned,vector<int>>& numCountList,std::map<unsigned,SATCount>& count);
		lbool BoundedSAT(
					unsigned maxSolutions, unsigned minSolutions
					, vector<Lit>& assumptions
					, std::map<std::string, unsigned> solutionMap
					, unsigned* solutionCount
					);
		string GenerateRandomBits(unsigned size);
		string GenerateRandomBits_prob(unsigned size,double prob);
		void trimVar(std::vector<unsigned>&);
		//config
		std::string cuspLogFile = "cusp_log.txt";
		unsigned singleIndex=0;
		double startTime;
		std::map< std::string, std::vector<unsigned>> globalSolutionMap;
		bool openLogFile();
		std::atomic<bool> must_interrupt;
		void call_after_parse() override;

		unsigned startIteration = 0;
		unsigned pivotApproxMC = 52;

		double tStdError = 0.05;
		double prevTime;
		unsigned endJaccardIndex = 0;

		int printXor=0;
		int trimOnly=0;
		int onlyOne=0;
		unsigned LowerFib = 0;
		unsigned UpperFib = 0;
		unsigned startHashCount=1;
		unsigned tApproxMC = 37;
		unsigned tJaccardMC = 100;
		unsigned searchMode = 1;
		double jaccardXorRate=0.5;
		double xorRate=0.5;
		std::vector<XorClause> jaccardXorClause;
		int jaccardXorMax=600;
		std::string specifiedOb;
		int XorMax=1000;
		bool Parallel=false;
		double   loopTimeout = 300;
		int      unset_vars = 1;
		int test_func=0;
		int Parity=1;
		int notSampled=0;
		int debug=0;
		int originalPC_size;
		std::ofstream cusp_logf;
		std::random_device random_dev;
		std::mt19937 randomEngine;
		int nCounterExamples=0;
		std::string outPrefix="";
};


#endif //CUSP_H_
