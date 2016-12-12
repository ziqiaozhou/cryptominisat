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
#define PARALLEL 2
struct SATCount {
    void clear()
    {
        SATCount tmp;
        *this = tmp;
    }
	std::string str(){
		std::ostringstream out("");
		out<<cellSolCount<<"*2^"<<hashCount;
		return out.str();
	}
    uint32_t hashCount = 0;
    double cellSolCount = 0;
};
class JaccardResult{
	public:
		std::map<uint64_t,vector<uint64_t>> numHashList;//for output
		std::map<uint64_t,vector<int64_t>> numCountList;//for outpur
		std::map<uint64_t,SATCount> count;//for outpur
		std::map<uint64_t,uint64_t> hashCount;
		std::map<uint64_t,bool> searched;
		JaccardResult(){
		};
		~JaccardResult(){
		};
};
struct JaccardPara{
	bool computePrev;
	uint64_t jaccardHashCount;
	std::map<uint64_t,vector<uint64_t>> numHashList;//for output
	std::map<uint64_t,vector<int64_t>> numCountList;//for outpur
	std::map<uint64_t,SATCount> count;//for outpur
	uint64_t *hashCount;
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
    void add_approxmc_options();

 bool checkParity(string randomBits,int num_xor_cls,int size,int i,int j);
	bool JaccardApproxMC(std::map<uint64_t,SATCount>& count);
	bool ScalApproxMC(SATCount& count);
	bool ApproxMC(SATCount& count);

	bool AddJaccardHash(uint32_t num_xor_cls, vector<Lit>& assumps, CMSat::SATSolver* solver);
	bool AddHash(uint32_t num_xor_cls, vector<Lit>& assumps,CMSat::SATSolver* solver);
	void SetHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, vector<Lit>& assumps,CMSat::SATSolver* solver);
	
	void SetJaccardHash(uint32_t clausNum, std::map<uint64_t,Lit>& hashVars, vector<Lit>& assumps, vector<Lit>& assumps2, CMSat::SATSolver* solver);
	int64_t BoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps, const vector<Lit>& jassumps,CMSat::SATSolver * solver);

	int64_t BoundedSATCount(uint32_t maxSolutions, const vector<Lit>& assumps,CMSat::SATSolver * solver);
	int OneRoundCount(uint64_t jaccardHashCount,JaccardResult *result,uint64_t & mPrev,uint64_t& hashPrev,vector<Lit>& jaccardAssumps,SATCount& count,CMSat::SATSolver* solver);
	void JaccardOneRound(uint64_t jaccardHashCount, JaccardResult* result,bool computePrev,CMSat::SATSolver* solver0);
void* JaccardOneThread();
	void computeCountFromList(uint64_t jaccardHashCount, std::map<uint64_t,vector<uint64_t>> &numHashList,std::map<uint64_t,vector<int64_t>>& numCountList,std::map<uint64_t,SATCount>& count);
	void addKey2Map(uint64_t jaccardHashCount,std::map<uint64_t,vector<uint64_t>> &numHashList,std::map<uint64_t,vector<int64_t>>& numCountList,std::map<uint64_t,SATCount>& count);
	lbool BoundedSAT(
				uint32_t maxSolutions, uint32_t minSolutions
				, vector<Lit>& assumptions
				, std::map<std::string, uint32_t>& solutionMap
				, uint32_t* solutionCount
				);
	string GenerateRandomBits(uint32_t size);

	//config
	std::string cuspLogFile = "cusp_log.txt";
	uint32_t singleIndex=0;
	double startTime;
	std::map< std::string, std::vector<uint32_t>> globalSolutionMap;
	bool openLogFile();
	std::atomic<bool> must_interrupt;
	void call_after_parse() override;

	uint32_t startIteration = 0;
	uint32_t pivotApproxMC = 52;
    double prevTime;
	uint32_t endJaccardIndex = 0;
	uint32_t tApproxMC = 37;
	uint32_t tJaccardMC = 16;
    uint32_t searchMode = 1;
	double jaccardXorRate=1;
	bool Parallel=false;
    double   loopTimeout = 300;
    int      unset_vars = 1;
	int parity=1;
	int originalPC_size;
    std::ofstream cusp_logf;
	std::random_device random_dev;
    std::mt19937 randomEngine;
};


#endif //CUSP_H_
