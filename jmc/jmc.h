/*
 * Jaccard Count Header
 */

#ifndef JACCARDMC_H_
#define JACCARDMC_H_

#include "src/main.h"
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

class XorClause
{
public:
    std::vector<unsigned> vars;
    bool rhs;

    XorClause(std::vector<unsigned> vars0, bool rhs0)
    {
        vars = vars0;
        rhs = rhs0;
    }

    ~XorClause()
    {
        vars.clear();
    }
};

class SATCount
{
public:
    void summarize();

    void clear()
    {
        SATCount tmp;
        *this = tmp;
        numHashList.clear();
        numCountList.clear();
    }

    int size()
    {
        return numHashList.size();
    }

    std::string str(int i)
    {
        std::ostringstream out("");
        if (i < (int) numHashList.size())
            out << numCountList[i] << "*2^" << numHashList[i];
        std::cout<<"str(count)="<<numCountList[i]<<"\n";
        return out.str();
    }

    std::string str()
    {
        std::ostringstream out("");
        out << cellSolCount << "*2^" << hashCount;
        return out.str();
    }

    void pop_back()
    {
        numHashList.pop_back();
        numCountList.pop_back();
    }
    unsigned hashCount = 0;
    double cellSolCount = 0;

    vector<unsigned> numHashList; //for output
    vector<double> numCountList; //for outpur

};

class JaccardResult
{
public:
    std::map< unsigned, vector<unsigned> > numHashList;
    std::map< unsigned, vector<double> > numCountList;
    std::map<unsigned, SATCount> count;
    std::map<unsigned, unsigned> hashCount;
    std::map<unsigned, bool> searched;

    JaccardResult()
    {
    };

    ~JaccardResult()
    {
    };

};

class JaccardMC : public Main
{
	private:
		/*
		vector<uint32_t> jaccard_vars;
		vector<uint32_t> jaccard_var2;
		std::vector<uint32_t> ob_vars2;
		std::vector<uint32_t> ob_vars;
		std::vector<uint32_t> attack_vars;*/
		std::string jaccard_vars_str = "";
		unsigned CountOnOut = 0;
		std::set<std::string> cachedSolutions;
		std::vector<std::string> cachedSubSolutions[3];
		std::vector<std::string> cachedFullSolutions[3];
		std::vector<uint32_t> independent_vars0;
	

		std::set<std::string> independent_samples;
		std::set<std::string> jaccard_samples;
		std::string logFileName = "cusp_log.txt";
		bool useWeight=false;
		unsigned singleIndex = 0;
		double startTime;
		std::map< std::string, std::vector<unsigned> > globalSolutionMap;
		bool openLogFile();
		std::atomic<bool> must_interrupt;
		string dFilename="";
		std::map<unsigned,float> distribution;
		double wsolution=0;
		void readDFile();
	public:

		std::vector<CMSat::SATSolver*> solvers;
		int solve() override;
		void add_supported_options() override;

		po::options_description approxMCOptions;

		JaccardMC(int argc, char** argv) :
			Main(argc, argv)
			, approxMCOptions("ApproxMC options")
	{
		must_interrupt.store(false, std::memory_order_relaxed);
		std::stringstream ss(jaccard_vars_str);
		uint32_t i;
		while (ss >> i)
		{
			const uint32_t var = i-1;
			jaccard_vars.push_back(var);

			if (ss.peek() == ',' || ss.peek() == ' ')
			  ss.ignore();
		}
	}

	private:

		void add_approxmc_options();
		void solver_init();
		bool JaccardApproxMC(std::map<unsigned, SATCount>& count);
		void setDiffOb();
		bool JaccardHatApproxMC(std::map<unsigned, SATCount>& count);
		bool ScalApproxMC(SATCount& count);
		bool ApproxMC(SATCount& count);
    bool SSetHashSample(unsigned num_xor_cls, vector<Lit>& assumps, std::vector<XorClause>&, CMSat::SATSolver* solver);
    bool SSetTwoHashSample(unsigned num_xor_cls, std::vector<Lit>& assumps, CMSat::SATSolver* solver);
    bool AddHash(unsigned num_xor_cls, vector<Lit>& assumps, CMSat::SATSolver* solver);
    void SetHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, CMSat::SATSolver* solver);
    int SampledBoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps, CMSat::SATSolver* solver);
    void SetSampledJaccardHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<vector<Lit>>&assumps, SATSolver* solver);
    void cache_clear();
    void SetJaccardHash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, vector<Lit>& assumps2, CMSat::SATSolver* solver);
    void SetJaccard2Hash(unsigned clausNum, std::map<unsigned, Lit>& hashVars, vector<Lit>& assumps, CMSat::SATSolver* solver);
void SetSampledJaccardHatHash(unsigned int, std::vector<std::vector<CMSat::Lit>>&, CMSat::SATSolver*);
    int BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, const vector<Lit> jassumps, int resultIndex, CMSat::SATSolver * solver);

    int BoundedSATCount_print(unsigned maxSolutions, const vector<Lit> assumps, CMSat::SATSolver * solver);
    int BoundedSATCount(unsigned maxSolutions, const vector<Lit> assumps, CMSat::SATSolver * solver);
    int OneRoundCount(unsigned jaccardHashCount, JaccardResult *result, unsigned & mPrev, unsigned& hashPrev, vector<Lit> jaccardAssumps, SATCount& count, CMSat::SATSolver* solver);

    int OneRoundForHatJ(unsigned jaccardHashCount, JaccardResult* result, unsigned &mPrev, unsigned &hashPrev, std::vector<std::vector<Lit>> jaccardAssumps, std::vector<std::pair<unsigned, double>>&scounts);
    int OneRoundFor3(unsigned jaccardHashCount, JaccardResult* result, unsigned &mPrev, unsigned &hashPrev, std::vector<std::vector<Lit>> jaccardAssumps, std::vector<SATCount>& scounts, SATSolver * solver);
    int OneRoundFor3NoHash(std::vector<std::vector<CMSat::Lit> >, std::vector<SATCount>&, int rindex, CMSat::SATSolver*);

    int OneRoundFor3WithHash(bool readyPrev, bool readyNext, std::set<std::string> nextCount, unsigned &hashCount, std::map<unsigned, Lit>& hashVars, vector<Lit>assumps, std::vector<std::vector<Lit>> jaccardAssumps, vector<SATCount>& scounts, int rindex, SATSolver * solver);
    //int OneRoundFor3WithHash(bool readyPrev,bool readyNext,unsigned nextCount,unsigned &hashCount,std::map<unsigned,Lit>& hashVars,std::vector<Lit>assumps ,std::vector<std::vector<Lit>> jaccardAssumps,std::vector<SATCount>& scounts,SATSolver * solver);
    void JaccardOneRoundFor3(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, SATSolver* solver);

    void Jaccard2OneRoundFor3(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, SATSolver* solver);
    void JaccardHatOneRound(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, CMSat::SATSolver* solver0);
    void JaccardOneRound(unsigned jaccardHashCount, JaccardResult* result, bool computePrev, CMSat::SATSolver* solver0);
    void computeCountFromList(unsigned jaccardHashCount, std::map<unsigned, vector<unsigned>> &numHashList, std::map<unsigned, vector<double>>&numCountList, std::map<unsigned, SATCount>& count);
    void addKey2Map(unsigned jaccardHashCount, std::map<unsigned, vector<unsigned>> &numHashList, std::map<unsigned, vector<double>>&numCountList, std::map<unsigned, SATCount>& count);
    lbool BoundedSAT(
                     unsigned maxSolutions, unsigned minSolutions
                     , vector<Lit>& assumptions
                     , std::map<std::string, unsigned> solutionMap
                     , unsigned* solutionCount
                     );
    string GenerateRandomBits(unsigned size);
    string GenerateRandomBits_prob(unsigned size, double prob);
    void trimVar(std::vector<unsigned>&);

    lbool solve_exclude(vector<Lit> assumps, int & count);
    //config

    void call_after_parse() override;

    unsigned startIteration = 0;
    int pivotApproxMC = 52;

    double tStdError = 0.05;
    double prevTime;
    unsigned endJaccardIndex = 0;
    
    int printXor = 0;
    int trimOnly = 0;
    int onlyOne = 0;
    int onlyLast = 0;
    unsigned LowerFib = 0;
    unsigned UpperFib = 0;
    unsigned startHashCount = 1;
    unsigned tApproxMC = 2;
    unsigned tJaccardMC = 100;
    unsigned searchMode = 1;
    double jaccardXorRate = 0.5;
    double xorRate = 0.5;
    std::vector<XorClause> jaccardXorClause;
    int jaccardXorMax = 600;
    std::string specifiedOb;
    int XorMax = 1000;
    bool Parallel = false;
    double loopTimeout = 300;
    int unset_vars = 1;
    int test_func = 0;
    int Parity = 1;
    int notSampled = 0;
    int debug = 0;
    int originalPC_size;
    std::ofstream LOGF;
    std::random_device random_dev;
    std::mt19937 randomEngine;
    int nCounterExamples = 0;
    std::string outPrefix = "";
    bool is_diff = false;
    bool exclude = false;
    bool same_set = false;
    bool gauss_manual = false;
};


#endif //CUSP_H_
