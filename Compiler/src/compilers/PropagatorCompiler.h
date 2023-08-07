#ifndef PROPAGATORCOMPILER_H
#define PROPAGATORCOMPILER_H
#include "../language/Program.h"
#include "DataStructureCompiler.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../utils/Indentation.h"
#include "../utils/SharedFunctions.h"
#include <limits.h>
#include <fstream>
#include <cctype>

class PropagatorCompiler{
    public:
        PropagatorCompiler(const aspc::Program& pg,const std::string& execPath, DataStructureCompiler* mapCompiler,const std::unordered_map<std::string,std::string>& predToStruct):program(pg), executablePath(execPath), auxMapCompiler(mapCompiler),builtSCC(false),predicateToStruct(predToStruct){}
        void compile();
        void buildAuxMapHandler();
        void compileRuleLevelZero(unsigned ruleId,std::ofstream&,Indentation&);
        void compileRuleWatcher(unsigned ruleId,std::ofstream&,Indentation&);
        void compileRuleFromStarter(unsigned ruleId, std::ofstream&, Indentation&);
        void compileEagerRuleWithCount(unsigned, std::ofstream&, Indentation&,bool);
        void compileEagerRuleWithSum(unsigned, std::ofstream&, Indentation&,bool);
        void compileEagerRuleWithAggregate(unsigned, std::ofstream&, Indentation&,bool);

        void printTuplePropagation(std::ofstream& outfile,Indentation& ind, std::string tuple,bool asFalse,bool level0 ,bool constraint = false);
        void printAddPropagatedToReason(std::ofstream& outfile,Indentation& ind, std::string tuplename,bool asFalse,bool constraint=false);
        void printAddToReason(std::ofstream& outfile,Indentation& ind, std::string var,std::string sign);
        void printUpdateSum(std::ofstream& outfile, Indentation& ind,bool);
        // void printAddToReason(std::ofstream& outfile,Indentation& ind, std::string tuplename,bool asFalse,std::string reasonStorage);

        void printConflict(std::ofstream& outfile,Indentation& ind, bool level0);
        
        void computeSCC();
        void buildPositiveDG();
        void computePropagatorOrder();
    private:
        aspc::Program program;
        DataStructureCompiler* auxMapCompiler;
        std::string executablePath;
        std::vector<bool> ruleLabel;
        
        std::vector<unsigned> propagatorOrder;                
        std::vector<std::pair<std::vector<std::vector<unsigned>>,std::vector<std::vector<unsigned>>>> ruleOrdering;

        std::unordered_map<std::string,unsigned> local_predicates;
        std::vector<std::string> localPredicatesName;
        
        GraphWithTarjanAlgorithm pdg;
        std::vector<std::vector<int>> scc;
        std::vector<std::set<std::string>> components;
        bool builtSCC;

        std::unordered_map<std::string,std::string> predicateToStruct;
};
#endif