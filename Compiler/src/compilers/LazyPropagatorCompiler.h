#ifndef LAZYPROPAGATORCOMPILER_H
#define LAZYPROPAGATORCOMPILER_H
#include<algorithm>
#include "../language/Program.h"
#include "DataStructureCompiler.h"
#include "DependencyManager.h"
//#define COMPILE_DEBUG_PRINT
//#define ALLOW_RESTARTS
class LazyPropagatorCompiler{
    private:
        //program containing both constraints and generation rules
        aspc::Program program;
        //should ask to declare data structure that the propagator will use
        DataStructureCompiler* auxMapCompiler;
        //used to take the tuples from the correct structure type
        std::unordered_map<std::string,std::string> predicateToStruct;
        //path to executable
        std::string execPath;
        //defines the order in which propagators will be called by propagator
        //std::vector<unsigned> propagatorOrder;
        DependencyManager depManager;  
        std::ofstream outfile;
        Indentation ind;
        std::set<std::string> positiveProgramHeadPredicates;
        int totalNumOfPredicates;
        //ordering of rules for every predicate of the corresponding component
        std::unordered_map<unsigned, std::vector<std::vector<unsigned>>> ruleOrderings;
        std::unordered_map<unsigned, std::vector<std::vector<unsigned>>> ruleOrderingsByHead;
        std::unordered_map<unsigned, std::vector<std::vector<unsigned>>> ruleOrderingsExplainFalse;
        std::vector<std::string> propagatorNames;
        std::unordered_set<std::string> alwaysToCheckPredicates;
        std::vector<unsigned> findNonExitRule(std::vector<int>, std::vector<unsigned>);
        void compileReasonAndSupportSaving(std::vector<std::pair<int, bool>>&, int, std::string tuplePrefix, bool fixpoint);
        void compileTrueInterfacePropagation(int, std::string, bool, bool, bool);
        void compileTrueNonInterfacePropagation(int, std::string, bool, bool);
        bool compileAddTupleToFactoryForExplainFalse(unsigned, const aspc::Literal*, const std::set<std::string>& componentPreds);
        void compileStopPropagateToFalse();
    public:
        LazyPropagatorCompiler(const aspc::Program&, std::string&, DataStructureCompiler*, const std::unordered_map<std::string, std::string>&);
        void setAlwaysToCheckPredicates(std::unordered_set<std::string>);
        void compile();
        void compileTupleFactoryCC();
        //compile scc of pos Cycle program
        void compileSCC(std::vector<int>, unsigned);
        void compileConstraint(unsigned, unsigned);
        void openPropagatorFile(unsigned, std::string, std::set<std::string>&);
        void closePropagatorFile();
        void compileComponentWatched(std::vector<int>& , std::vector<unsigned>&);
        void compileRuleWatcher(unsigned, std::unordered_map<std::string, int>&);
        void compileFixPointComputationLevelZero(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileFixPointComputation(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileCheckLiteralStatus(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileExplainTrue(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileExplainFalse(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>& );
        void compileRuleByStarter(unsigned, const aspc::Rule&, int, const std::set<std::string>&, bool, bool, bool, bool);
        void compileLazyPropClass();
};
#endif /*LAZYPROPAGATORCOMPILER*/