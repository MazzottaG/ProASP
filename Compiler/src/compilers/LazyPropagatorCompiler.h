#ifndef LAZYPROPAGATORCOMPILER_H
#define LAZYPROPAGATORCOMPILER_H
#include<algorithm>
#include "../language/Program.h"
#include "DataStructureCompiler.h"
#include "DependencyManager.h"
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
        //ordering of rules for every predicate of the corresponding component
        std::unordered_map<unsigned, std::vector<std::vector<unsigned>>> ruleOrderings;
        std::unordered_map<unsigned, std::vector<std::vector<unsigned>>> ruleOrderingsByHead;
        std::vector<std::string> propagatorNames;
        std::vector<unsigned> findNonExitRule(std::vector<int>, std::vector<unsigned>);
        void compileReasonSaving(std::vector<std::pair<int, bool>>&);
    public:
        LazyPropagatorCompiler(const aspc::Program&, std::string&, DataStructureCompiler*, const std::unordered_map<std::string, std::string>&);
        void compile();
        //compile scc of pos Cycle program
        void compileSCC(std::vector<int>, unsigned);
        //compile propagators for constraints is pos cycle Program
        //void compileConstraints();
        //void computePropagatorOrder();
        void openPropagatorFile(unsigned);
        void closePropagatorFile();
        void compileComponentWatched(std::vector<int> , unsigned);
        void compileRuleWatcher(unsigned, std::unordered_map<std::string, int>&);
        void compileFixPointComputation(std::vector<int>& , std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileFixPointComputationFromStarters(std::vector<int>& , std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileCheckLiteralStatus(std::vector<int>&, std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileExplainTrue(std::vector<int>& , std::vector<unsigned>&, std::set<std::string>&, std::vector<unsigned>&);
        void compileRuleByStarter(unsigned, const aspc::Rule&, int, const std::set<std::string>&, bool, bool, bool, bool);
        void compileLazyPropClass();
};
#endif /*LAZYPROPAGATORCOMPILER*/