#ifndef LAZYPROPAGATORCOMPILER_H
#define LAZYPROPAGATORCOMPILER_H
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
        std::vector<unsigned> propagatorOrder;
        DependencyManager depManager;  
        std::ofstream outfile;
        Indentation ind;
    
    public:
        LazyPropagatorCompiler(const aspc::Program&, std::string&, DataStructureCompiler*, const std::unordered_map<std::string, std::string>&);
        void compile();
        //compile scc of pos Cycle program
        void compileSCC(std::vector<int>, unsigned);
        //compile propagators for constraints is pos cycle Program
        void compileConstraints();
        void computePropagatorOrder();
        void openPropagatorFile(bool, unsigned);
        void closePropagatorFile();
};
#endif /*LAZYPROPAGATORCOMPILER*/