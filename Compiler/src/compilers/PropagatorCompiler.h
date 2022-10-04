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
        PropagatorCompiler(const aspc::Program& pg,const std::string& execPath, const std::vector<std::string>& names, const std::unordered_map<std::string,unsigned>& id, DataStructureCompiler* mapCompiler):program(pg), executablePath(execPath),predNames(names),predIds(id),auxMapCompiler(mapCompiler){}
        void compile();
        void buildAuxMapHandler();
        void compileRuleLevelZero(unsigned ruleId,std::ofstream&,Indentation&);


    private:
        aspc::Program program;
        DataStructureCompiler* auxMapCompiler;
        
        std::vector<std::pair<std::vector<std::vector<unsigned>>,std::vector<std::vector<unsigned>>>> ruleOrdering;
        std::unordered_map<std::string,unsigned> predIds;
        std::vector<std::string> predNames;
        
        // DATA
        std::unordered_map<std::string,unsigned> local_predicates;
        std::vector<std::string> localPredicatesName;
        std::string executablePath;                
};
#endif