#ifndef HYBRIDGENERATOR_H
#define HYBRIDGENERATOR_H
#include "../language/Program.h"
#include "DataStructureCompiler.h"
#include "DependenciesHandler.h"

class HybridGenerator{
    
    public:
        HybridGenerator(const aspc::Program& pg, std::vector<bool> labels, const std::string& execPath, const std::vector<std::string>& names, const std::unordered_map<std::string,unsigned>& id, DataStructureCompiler* mapCompiler,std::unordered_set<std::string>& preds,const std::unordered_map<std::string,std::string>& predToStruct,const std::unordered_map<std::string,unsigned>& predToAggrIndex,const std::unordered_map<std::string,std::string>& aggrIdToAggrSet):
            program(pg),
            ruleLabel(labels), 
            auxMapCompiler(mapCompiler),
            predIds(id),
            predNames(names),
            executablePath(execPath),
            originalPredicates(preds),
            depHandler(pg),
            negDep(true),
            predicateToStruct(predToStruct),
            predicateToAggrIndex(predToAggrIndex),
            sumAggregateIdData(aggrIdToAggrSet){}

        void compile();
        void compileComponentRules(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleIndex);
        void buildComponentGenerator(int componentId,std::string className,std::ofstream& outfile,Indentation& ind);
        void buildConstraintGrounder(int ruleId,std::string className,std::ofstream& outfile,Indentation& ind);
    private:
        aspc::Program program;
        std::vector<bool> ruleLabel;

        DataStructureCompiler* auxMapCompiler;
        std::unordered_map<std::string,unsigned> predIds;
        std::vector<std::string> predNames;

        std::string executablePath;
        std::unordered_set<std::string>& originalPredicates;
        DependenciesHandler depHandler;
        bool negDep;
        std::unordered_map<std::string,std::string> predicateToStruct;
        std::unordered_map<std::string,unsigned> predicateToAggrIndex;
        std::unordered_map<std::string,std::string> sumAggregateIdData;
        
};
#endif