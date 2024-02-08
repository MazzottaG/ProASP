#ifndef HYBRIDGENERATOR_H
#define HYBRIDGENERATOR_H
#include "../language/Program.h"
#include "../rewriting/Rewriter.h"
#include "DataStructureCompiler.h"
#include "DependenciesHandler.h"
#include "GrounderGenCompiler.h"
#include "DomainRuleCompiler.h"
#include "SubSetSumRuleCompiler.h"

class HybridGenerator{
    
    public:
        HybridGenerator(Analyzer* analyzer,Rewriter* rewriter, const aspc::Program& pg, std::vector<int> labels, const std::string& execPath, const std::vector<std::string>& names, const std::unordered_map<std::string,unsigned>& id, DataStructureCompiler* mapCompiler,std::unordered_set<std::string>& preds,const std::unordered_map<std::string,std::string>& predToStruct,const std::unordered_map<std::string,unsigned>& predToAggrIndex,const std::unordered_map<std::string,std::string>& aggrIdToAggrSet,const std::unordered_map<unsigned,unsigned>& tracedRule):
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
            sumAggregateIdData(aggrIdToAggrSet),
            prgRewriter(rewriter),
            prgAnalyzer(analyzer),
            traceToGroundRule(tracedRule){
                // std::cout << "HybridGenerator::constructor Debug original predicates ";
                // for(std::string pred : originalPredicates){
                //     std::cout << pred << " ";
                // }
                // std::cout << std::endl;
            }

        void compile();
        void compileComponentRules(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleIndex);
        void buildComponentGenerator(int componentId,std::string className,std::ofstream& outfile,Indentation& ind,std::unordered_set<std::string>& generatedPredicate);
        void buildConstraintGrounder(int ruleId,std::string className,std::ofstream& outfile,Indentation& ind);
    private:
        Rewriter* prgRewriter;
        Analyzer* prgAnalyzer;
        aspc::Program program;
        std::vector<int> ruleLabel;

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

        std::unordered_map<unsigned, unsigned> traceToGroundRule;

        std::vector<std::vector<int>> cleaningComponents;
        
};
#endif