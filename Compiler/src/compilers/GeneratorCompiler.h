#ifndef GENERATORCOMPILER_H
#define GENERATORCOMPILER_H
#include "../language/Program.h"
#include "DataStructureCompiler.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../utils/Indentation.h"
#include "../utils/SharedFunctions.h"
#include <limits.h>
#include <fstream>
#include <cctype>

class GeneratorCompiler{
    public:
        GeneratorCompiler(const aspc::Program& pg,const std::string& execPath, const std::vector<std::string>& names, const std::unordered_map<std::string,unsigned>& id, DataStructureCompiler* mapCompiler,bool isStratified,std::unordered_set<std::string>& preds,std::string className,bool datalog,std::string prefix,bool model,const std::unordered_map<std::string,std::string>& predToStruct): modelFound(model),compPrefix(prefix),generatorClass(className), isDatalog(datalog), program(pg), executablePath(execPath), builtSCC(false),predNames(names),predIds(id),auxMapCompiler(mapCompiler),solvedByGenerator(isStratified),originalPredicates(preds),predicateToStruct(predToStruct){
            // std::cout << "GeneratorCompiler::constructor ";
            // std::cout << "Debug original predicates ";
            // for(std::string pred : originalPredicates){
            //     std::cout << pred << " ";
            // }
            // std::cout << std::endl; 
        }
        void compile();
        void buildAuxMapHandler();
        void buildGenerator();
        void buildComponentGenerator(int componentId);
        void compileComponentRules(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleId);
        void compileOrderedBody(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleIndex,std::vector<unsigned> order, const std::vector<const aspc::Formula*>& body,std::unordered_set<std::string>& boundVars,int& closingPars);

        void computeSCC();
        void buildPositiveDG();
        void buildDG();
        const std::vector<std::set<std::string>>& getComponents(){if(!builtSCC) computeSCC(); return components;}
    private:
        aspc::Program program;
        DataStructureCompiler* auxMapCompiler;
        std::vector<std::vector<std::vector<unsigned>>> ruleOrdering;
        std::vector<std::vector<std::unordered_map<unsigned,std::vector<unsigned>>>> aggregateOrderingForRule;
        std::unordered_map<std::string,unsigned> predIds;
        std::vector<std::string> predNames;
        
        std::string generatorClass;
        std::string compPrefix;
        bool isDatalog;
        bool modelFound;

        // DATA
        std::unordered_map<std::string,unsigned> local_predicates;
        std::vector<std::string> localPredicatesName;
        GraphWithTarjanAlgorithm pdg;
        std::vector<std::vector<int>> scc;
        std::vector<std::set<std::string>> components;
        bool builtSCC;
        std::string executablePath;
        bool solvedByGenerator;         

        std::unordered_set<std::string>& originalPredicates;
        std::unordered_map<std::string,std::string> predicateToStruct;
};
#endif