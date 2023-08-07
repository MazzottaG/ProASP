#ifndef DATASTRUCTURECOMPILER_H
#define DATASTRUCTURECOMPILER_H
#include "../language/Rule.h"
#include "../utils/Indentation.h"
#include <limits.h>
#include <fstream>

#include <unordered_map>

class DataStructureCompiler{
    public:
        std::vector<std::vector<unsigned>> declareGeneratorDataStructure(const aspc::Rule& rule,const std::set<std::string>& component);
        std::pair<std::vector<std::vector<unsigned>>,std::vector<std::vector<unsigned>>> declarePropagatorDataStructure(const aspc::Rule& rule);
        void printAuxMap()const;
        const std::unordered_map<std::string,std::set<std::vector<unsigned>>>& getAuxMapNameForPredicate()const{return auxMapNameForPredicate;}
        void buildAuxMapHandler(std::string,const std::vector<std::string>&,const std::unordered_map<std::string,std::string>&);
        void addAuxMap(std::string,std::vector<unsigned>);
    private:
        std::unordered_map<std::string,std::set<std::vector<unsigned>>> auxMapNameForPredicate;
};
#endif