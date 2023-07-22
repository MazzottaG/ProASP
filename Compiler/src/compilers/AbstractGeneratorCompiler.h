#ifndef ABSTRACTGENERATORCOMPILER_H
#define ABSTRACTGENERATORCOMPILER_H
#include <fstream>
#include "../utils/Indentation.h"
#include "../language/Rule.h"
#include "../utils/SharedFunctions.h"

class AbstractGeneratorCompiler{

    public:
        AbstractGeneratorCompiler(std::ofstream& file,int indentation,const aspc::Rule* r,const std::vector<std::string>& predNames,const std::unordered_map<std::string,unsigned>& predIds):outfile(file),ind(indentation),rule(r),predicateNames(predNames),predicateIds(predIds),auxliteral("aux_body"){}
        
        void compileFromStarter(bool recursive);
        void compileNoStarter(bool recursive);
        virtual std::string concreteClass(){return "BasicGenerator";}
        virtual void printAddClause(std::vector<unsigned>,bool){}
        virtual void printAddConstraintClause(std::vector<unsigned>,bool){}
        virtual void printAddSP(int index){}
        void compileSingleStarter(bool recursive,std::vector<unsigned> order,unsigned starter);
        std::unordered_map<std::string,std::set<std::vector<unsigned>>> getUsedAuxMaps()const{return usedAuxMap;}
        std::vector<std::vector<unsigned>> reorderRule();

        std::ofstream& outfile;
        Indentation ind;
        const aspc::Rule* rule;

        const std::vector<std::string>& predicateNames;
        const std::unordered_map<std::string,unsigned>& predicateIds;

        std::unordered_map<std::string,std::set<std::vector<unsigned>>> usedAuxMap;
        const std::string auxliteral; 
};
#endif