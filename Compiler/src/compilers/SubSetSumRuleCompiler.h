#ifndef SUBSETSUMRULECOMPILER_H
#define SUBSETSUMRULECOMPILER_H
#include "AbstractGeneratorCompiler.h"

class SubSetSumRuleCompiler: public AbstractGeneratorCompiler{

    public:
        SubSetSumRuleCompiler(std::ofstream& file,int indentation,const aspc::Rule* r,const std::vector<std::string>& predNames,const std::unordered_map<std::string,unsigned>& predIds,const std::unordered_map<std::string,std::string>& predToStruct, std::unordered_set<std::string>& origPreds): AbstractGeneratorCompiler(file,indentation,r,predNames,predIds,predToStruct,origPreds){}
        std::string concreteClass(){return "SubSetSumGenerator";}
        void printAddClause(std::vector<unsigned>,bool){}
        void printAddConstraintClause(std::vector<unsigned>,bool){}
        void printAddSP(int index){}
        unsigned printAggregateInitialization(std::unordered_set<std::string>&){}
        void printUntrackLiteral(std::string tuplename){}
        void printHeadDerivation(std::string){}
        int printTrackedCheck(std::string tuplename){ return 0;}
        void compileFromStarter(bool recursive){}
        void compileNoStarter(bool recursive);
        
};
#endif