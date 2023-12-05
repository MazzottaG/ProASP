#ifndef GROUNDERGENCOMPILER_H
#define GROUNDERGENCOMPILER_H

#include "AbstractGeneratorCompiler.h"
#include "../rewriting/Rewriter.h"
#include <cassert>

class GrounderGenCompiler : public AbstractGeneratorCompiler{
    public:
        GrounderGenCompiler(std::ofstream& file,int indentation,const aspc::Rule* r,const std::vector<std::string>& predNames,const std::unordered_map<std::string,unsigned>& predIds,const std::unordered_map<std::string,std::string>& predicateToStruct,GroundedAggrData& groundAgg, std::unordered_set<std::string>& origPreds):AbstractGeneratorCompiler(file,indentation,r,predNames,predIds,predicateToStruct,origPreds),aggregateData(groundAgg){
            std::cout << "Building GrounderGenCompiler"<<std::endl;
            aggregateData.print();
            // std::cout << "GrounderGenCompiler::constructor ";
            // std::cout << "Debug original predicates ";
            // for(std::string pred : originalPredicates){
            //     std::cout << pred << " ";
            // }
            // std::cout << std::endl; 
        }
        void compileAggregate(std::unordered_set<std::string>& boundVars,const aspc::ArithmeticRelationWithAggregate* aggr);
        std::string concreteClass(){return "BasicGenerator";}
        void printAddClause(std::vector<unsigned>,bool);
        void printAddConstraintClause(std::vector<unsigned>,bool);
        void printAddSP(int);
        void printAggregateInitialization(std::unordered_set<std::string>&);
        void compileConstraintGrounder();
        int printTrackedCheck(std::string tuplename);
    private:
        GroundedAggrData aggregateData;
};
#endif