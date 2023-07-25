#ifndef GROUNDERGENCOMPILER_H
#define GROUNDERGENCOMPILER_H

#include "AbstractGeneratorCompiler.h"

class GrounderGenCompiler : public AbstractGeneratorCompiler{
    public:
        GrounderGenCompiler(std::ofstream& file,int indentation,const aspc::Rule* r,const std::vector<std::string>& predNames,const std::unordered_map<std::string,unsigned>& predIds):AbstractGeneratorCompiler(file,indentation,r,predNames,predIds){}
            
        std::string concreteClass(){return "BasicGenerator";}
        void printAddClause(std::vector<unsigned>,bool);
        void printAddConstraintClause(std::vector<unsigned>,bool);
        void printAddSP(int);
        void compileConstraintGrounder();
        int printTrackedCheck(std::string tuplename);
};
#endif