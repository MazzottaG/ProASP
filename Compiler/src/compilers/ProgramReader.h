#ifndef PROGRAMREADER_H
#define PROGRAMREADER_H

#include <iostream>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include "../language/Program.h"
#include "antlr4-runtime.h"
#include "../parser/ASPCore2Lexer.h"
#include "../parser/ASPCore2Parser.h"
#include "../parser/ASPCore2CompileProgramListener.h"
#include "DependencyManager.h"
#include "../rewriting/PosCycleRewriter.h"

class ProgramReader{

    public:
        ProgramReader(int argc, char *argv[]);
        void labelHybridRule(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        void rewriteGroundingPredicate(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        const aspc::Program& getInputProgram(){ return rewrittenProgram;}
        const aspc::Program& getPosCycleProgram(){ return lazyProgramListener.getProgram();}
        const aspc::Program& getPosCycleDomainProgram(){return *posCycleDomainProgram;}
        const aspc::Program& getPosCycleGeneratorProgram(){ return posCycleRewriter.getGeneratorProgram();}
        const aspc::Program& getPosCyclePropagatorProgram(){ return *posCyclePropagatorProgram;}
        const std::vector<bool>& getInputProgramLabel(){ return rewrittenRuleLabel;}
        const std::unordered_set<std::string>& getOriginalPredicates(){ return originalPredicates;}
        std::unordered_set<std::string> getAlwaysToCheckPredicates(){return posCycleRewriter.getAlwaysToCheckFalsePredicates();}
        bool isFullGrounding()const {return fullGrounding;}
        void rewriteRuleForComponent(std::set<std::string>);
        std::pair<std::unordered_map<std::string,std::string>,bool> getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const;
private:

        bool label;
        bool fullGrounding;
        ASPCore2CompileProgramListener listener;
        ASPCore2CompileProgramListener lazyProgramListener;
        std::vector<bool> ruleLabel;
        std::unordered_set<std::string> originalPredicates;
        std::unordered_set<std::string> toGroundPredicates;
		std::unordered_set<std::string> propagatorPredicates;
        std::unordered_set<std::string> alwaysToCheckPredicates;

        std::unordered_map<std::string,std::string> remapped_predicates;
        std::vector<std::pair<std::string,int>> remapped;

        DependencyManager dependencyManager;
        aspc::Program rewrittenProgram;
        aspc::Program constraintsPosP;
        const aspc::Program* posCycleDomainProgram;
        const aspc::Program* posCycleProgram;
        const aspc::Program* posCyclePropagatorProgram;
        PosCycleRewriter posCycleRewriter;
        
        std::vector<bool> rewrittenRuleLabel;
        bool posCyclePredsDefinedInProgram(const aspc::Program&, const aspc::Program&);
        void mergePosCycleProgramAndInputProgram(const aspc::Program&);
};
#endif