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

class ProgramReader{

    public:
        ProgramReader(int argc, char *argv[]);
        void labelHybridRule(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        void rewriteGroundingPredicate(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        const aspc::Program& getInputProgram(){ return rewrittenProgram;}
        const std::vector<bool>& getInputProgramLabel(){ return rewrittenRuleLabel;}
        const std::unordered_set<std::string>& getOriginalPredicates(){ return originalPredicates;}
        bool isFullGrounding()const {return fullGrounding;}
        void rewriteRuleForComponent();
        std::pair<std::unordered_map<std::string,std::string>,bool> getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const;

private:

        bool label;
        bool fullGrounding;
        ASPCore2CompileProgramListener listener;
        std::vector<bool> ruleLabel;
        std::unordered_set<std::string> originalPredicates;
        std::unordered_set<std::string> toGroundPredicates;
		std::unordered_set<std::string> propagatorPredicates;

        std::unordered_map<std::string,std::string> remapped_predicates;
        std::vector<std::pair<std::string,int>> remapped;

        DependencyManager dependencyManager;

        aspc::Program rewrittenProgram;
        std::vector<bool> rewrittenRuleLabel;


};
#endif