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

class ProgramReader{

    public:
        ProgramReader(int argc, char *argv[]);
        void labelHybridRule(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        void rewriteGroundingPredicate(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId);
        const aspc::Program& getInputProgram(){ return listener.getProgram();}
        const std::vector<bool>& getInputProgramLabel(){ return ruleLabel;}
        const std::unordered_set<std::string>& getOriginalPredicates(){ return originalPredicates;}
    private:
        bool label;
        ASPCore2CompileProgramListener listener;
        std::vector<bool> ruleLabel;
        std::unordered_set<std::string> originalPredicates;
        std::unordered_set<std::string> toGroundPredicates;
		std::unordered_set<std::string> propagatorPredicates;

        std::unordered_map<std::string,std::string> remapped_predicates;
        std::vector<std::pair<std::string,int>> remapped;

};
#endif