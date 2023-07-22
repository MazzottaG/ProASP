#ifndef REWRITER_H
#define REWRITER_H
#include "../language/Program.h"

class Rewriter{
    public:
        Rewriter(const aspc::Program& p,const std::vector<std::string>& predNames, const std::unordered_map<std::string,unsigned>& predId):program(p),predicateNames(predNames),predicateId(predId){}
        void reduceToSigleHeadForPredicate();
        void computeCompletion();
        void addOriginalConstraint();
        void computeGlobalPredicates();
        void addToGroundRule(const aspc::Rule&);

        const std::vector<std::string>& getPredicateNames()const {return predicateNames;}
        const std::unordered_map<std::string,unsigned>& getPredicateId()const {return predicateId;}
        
        const aspc::Program& getSingleHeadProgram()const {return singleHeadForPredicate;}
        const aspc::Program& getGeneratorProgram()const {return generatorProgram;}
        const aspc::Program& getPropagatorsProgram()const {return propagatorsProgram;}

        const std::vector<bool>& getPropagatorRuleLabeling()const {return labeledPropgatorRules;}
    private:
        aspc::Program program;
        std::vector<std::string> predicateNames;
        std::unordered_map<std::string,unsigned> predicateId;
        
        aspc::Program singleHeadForPredicate;
        std::vector<bool> labeledSingleHeadRules;
        aspc::Program generatorProgram;
        aspc::Program propagatorsProgram;
        std::vector<bool> labeledPropgatorRules;

        std::vector<std::string> supportPredicates;
        std::unordered_map<std::string,unsigned> supportPredicateId;

        std::vector<std::string> auxPredicates;
        std::unordered_map<std::string,unsigned> auxPredicateId;

};
#endif