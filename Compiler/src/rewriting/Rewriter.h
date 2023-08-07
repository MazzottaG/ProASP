#ifndef REWRITER_H
#define REWRITER_H
#include "../language/Program.h"
#include "../utils/AggrSetPredicate.h"
#include "../utils/SharedFunctions.h"

class Rewriter{
    public:
        Rewriter(const aspc::Program& p,const std::vector<std::string>& predNames, const std::unordered_map<std::string,unsigned>& predId):program(p),predicateNames(predNames),predicateId(predId){}
        void reduceToSigleHeadForPredicate();
        std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation);
        std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm);
        std::vector<std::string> writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r);
        void rewriteAggregates();
        void computeCompletion();
        void addOriginalConstraint();
        void computeGlobalPredicates();
        void addToGroundRule(const aspc::Rule&);

        const std::vector<std::string>& getPredicateNames()const {return predicateNames;}
        const std::unordered_map<std::string,unsigned>& getPredicateId()const {return predicateId;}
        
        const aspc::Program& getSingleHeadProgram()const {return singleHeadForPredicate;}
        const aspc::Program& getGeneratorProgram()const {return generatorProgram;}
        const aspc::Program& getPropagatorsProgram()const {return propagatorsProgram;}

        //const std::vector<bool>& getPropagatorRuleLabeling()const {return labeledPropgatorRules;}
    private:
        aspc::Program program;
        std::vector<std::string> predicateNames;
        std::unordered_map<std::string,unsigned> predicateId;
        
        aspc::Program singleHeadForPredicate;
        //std::vector<bool> labeledSingleHeadRules;
        
        aspc::Program afterAggregate;
        
        aspc::Program generatorProgram;
        aspc::Program propagatorsProgram;
        //std::vector<bool> labeledPropgatorRules;

        std::vector<std::string> supportPredicates;
        std::unordered_map<std::string,unsigned> supportPredicateId;

        std::vector<std::string> auxPredicates;
        std::unordered_map<std::string,unsigned> auxPredicateId;

        std::unordered_map<std::string,AggrSetPredicate> aggrSetPredicates;
        std::unordered_map<std::string,int> prgPredicatAsAggSet;
        std::unordered_set<std::string> bodyPredicates;
        std::unordered_set<std::string> aggrIdPredicates;

        std::vector<aspc::Literal> buildingBody;
        std::vector<aspc::ArithmeticRelation> inequalities;
        std::vector<aspc::ArithmeticRelationWithAggregate> inequalitiesWithAggregate;
        std::vector<aspc::Atom> buildingHead;
        
        void clearData(){
            buildingHead.clear();
            buildingBody.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
        }
        void addRuleAfterAggregate(){
            afterAggregate.addRule(aspc::Rule(buildingHead,buildingBody,inequalities,inequalitiesWithAggregate,false,false));
        }

};
#endif