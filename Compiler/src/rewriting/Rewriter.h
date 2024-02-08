#ifndef REWRITER_H
#define REWRITER_H
#include "../language/Program.h"
#include "../utils/AggrSetPredicate.h"
#include "../utils/SharedVars.h"
#include "../utils/SharedFunctions.h"
#include "Analyzer.h"
#include <cassert>

struct GroundedAggrData{
    std::vector<aspc::Rule> rules;
    aspc::Atom* aggId;
    bool isEqual;
    bool genBound;
    aspc::Literal* aggSet;

    GroundedAggrData(): aggId(NULL), aggSet(NULL), rules({}), isEqual(false), genBound(false){}
    GroundedAggrData(const GroundedAggrData& other): aggId(NULL), isEqual(other.isEqual), genBound(other.genBound), aggSet(NULL), rules(other.rules){
        if(other.aggSet != NULL)
            setAggSet(*other.aggSet);
        if(other.aggId != NULL)
            setAggId(*other.aggId);
    }
    ~GroundedAggrData(){
        if(aggId != NULL)
            delete aggId;
        if(aggSet != NULL)
            delete aggSet;
    }
    GroundedAggrData& operator=(const GroundedAggrData& other){
        rules.clear();
        for(const aspc::Rule& r : other.rules) rules.push_back(r);
        if(aggId != NULL)
            delete aggId;
        aggId=NULL;
        if(other.aggId != NULL) setAggId(*other.aggId);
        
        isEqual=other.isEqual;
        genBound=other.genBound;

        if(aggSet != NULL)
            delete aggSet;
        aggSet=NULL;
        if(other.aggSet != NULL) setAggSet(*other.aggSet);
    }

    void setEqual(bool equal){this->isEqual=equal;}
    bool isEqualAgg()const {return isEqual;}

    void setGenBound(bool gen){this->genBound=gen;}
    bool isBoundGen()const {return genBound;}

    void setAggSet(aspc::Literal l){
        if(aggSet != NULL) delete aggSet;
        aggSet = new aspc::Literal(l);
    }
    void setAggId(aspc::Atom a){
        if(aggId != NULL) delete aggId;
        aggId = new aspc::Atom(a);
    }
    bool empty(){return aggId == NULL && aggSet == NULL && rules.empty();}
    void print(){
        std::cout << "Grounding aggregate data: {\n";
        std::cout << "   Rules:{\n";
        for(unsigned i=0; i<rules.size();i++){
            std::cout << "      ";
            rules[i].print();
        }
        std::cout << "   }\n";
        std::cout << "   AggId: "<< (aggId == NULL ? "Null" : "");
        if(aggId != NULL) aggId->print();
        std::cout << std::endl;
        std::cout << "   AggSet: "<< (aggSet == NULL ? "Null" : "");
        if(aggSet != NULL) aggSet->print();
        std::cout << std::endl;
        std::cout << "}\n";
    }
};
class Analyzer;
class Rewriter{
    public:
        static const int DOMAIN_RULE;
        static const int SUBSETSUM_RULE;
        static const int GROUND_RULE;
        static const int TO_GENERATE;
        Rewriter(Analyzer* prgAnalyzer, const aspc::Program& p,const std::vector<std::string>& predNames, const std::unordered_map<std::string,unsigned>& predId):analyzer(prgAnalyzer), program(p),predicateNames(predNames),predicateId(predId){}
        void reduceToSigleHeadForPredicate();
        std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation,const std::vector<aspc::Literal>& bodyLits,const std::vector<aspc::ArithmeticRelation>& bodyIneqs);
        std::pair<bool,std::pair<std::string,AggrSetPredicate>> buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm);
        std::vector<std::string> writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r);
        void rewriteAggregates();
        void computeCompletion();
        void addOriginalConstraint();
        void computeGlobalPredicates();
        void addToGroundRule(const aspc::Rule&,std::vector<int>&,Analyzer&);
        void rewriteGroundedAggregate(const aspc::Rule& r, Analyzer& analyzer, GroundedAggrData& data);
        void addDomainRule(std::vector<int>&);
        void addSubSetSumRule(std::vector<int>&);
        void printSharedVars();
        
        const std::vector<std::string>& getPredicateNames()const {return predicateNames;}
        const std::unordered_map<std::string,unsigned>& getPredicateId()const {return predicateId;}
        
        const aspc::Program& getSingleHeadProgram()const {return singleHeadForPredicate;}
        const aspc::Program& getGeneratorProgram()const {return generatorProgram;}
        const aspc::Program& getPropagatorsProgram()const {return propagatorsProgram;}

        GroundedAggrData& getAggregateGrounding(int ruleId) { 
            if(!aggregateGroundingMapping.count(ruleId)){
                return empty; 
            }
            return aggregateGrounding[aggregateGroundingMapping[ruleId]];
        }

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

        std::vector<std::string> subSetSumPredicates;
        std::unordered_map<std::string,unsigned> subSetSumPredicateToId;

        std::vector<std::string> sharedVarsPredicates;
        std::unordered_map<std::string,unsigned> sharedVarsPredicateId;

        std::vector<std::string> auxPredicates;
        std::unordered_map<std::string,unsigned> auxPredicateId;

        std::unordered_map<std::string,std::string> aggSetToSharedVars;
        std::unordered_map<std::string,SharedVars> aggrSharedVarsPredicate;
        std::unordered_map<std::string,AggrSetPredicate> aggrSetPredicates;
        std::unordered_map<std::string,int> prgPredicatAsAggSet;
        std::unordered_set<std::string> bodyPredicates;
        std::unordered_set<std::string> aggrIdPredicates;

        std::vector<aspc::Literal> buildingBody;
        std::vector<aspc::ArithmeticRelation> inequalities;
        std::vector<aspc::ArithmeticRelationWithAggregate> inequalitiesWithAggregate;
        std::vector<aspc::Atom> buildingHead;
        
        GroundedAggrData empty;
        std::vector<GroundedAggrData> aggregateGrounding;
        std::unordered_map<int,int> aggregateGroundingMapping;

        std::vector<aspc::Rule> domainRules;
        std::vector<aspc::Rule> subSetSumRules;

        Analyzer* analyzer;

        void clearData(){
            buildingHead.clear();
            buildingBody.clear();
            inequalities.clear();
            inequalitiesWithAggregate.clear();
        }
        void addRuleAfterAggregate(){
            afterAggregate.addRule(aspc::Rule(buildingHead,buildingBody,inequalities,inequalitiesWithAggregate,false,false));
            std::cout << "Rule after aggregate: ";afterAggregate.getRules().back().print();
        }

};
#endif