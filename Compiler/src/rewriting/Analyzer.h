#ifndef ANALYZER_H
#define ANALYZER_H
#include "../language/Program.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../utils/SharedFunctions.h"
#include "../compilers/DependencyManager.h"
struct RuleBody{

    //projection terms
    std::vector<std::string> terms;
    //body literals
    std::vector<aspc::Literal> literals;
    //body inequalities
    std::vector<aspc::ArithmeticRelation> inequalities;
    //body aggregate
    std::vector<aspc::ArithmeticRelationWithAggregate> aggregates;
    RuleBody(){}
    RuleBody(std::vector<aspc::Literal> lits,std::vector<aspc::ArithmeticRelation> ineqs,std::vector<aspc::ArithmeticRelationWithAggregate> aggs, std::vector<std::string> headTerms): literals(lits),inequalities(ineqs),aggregates(aggs),terms(headTerms) {}
    RuleBody(const RuleBody& other): literals(other.literals),inequalities(other.inequalities),aggregates(other.aggregates),terms(other.terms) {}

    RuleBody& operator=(const RuleBody& other){
        literals.clear();
        for(const aspc::Literal& l : other.literals){
            literals.push_back(l);
        }
        inequalities.clear();
        for(const aspc::ArithmeticRelation& l : other.inequalities){
            inequalities.push_back(l);
        } 
        aggregates.clear();
        for(const aspc::ArithmeticRelationWithAggregate& l : other.aggregates){
            aggregates.push_back(l);
        }
        terms = other.terms;
        return *this;
    }
    
    bool operator==(const RuleBody& other){
        if(literals.size() != other.literals.size()) return false;
        for(unsigned i = 0; i < literals.size(); i++){
            if(!(literals[i] == other.literals[i])) return false;
        }
        if(inequalities.size() != other.inequalities.size()) return false;
        for(unsigned i = 0; i < inequalities.size(); i++){
            if(!(inequalities[i] == other.inequalities[i])) return false;
        }
        if(aggregates.size() != other.aggregates.size()) return false;
        for(unsigned i = 0; i < aggregates.size(); i++){
            if(!(aggregates[i] == other.aggregates[i])) return false;
        }
        if(terms.size() != other.terms.size()) return false;
        for(unsigned i = 0; i < terms.size(); i++){
            if(!(terms[i] == other.terms[i])) return false;
        }
        return true;
    }
    void print(std::string predicate){
        std::cout << predicate << ": {\n";

        std::cout<<"   Terms:";
        for(std::string t : terms){
            std::cout<<" "<<t;
        }
        std::cout<<std::endl<<"   Literals:";
        for(const aspc::Literal& l : literals){
            std::cout << " ";
            l.print();
        }
        std::cout<<std::endl<<"   Inequalities:";
        for(const aspc::ArithmeticRelation& l : inequalities){
            std::cout << " ";
            l.print();
        }

        std::cout<<std::endl<<"   Aggregates:";
        for(const aspc::ArithmeticRelationWithAggregate& l : aggregates){
            std::cout << " ";
            l.print();
        }
        std::cout << std::endl << "}\n";
    }
    
};
class Analyzer{
    private:
        std::vector<bool> inputLabel;
        aspc::Program program;
        DependencyManager dependencyManager;

        // Rewriter output
        std::vector<bool> eagerLabel;
        aspc::Program datalogPrg;
        aspc::Program eagerPrg;
        aspc::Program lazyPrg;

        std::unordered_map<int,std::vector<std::string>> joinRuleTerms;

        std::unordered_map<std::string,RuleBody> joinRuleData;
        std::vector<int> sccTypeLabel;
        std::unordered_map<std::string,int> predicateToComponent;

        std::unordered_map<int,std::vector<int>> rulesBodyLabeling;
        std::unordered_map<int,int> remappingBodyLabeling;

        bool fullGrounding;
        
        bool findAggregateNegativeDependency(const std::vector<std::vector<int>>& scc, unsigned componentId,const aspc::ArithmeticRelationWithAggregate* aggrRelation);
        bool labelAggregateLiteral(std::unordered_map<std::string,int>& predToComponent,std::vector<int>& sccLabel,const aspc::ArithmeticRelationWithAggregate* aggrRelation);
        void mapPredicateToComponent(const std::vector<std::vector<int>>& scc,std::unordered_map<std::string,int>& predicateToComponent);
        void renameVariablesForComponent();
        void labelStratified(std::vector<int>& stratLabel,const std::vector<std::vector<int>>& scc);
        void labelLazyness(const std::vector<std::vector<int>>& scc, std::unordered_map<std::string,int>& predToComponent,std::vector<int>& sccLabel);
        void labelEager(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc);
        void labelLazy(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc);
        void labelDatalog(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc);
        void labelType(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc);
        int labelAggregate(const std::vector<int>& sccLabel,const aspc::ArithmeticRelationWithAggregate* aggrRelation,std::unordered_map<std::string,int>& predToComponent);
        bool labelFormulas(const std::vector<int>& sccLabel,const std::vector<const aspc::Formula*>* body,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& label);
        void labelArithmeticRelations(const std::vector<const aspc::Formula*>* formulas,std::vector<int>& formulaLabeling, std::unordered_set<std::string>& positiveVars);
        void labelRemainingArithmeticRelations(const std::vector<const aspc::Formula*>* formulas,std::vector<int>& formulaLabeling, std::unordered_set<std::string>& positiveVars);
        bool canExportAggregate(const aspc::ArithmeticRelationWithAggregate* aggrRelation, std::unordered_set<std::string> positiveEDBVars, std::unordered_set<std::string> positiveIDBVars);
        bool findMaximalDatalogBody(const aspc::Rule* rule,int ruleId,const std::vector<int>& sccLabel,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& formulaLabeling);
        void rewriteWithJoin(const aspc::Rule* rule,int ruleId,std::vector<int> formulaLabeling,bool isConstraint);

        void buildPrograms(const std::vector<std::vector<int>>& scc,const std::vector<int>&  sccLabel,std::unordered_map<std::string,int>& predToComponent);
        void printProgramBySCC(const std::vector<std::vector<int>>& scc,const std::vector<int>& sccLabel,int label);
        void splitProgram();
        std::pair<std::unordered_map<std::string,std::string>,bool> getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const;
        
    public:

        const int UNK_LAZY  = 0;
        const int NOT_LAZY  = 1;
        const int LAZY      = 2;

        const int UNK_STRATIFIED = 0;
        const int STRATIFIED    = 1;
        const int NOT_STRATIFIED = 2;

        const int UNK_TYPE      = 0;
        const int TYPE_LAZY     = 1;
        const int TYPE_EAGER    = 2;
        const int TYPE_DATALOG  = 3;

        const int DATALOG_BODY      = 0;
        const int EXTRACTED_JOIN    = 1;
        const int NOT_EXTRACTED     = 2;

        const int UNK_FORMULA_LABEL     = 0;
        const int DATALOG_FORMULA       = 1;
        const int NON_DATALOG_FORMULA   = 2;


        Analyzer(const aspc::Program& p,const std::vector<bool>& labels,bool fullGrounding);
        const std::vector<bool>& getEagerLabel()const;
        const aspc::Program& getDatalog()const;
        const aspc::Program& getEager()const;
        const aspc::Program& getLazy()const;

        const std::unordered_map<std::string,unsigned> getPredicateToId()const;
        const std::vector<std::string> getIdToPredicate()const;

        std::vector<int> getRemappedRuleBodyLabeling(int ruleId) {
            assert(remappingBodyLabeling.count(ruleId)!=0);
            assert(rulesBodyLabeling.count(remappingBodyLabeling[ruleId])!=0); 
            return rulesBodyLabeling[remappingBodyLabeling[ruleId]];
        }
        std::vector<int> getRuleBodyLabeling(int ruleId) {
            assert(rulesBodyLabeling.count(ruleId)!=0); 
            return rulesBodyLabeling[ruleId];
        }
        bool isEDB(std::string predicate);
        bool isFullGrounding()const{return fullGrounding;}
        bool isJoinPredicate(std::string predicate){return joinRuleData.find(predicate)!=joinRuleData.end();}
        
};
#endif