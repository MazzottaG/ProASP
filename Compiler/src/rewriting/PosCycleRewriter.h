#ifndef POSCYCLEREWRITER_H
#define POSCYCLEREWRITER_H

#include "../language/Program.h"
#include "../compilers/DependencyManager.h"
#include <algorithm>

class PosCycleRewriter{
private:
    //inputProgram / rewrittenProgram
    aspc::Program* propProgram;
    //to-lazy program
    const aspc::Program* programPP;
    //constraints of to-ground to-compile
    aspc::Program* addedConstraintsProgram;
    //generator rules from constraints
    aspc::Program generatorProgram;
    //to-lazy propagator (normal rules only)
    aspc::Program propagatorProgram;
    //domainRules for lazy predicates
    aspc::Program domainProgram;
    DependencyManager dependencyManager;
    std::vector<std::vector<int>> sccs;
    std::set<std::string> predicatesDefinedInPosCycleProgram;
    std::unordered_set<std::string> alwaysToCheckFalsePredicates;
    std::unordered_set<std::string> predicatesAppearingInUnaryPosConstr;
    bool crossComponentPredicatesAppearsInConstraint(const aspc::Rule&);
    bool constraintPredicatesBoundByExternalPreds(const aspc::Rule&);
    bool normalRulePredicatesBoundByHeadAndExternalPreds(const aspc::Rule&, bool);
    void rewriteComponentRulesAsConstraint();
    void rewriteRulesAsGeneratorRules();
    
    void rewriteComponentRuleAsConstraint(const aspc::Rule*);
    void buildPropagatorProgram();

    //domain rules methods
    void createDomainRulesFromProgram();
    void findAlwaysToCheckFalsePredicates();
    std::unordered_set<std::string> getToBoundVariablesForRule(aspc::Rule& rule, bool headAsExternal = true);
    void findPredicatesAppearingInUnaryPosConstraints();
public:
    std::unordered_set<std::string> getAlwaysToCheckFalsePredicates();
    static const std::string domainPredicatexPrefix;
    void crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& );
    PosCycleRewriter(){};
    void rewrite(aspc::Program*, const aspc::Program*, aspc::Program*);
    const aspc::Program& getGeneratorProgram() const;
    const aspc::Program& getPropagatorProgram() const;
    const aspc::Program& getDomainProgram() const;   
    const std::unordered_map<std::string,unsigned> getPredicateToId() const;
    const std::vector<std::string> getIdToPredicate() const;
    std::set<std::string> getPredicatesDefinedInPosCycleProgram();
    void rewriteRuleAsGeneratorsForPredicate(const aspc::Rule*, unsigned);
    //std::unordered_set<int> removePredicatesFromConstrID;
};

#endif /*POSCYCLEREWRITER*/