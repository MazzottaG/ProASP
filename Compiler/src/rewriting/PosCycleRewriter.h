#ifndef POSCYCLEREWRITER_H
#define POSCYCLEREWRITER_H

#include "../language/Program.h"
#include "../compilers/DependencyManager.h"
#include <algorithm>

class PosCycleRewriter{
private:
    const aspc::Program* program;
    const aspc::Program* addedConstraintsProgram;
    aspc::Program generatorProgram;
    aspc::Program propagatorProgram;
    DependencyManager dependencyManager;
    std::vector<std::vector<int>> sccs;
    //std::unordered_set<std::string> recursivePredicates;
    std::set<std::string> predicatesDefinedInPosCycleProgram;
    bool crossComponentPredicatesAppearsInConstraint(const aspc::Rule&);
    bool constraintPredicatesBoundByExternalPreds(const aspc::Rule&);
    void rewriteComponentRulesAsConstraint();
    void rewriteConstraintsAsGeneratorRules();
    
    void rewriteComponentRuleAsConstraint(const aspc::Rule*);
    void buildPropagatorProgram();


public:
    void crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& );
    PosCycleRewriter(){};
    void rewrite(const aspc::Program*, const aspc::Program*);
    const aspc::Program& getGeneratorProgram() const;
    const aspc::Program& getPropagatorProgram() const;    
    const std::unordered_map<std::string,unsigned> getPredicateToId() const;
    const std::vector<std::string> getIdToPredicate() const;
    std::set<std::string> getPredicatesDefinedInPosCycleProgram();
    void rewriteConstraintAsGeneratorsForPredicate(const aspc::Rule*, unsigned);
    //std::unordered_set<int> removePredicatesFromConstrID;
};

#endif /*POSCYCLEREWRITER*/