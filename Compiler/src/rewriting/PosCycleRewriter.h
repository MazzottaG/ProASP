#ifndef POSCYCLEPROGRAM_H
#define POSCYCLEPROGRAM_H

#include "../language/Program.h"
#include "../compilers/DependencyManager.h"
#include <algorithm>

class PosCycleRewriter{
private:
    aspc::Program program;
    aspc::Program generatorProgram;
    DependencyManager dependencyManager;
    std::vector<std::vector<int>> sccs;
    std::unordered_set<std::string> recursivePredicates;
    bool crossComponentPredicatesAppearsInConstraint(const aspc::Rule&) const;
    void rewriteComponentRulesAsConstraint();
    void rewriteConstraintsAsGeneratorRules();
    void rewriteConstraintAsGeneratorsForPredicate(const aspc::Rule*, unsigned);
    void rewriteComponentRuleAsConstraint(const aspc::Rule*);
    void addNonRecursiveComponentsToGenerator();


public:
    void crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& )const;
    PosCycleRewriter(const aspc::Program&);
    const aspc::Program& getGeneratorProgram() const;    
    const std::unordered_map<std::string,unsigned> getPredicateToId() const;
    const std::vector<std::string> getIdToPredicate() const;
    std::set<std::string> getPredicatesDefinedInPosCycleProgram();
};

#endif /*POSCYCLEPROGRAM*/