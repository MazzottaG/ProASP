#include "PosCycleRewriter.h"


const std::string PosCycleRewriter::domainPredicatexPrefix = "DomL_";
void PosCycleRewriter::rewrite(aspc::Program* propProgram, const aspc::Program* prg){
    this->programPP = prg;
    //this->addedConstraintsProgram = constraintsProgram;
    this->propProgram = propProgram;
    if(!programPP->isStratified()){
        std::cout <<"Lazy propagator can only work with stratified programs\n";
        exit(180);
    }
    // for(const aspc::Rule& rule : addedConstraintsProgram->getRules()){
    //     assert(rule.isConstraint());
    // }
    for(const aspc::Rule& rule : prg->getRules()){
        if(rule.getArithmeticRelationsWithAggregate().size() != 0){
            std::cout << "Lazy propagator does not support aggregates\n";
            exit(180);
        }
    }
    dependencyManager.buildDependecyGraph(*programPP);
    sccs = dependencyManager.getSCC();
    
    predicatesDefinedInPosCycleProgram = programPP->getHeadPredicates();
    //build normal-stratified program that will be encoded in lazy propagators
    buildPropagatorProgram();
    findAlwaysToCheckFalsePredicates();
    //rewrite constraints from PP
    createDomainRulesFromProgram();
    rewriteRulesAsGeneratorRules();
    
    for(const aspc::Rule& rule : propagatorProgram.getRules()){
        //Assuming only one head
        if(!rule.isConstraint() && predicatesAppearingInUnaryPosConstr.count(rule.getHead().at(0).getPredicateName()) == 0){
            if(!normalRulePredicatesBoundByHeadAndExternalPreds(rule, true)){
                std::cout <<"Error on rule: ";
                rule.print();
                std::cout <<"Nomal rules of lazy program must have lazy predicate variables bound by external predicates and domain predicates\n";
                exit(180);
            }
        }
    }
}

const aspc::Program& PosCycleRewriter::getGeneratorProgram() const{
    return generatorProgram;
}

const aspc::Program& PosCycleRewriter::getPropagatorProgram() const{
    return propagatorProgram;
}
const aspc::Program& PosCycleRewriter::getDomainProgram() const{
    return domainProgram;
}

std::unordered_set<std::string> PosCycleRewriter::getAlwaysToCheckFalsePredicates(){
    return alwaysToCheckFalsePredicates;
}
void PosCycleRewriter::rewriteRulesAsGeneratorRules(){
    //no constraint can contain two predicates in its body defined in two distinct components
    //except when external predicates (predicates not define in P.P.) bind all the variables
    // for(const aspc::Rule& rule : programPP->getRules()){
    //     if(rule.isConstraint() && crossComponentPredicatesAppearsInConstraint(rule)){
    //         std::cout << "Constraints cannot contain predicates defined by two different sccs of the positive cycle program\nIn case this is needed, all variables must be bound by predicates not defined in positive cycle program\n";
    //         exit(180);
    //     }
            
    // }

    // for(const aspc::Rule& rule : programPP->getRules()){
    //     if(rule.isConstraint()){
    //         for(const aspc::Literal& lit : rule.getBodyLiterals()){
    //             if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
    //                 rewriteRuleAsGeneratorsForPredicate(&rule, dependencyManager.getPredicateId(lit.getPredicateName()));
    //             }
    //         }
    //     }
    // }
    
    for(const aspc::Rule& rule : propProgram->getRules()){
        for(const aspc::Literal& lit : rule.getBodyLiterals()){
            if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
                rewriteRuleAsGeneratorsForPredicate(&rule, dependencyManager.getPredicateId(lit.getPredicateName()));
            }
        }
    }
}

// void PosCycleRewriter::crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& prg){
//     for(const aspc::Rule& rule : prg.getRules()){
//         if(rule.isConstraint()){
//             if(crossComponentPredicatesAppearsInConstraint(rule)){
//                 std::cout <<  "Constraints have literals in their body that belong to two different sccs of the positive cycle program\n";
//                 exit(180);
//             }  
//         }
//     }
// }

bool PosCycleRewriter::crossComponentPredicatesAppearsInConstraint(const aspc::Rule& constraint){
    std::unordered_set<int> sccsForConstraint;
    for(const aspc::Literal& lit : constraint.getBodyLiterals()){
        if(std::find(predicatesDefinedInPosCycleProgram.begin(), predicatesDefinedInPosCycleProgram.end(), lit.getPredicateName()) != predicatesDefinedInPosCycleProgram.end()){
            for(unsigned i = 0; i < sccs.size(); ++i){
                if(std::find(sccs[i].begin(), sccs[i].end(), dependencyManager.getPredicateToId().at(lit.getPredicateName())) != sccs[i].end()){
                    sccsForConstraint.insert(i);
                    if(sccsForConstraint.size() > 1){
                        if(!constraintPredicatesBoundByExternalPreds(constraint)) return true;
                        //else removePredicatesFromConstrID.insert(constraint.getRuleId());
                    }
                }
            }
        }
    }
    return false;
}

bool PosCycleRewriter::constraintPredicatesBoundByExternalPreds(const aspc::Rule& constraint){
    std::unordered_set<std::string> posPredicatesVariables;
    std::unordered_set<std::string> externalPredicatesVariables;
    for(const aspc::Literal& lit : constraint.getBodyLiterals()){
        if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
            for(const std::string& var: lit.getVariables()){
                posPredicatesVariables.insert(var);
            }
        }else{
            for(const std::string& var: lit.getVariables()){
                externalPredicatesVariables.insert(var);
            }
        }
    }

    //add bound vars from arithmetic relations
    for(const aspc::ArithmeticRelation& rel : constraint.getArithmeticRelations())
    {
        if(rel.isBoundedValueAssignment(externalPredicatesVariables)){
            std::string assignedVar =  rel.getAssignedVariable(externalPredicatesVariables);
            externalPredicatesVariables.insert(assignedVar);
        }
    }
    
    for(const std::string& var : posPredicatesVariables){
        if(!externalPredicatesVariables.count(var))
            return false;
    }
    return true;
}

bool PosCycleRewriter::normalRulePredicatesBoundByHeadAndExternalPreds(const aspc::Rule& rule, bool allowArithHeadBound){
    std::unordered_set<std::string> posPredicatesVariables;
    std::unordered_set<std::string> externalPredicatesVariables;
    std::unordered_set<std::string> externalAndHeadPredicatesVariables;
    for(const aspc::Atom& head : rule.getHead()){
        for(unsigned i = 0; i < head.getAriety(); ++i){
            posPredicatesVariables.insert(head.getTermAt(i));
            externalAndHeadPredicatesVariables.insert(head.getTermAt(i));
        }
    }

    for(const aspc::Literal& lit : rule.getBodyLiterals()){
        if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
            for(const std::string& var : lit.getVariables()){
                posPredicatesVariables.insert(var);
            }
        }else{
            for(const std::string& var : lit.getVariables()){
                externalPredicatesVariables.insert(var);
                externalAndHeadPredicatesVariables.insert(var);

            }
        }
    }

    //add bound vars from arithmetic relations
    bool assigned;
    do{
        assigned = false;
        for(const aspc::ArithmeticRelation& rel : rule.getArithmeticRelations()){
            if(allowArithHeadBound){
                if(rel.isBoundedValueAssignment(externalAndHeadPredicatesVariables)){
                    std::string assignedVar =  rel.getAssignedVariable(externalAndHeadPredicatesVariables);
                    assigned = true;
                    externalAndHeadPredicatesVariables.insert(assignedVar);
                }
            }else{
                if(rel.isBoundedValueAssignment(externalPredicatesVariables)){
                    std::string assignedVar =  rel.getAssignedVariable(externalPredicatesVariables);
                    if(!externalAndHeadPredicatesVariables.count(assignedVar))
                        assigned = true;
                    externalAndHeadPredicatesVariables.insert(assignedVar);
                    externalPredicatesVariables.insert(assignedVar);
                }
            }
        }
    }while(assigned);
    
    for(const std::string& var : posPredicatesVariables){
        if(!externalAndHeadPredicatesVariables.count(var)){
            return false;
        }
    }
    return true;
}

void PosCycleRewriter::findAlwaysToCheckFalsePredicates(){
    std::unordered_set<std::string> lazyPredicateNegatedVars;
    std::unordered_set<std::string> lazyPredicatePositiveVars;
    for(unsigned i = 0; i < 2; ++i){
        std::vector<aspc::Rule>& rules = i == 0 ? propagatorProgram.getRules() : propProgram->getRules();
        for(aspc::Rule r : rules){
            if(!r.isConstraint()){
                for(const aspc::Literal lit : r.getBodyLiterals()){
                    if(lit.isNegated() && predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
                        for(std::string var : lit.getVariables()){
                            lazyPredicateNegatedVars.insert(var);
                        }
                    }
                    if(!lit.isNegated() && predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
                        for(std::string var : lit.getVariables()){
                            lazyPredicatePositiveVars.insert(var);
                        }
                    }
                }
                std::unordered_set<std::string> nonBoundedVars;
                for(std::string var : lazyPredicateNegatedVars){
                    if(!lazyPredicatePositiveVars.count(var)){
                        nonBoundedVars.insert(var);
                    }

                }
                //head predicates for rules s.t. nonBoundedVars is not empty are always to check
                //predicates that contain variables that are in nonBoundedVars
                //are as well added in always to check
                if(i == 0 && nonBoundedVars.size() > 0){
                    for(const aspc::Atom h : r.getHead()){
                        alwaysToCheckFalsePredicates.insert(h.getPredicateName());
                    }
                }

                for(const aspc::Literal lit : r.getBodyLiterals()){
                    for(std::string var : lit.getVariables()){
                        if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName()) && nonBoundedVars.count(var)){
                            alwaysToCheckFalsePredicates.insert(lit.getPredicateName());
                        }
                    }
                    
                }
                lazyPredicateNegatedVars.clear();
                lazyPredicatePositiveVars.clear();
            }
        }
    } 
}

 //:-a, b where a is involved in recursion becomes a :- b (needed for symbols generation)
void PosCycleRewriter::rewriteRuleAsGeneratorsForPredicate(const aspc::Rule* rule, unsigned predicateName){
    std::cout <<"Rewriting of rule: \n";
    rule->print();
    std::cout <<"Into the following generator rules:\n ";
    std::vector<aspc::Literal> genRulesHeadPredicates;
    std::vector<aspc::Literal> genRulesBodyPredicates;

    std::vector<aspc::Literal> constrBodyLiterals = rule->getBodyLiterals();
    std::unordered_set<std::string> posBodyVars;

    for(unsigned i = 0; i < rule->getBodyLiterals().size(); ++i){
        if(constrBodyLiterals[i].getPredicateName() == dependencyManager.getPredicateName(predicateName)){
            genRulesHeadPredicates.push_back(constrBodyLiterals[i]);
            generatorProgram.addPredicate(constrBodyLiterals[i].getPredicateName(), constrBodyLiterals[i].getAriety());
        }
        else{
            if(!predicatesDefinedInPosCycleProgram.count(constrBodyLiterals[i].getPredicateName())){   
                genRulesBodyPredicates.push_back(constrBodyLiterals[i]);
                generatorProgram.addPredicate(constrBodyLiterals[i].getPredicateName(), constrBodyLiterals[i].getAriety());
                if(constrBodyLiterals[i].isPositiveLiteral()){
                    for(const std::string& var : constrBodyLiterals[i].getVariables()){
                        posBodyVars.insert(var);
                    }
                }
            }
        }
    }

    std::vector<aspc::ArithmeticRelation> ineqs;
    std::vector<aspc::ArithmeticRelationWithAggregate> aggregates;
    bool assigned;
    do{
        assigned = false;
        for(unsigned i = 0; i < rule->getArithmeticRelations().size();i++){       
            ineqs.push_back(rule->getArithmeticRelations().at(i));
            if(rule->getArithmeticRelations().at(i).isBoundedValueAssignment(posBodyVars)){
                std::string assignedVar =  rule->getArithmeticRelations().at(i).getAssignedVariable(posBodyVars);
                if(!posBodyVars.count(assignedVar))
                    assigned = true;
                posBodyVars.insert(assignedVar);
            }
        }
    }while(assigned);

    for(unsigned i = 0; i < rule->getArithmeticRelationsWithAggregate().size();i++){     
        aggregates.push_back(rule->getArithmeticRelationsWithAggregate().at(i));
    }
    //if(!genRulesBodyPredicates.empty()){
    for(aspc::Literal lit : genRulesHeadPredicates){
        // for(const std::string& headVar : lit.getVariables()){
        //     if(!posBodyVars.count(headVar)){
        //         std::cout << "head variables of generator rules for lazy propragator must be bound by positive body vars\n";
        //         exit(1);
        //     }
        // }
        const aspc::Atom a(lit.getPredicateName(), lit.getTerms());
        std::vector<aspc::Atom> head;
        head.push_back(a);
        aspc::Rule generatorRule(head, genRulesBodyPredicates, ineqs, aggregates, false, false); 
        generatorRule.print();
        generatorProgram.addRule(generatorRule);
        
    }
    //}//else constraint contains only P.P.-defined predicates (no generation of symbols is needed)
    std::cout<<"-----\n";
}

//rewrite scc rules that define recursive predicates as constraints
//a(X,Z) :-a(X,Y), c(Z) not b(X, Y) -> :- a(X,Y), c(Z), not b(X, Y), not a(X,Z).
//Remember that program is stratified
void PosCycleRewriter::rewriteComponentRulesAsConstraint(){
    for(const aspc::Rule& rule : programPP->getRules()){
        if(!rule.isConstraint()){
            rewriteComponentRuleAsConstraint(&rule);
        }
    }
}

void PosCycleRewriter::rewriteComponentRuleAsConstraint(const aspc::Rule* rule){
    std::cout <<"Rewriting of rule: \n";
    rule->print();
    std::cout <<"Into the following constraint:\n ";
    std::vector<aspc::Literal> constrBodyPredicates;

    std::vector<aspc::Literal> ruleBodyLiterals = rule->getBodyLiterals();
    //if rule has the same literal with the same variables in head and in body
    //with the same sign. The constraint that will be generated is inconsistent by def
    for(const aspc::Atom& head : rule->getHead()){
        for(const aspc::Literal& lit : rule->getBodyLiterals()){
            if(lit.getPredicateName() == head.getPredicateName() && lit.isPositiveLiteral()){
                aspc::Literal headLit(false, head);
                if(headLit == lit){
                    std::cout <<"rewritten constraint would lead to inconsistency\n";
                    return;
                }
            }
        }
    }

    for(unsigned i = 0; i < rule->getBodyLiterals().size(); ++i){
        constrBodyPredicates.push_back(ruleBodyLiterals[i]);
        generatorProgram.addPredicate(ruleBodyLiterals[i].getPredicateName(), ruleBodyLiterals[i].getAriety());
    }

    std::vector<aspc::ArithmeticRelation> ineqs;

    for(unsigned i = 0; i < rule->getArithmeticRelations().size();i++){       
        ineqs.push_back(rule->getArithmeticRelations().at(i));
            
    }
    for(const auto& head : rule->getHead()){
        constrBodyPredicates.push_back(aspc::Literal(true, head));
        aspc::Rule constraint({}, constrBodyPredicates, ineqs, {}, false, false); 
        constraint.print();
        generatorProgram.addRule(constraint);
        constrBodyPredicates.pop_back();
    }
        
    std::cout<<"-----\n";
}

//propagator program is made of all the rules that were not constraints inside the 
//original P.P.
void PosCycleRewriter::buildPropagatorProgram(){
    for(const aspc::Rule& rule : programPP->getRules()){
        //if(!rule.isConstraint()){
            propagatorProgram.addRule(rule);
        //}
    }
}

std::unordered_set<std::string> PosCycleRewriter::getToBoundVariablesForRule(aspc::Rule& rule, bool headAsExternal){
    //if rule requires bound then add in requiring domain rules
    //a rule requires bound if variables from external predicates leave unbounded some variables of P.P. preicates
    std::unordered_set<std::string> externalVariables;
    std::unordered_set<std::string> toBoundVariables;
    std::cout <<"HeadAsExternal: "<< headAsExternal << "\n";
    for(const aspc::Atom& head : rule.getHead()){
        for(unsigned i = 0; i < head.getAriety(); ++i){
            if(head.isVariableTermAt(i)){
                if(headAsExternal)
                    externalVariables.insert(head.getTermAt(i));
                else
                    toBoundVariables.insert(head.getTermAt(i));
            }
        }
    }
    for(const aspc::Literal& lit : rule.getBodyLiterals()){
        if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
            for(std::string var : lit.getVariables()){
                if(!externalVariables.count(var)){
                    toBoundVariables.insert(var);
                }
            }
        }else{
            for(std::string var : lit.getVariables()){
                if(!lit.isNegated()){
                    externalVariables.insert(var);
                    toBoundVariables.erase(var);
                }
            }
        }
    }
    bool assigned;
    do{
        assigned = false;
        //add bound vars from arithmetic relations
        for(const aspc::ArithmeticRelation& rel : rule.getArithmeticRelations()){
            if(rel.isBoundedValueAssignment(externalVariables)){
                std::string assignedVar = rel.getAssignedVariable(externalVariables);
                if(!externalVariables.count(assignedVar)){
                    externalVariables.insert(assignedVar);
                    assigned = true;
                }
                toBoundVariables.erase(assignedVar);
            }
        }
        if(toBoundVariables.size() == 0)
            break;
    }while(assigned);

    return toBoundVariables;
}

void PosCycleRewriter::findPredicatesAppearingInUnaryPosConstraints(){
    for(unsigned programToAddDomainAtoms  = 0; programToAddDomainAtoms < 2; ++programToAddDomainAtoms){
        aspc::Program* currentProgram;
        if(programToAddDomainAtoms == 0) currentProgram = propProgram;
        else if(programToAddDomainAtoms == 1) currentProgram = &propagatorProgram;
        //else currentProgram = addedConstraintsProgram;
        std::vector<aspc::Rule>& rules = currentProgram->getRules();
        for(aspc::Rule& rule : rules){
            if(rule.isConstraint() && rule.getFormulas().size() == 1){
                if(rule.getBodyLiterals().size() == 1){
                    aspc::Literal lit = rule.getBodyLiterals().at(0);
                    if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName()) && !lit.isNegated() && lit.getAriety() == 0)
                        predicatesAppearingInUnaryPosConstr.insert(lit.getPredicateName());
                }
            }
        }
    } 
}

void PosCycleRewriter::createDomainRulesFromProgram(){
    
    //<predName, {pos_1, ..., pos_n}> for every position in the set domain rules must be written
    std::unordered_map<std::string, std::unordered_set<int>> predicateAndTermRequiringDomain;
    
    
    findPredicatesAppearingInUnaryPosConstraints();
    //if rule requires bound then add in requiring domain rules
    //a rule requires bound if variables from external predicates leave unbounded some variables of P.P. preicates
    std::unordered_set<std::string> toBoundVariables;
    
    //find required domain predicates
    //after required domain predicates are found in the first iteration,
    //put additional domainAtoms considering head variables no longer as external vars (in this way domain rules will be safe)
    for(unsigned programToAddDomainAtoms  = 0; programToAddDomainAtoms < 2; ++programToAddDomainAtoms){
        aspc::Program* currentProgram;
        if(programToAddDomainAtoms == 0) currentProgram = propProgram;
        else if(programToAddDomainAtoms == 1) currentProgram = &propagatorProgram;
        //else currentProgram = addedConstraintsProgram;
        std::vector<aspc::Rule>& rules = currentProgram->getRules();
        for(aspc::Rule& rule : rules){
            //normal rules coming from to-ground and to-lazy have to be rewritten as generator rules
            //if they have P.P. predicates in body and therefore head vars are considered as internal
            //lazy constraints do not require domain predicates
            if(programToAddDomainAtoms == 1 && rule.isConstraint())
                continue;
            //Assuming only one head
            if(!rule.isConstraint()){
                if( predicatesAppearingInUnaryPosConstr.count(rule.getHead().at(0).getPredicateName()) > 0)
                    continue;
            }
            toBoundVariables = getToBoundVariablesForRule(rule, programToAddDomainAtoms != 0);
            std::cout <<"Rule \t";
            rule.print();
            std::cout <<"requires a num of bounds: "<< toBoundVariables.size()<<"\n";
            //some variable needs bound: save terms that require domain and complete rule with domain predicates definig such terms
            if(toBoundVariables.size() > 0){
                std::vector<aspc::Literal> toAddDomain;
                for(const aspc::Literal& lit : rule.getBodyLiterals()){
                    if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
                        int termIdx = 0;
                        for(const std::string var : lit.getTerms()){
                            if(toBoundVariables.count(var)){
                                if(!predicateAndTermRequiringDomain.count(lit.getPredicateName()))
                                    predicateAndTermRequiringDomain.emplace(std::make_pair(lit.getPredicateName(), std::unordered_set<int>())); 
                                
                                predicateAndTermRequiringDomain.at(lit.getPredicateName()).insert(termIdx);
                            }
                        termIdx++;
                        }
                    }
                }
            }
        }
    }

    //Add required domain atoms in the body of 
    //normal rules of lazy program
    for(aspc::Rule& rule : propagatorProgram.getRules()){
        if(!rule.isConstraint()){
            std::vector<aspc::Literal> toAddDomain;
            for(const aspc::Literal& lit : rule.getBodyLiterals()){
                if(predicateAndTermRequiringDomain.count(lit.getPredicateName())){
                    for(int idx : predicateAndTermRequiringDomain[lit.getPredicateName()]){
                        aspc::Literal domainLiteral(domainPredicatexPrefix + lit.getPredicateName() + std::to_string(idx), false);
                        domainLiteral.addTerm(lit.getTermAt(idx));
                        toAddDomain.push_back(domainLiteral);
                    }
                }
            }
            for(int i = 0; i< toAddDomain.size(); ++i)
                rule.addBodyLiteral(toAddDomain[i]);
        }
    }

    //add required domain atoms in body of constraints
    for(aspc::Rule& rule : propProgram->getRules()){
        std::vector<aspc::Literal> toAddDomain;
        for(const aspc::Literal& lit : rule.getBodyLiterals()){
            if(predicateAndTermRequiringDomain.count(lit.getPredicateName())){
                for(int idx : predicateAndTermRequiringDomain[lit.getPredicateName()]){
                    aspc::Literal domainLiteral(domainPredicatexPrefix + lit.getPredicateName() + std::to_string(idx), false);
                    domainLiteral.addTerm(lit.getTermAt(idx));
                    toAddDomain.push_back(domainLiteral);
                }
            }
        }
        for(int i = 0; i< toAddDomain.size(); ++i)
            rule.addBodyLiteral(toAddDomain[i]);
    }

    //create domain rules to be added in generator program
    //for every rule that defines a predicate requiring domain, add new rules
    //that define a projection of such predicates into domain predicates
    for(aspc::Rule& rule : propagatorProgram.getRules()){
        if(rule.isConstraint())
            continue;
        std::cout <<"Creating domain rule from: ";
        rule.print();
        //TODO if head has multiple atoms domain rules are subdivided into more compilations
        for(const aspc::Atom& head : rule.getHead()){
            //create domain rule if rule defines a predicate that requires domain
            std::vector<aspc::Atom> domainRuleHeads;
            std::vector<aspc::Literal> domainRuleBody;
            if(predicateAndTermRequiringDomain.count(head.getPredicateName())){
                std::cout <<"Considering predicate " << head.getPredicateName() << "\n";
                int itRuleBody = 0;
                for(int idx : predicateAndTermRequiringDomain.at(head.getPredicateName())){
                    std::cout <<"\tidx: " << idx << "\n";
                    std::string headVar = head.getTermAt(idx);
                    bool isSafe = false;
                    aspc::Atom domainRuleHead(domainPredicatexPrefix + head.getPredicateName() + std::to_string(idx));
                    domainRuleHead.setTerms({headVar});
                    domainRuleHeads.push_back(domainRuleHead);
                    if(itRuleBody == 0){
                        std::unordered_set<std::string> boundVars;
                        for(aspc::Literal lit: rule.getBodyLiterals()){
                            if(head.getPredicateName() != lit.getPredicateName()){
                                domainRuleBody.push_back(lit);
                                if(lit.isPositiveLiteral()){
                                    for(std::string variable : lit.getVariables()){
                                        boundVars.insert(variable);
                                    }
                                }
                            }
                        }
                        //check that builtins can bound var
                        if(!boundVars.count(headVar)){
                            bool assigned;
                            do{
                                assigned = false;
                                for(const aspc::ArithmeticRelation& rel : rule.getArithmeticRelations()){
                                    if(rel.isBoundedValueAssignment(boundVars)){
                                        std::string assignedVar =  rel.getAssignedVariable(boundVars);
                                        assigned = true;
                                        boundVars.insert(assignedVar);
                                    }
                                }
                            }while(assigned);
                        }
                    }
                    itRuleBody++;
                }
                
                aspc::Rule domainRule(domainRuleHeads, domainRuleBody, rule.getArithmeticRelations(), false);
                domainProgram.addRule(domainRule);
                std::cout <<"Created domain rule: ";
                domainRule.print();
            }
        }
    }
}

std::set<std::string> PosCycleRewriter::getPredicatesDefinedInPosCycleProgram(){
    return predicatesDefinedInPosCycleProgram;
}

const std::unordered_map<std::string,unsigned> PosCycleRewriter::getPredicateToId()const {return dependencyManager.getPredicateToId();}
const std::vector<std::string> PosCycleRewriter::getIdToPredicate()const {return dependencyManager.getIdToPredicate();}
