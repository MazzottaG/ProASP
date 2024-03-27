#include "PosCycleRewriter.h"


void PosCycleRewriter::rewrite(const aspc::Program* prg){
    this->program = prg;
    if(!program->isStratified()){
        std::cout <<"Lazy propagator can only work with stratified programs\n";
        exit(180);
    }
    dependencyManager.buildDependecyGraph(*program);
    sccs = dependencyManager.getSCC();
    
    //compute recursive predicates
    // for (std::vector<int>& scc : sccs){
    //     if(scc.size() > 1){
    //         for(unsigned predicateName : scc){
    //             recursivePredicates.insert(dependencyManager.getPredicateName(predicateName));
    //         }
    //     }else{//scc made by only one literal - check self recursion
    //         if(dependencyManager.existsEdge(scc[0], scc[0])){
    //             recursivePredicates.insert(dependencyManager.getPredicateName(scc[0]));
    //         }
    //     }
    // }
    predicatesDefinedInPosCycleProgram = program->getHeadPredicates();
    rewriteConstraintsAsGeneratorRules();
    //rewriteComponentRulesAsConstraint();
    buildPropagatorProgram();
}

const aspc::Program& PosCycleRewriter::getGeneratorProgram() const{
    return generatorProgram;
}

const aspc::Program& PosCycleRewriter::getPropagatorProgram() const{
    return propagatorProgram;
}

void PosCycleRewriter::rewriteConstraintsAsGeneratorRules(){
    //no constraint can contain two predicates in its body defined in two distinct components
    //except when external predicates (predicates not define in P.P.) bind all the variables
    for(const aspc::Rule& rule : program->getRules()){
        if(rule.isConstraint() && crossComponentPredicatesAppearsInConstraint(rule)){
            std::cout << "Constraints cannot contain predicates defined by two different sccs of the positive cycle program\nIn case this is needed, all variables must be bound by predicates not defined in positive cycle program\n";
            exit(180);
        }
            
    }

    for(const aspc::Rule& rule : program->getRules()){
        if(rule.isConstraint()){
            for(const aspc::Literal& lit : rule.getBodyLiterals()){
                if(predicatesDefinedInPosCycleProgram.count(lit.getPredicateName())){
                    rewriteConstraintAsGeneratorsForPredicate(&rule, dependencyManager.getPredicateId(lit.getPredicateName()));
                }
            }
        }
    }
}

void PosCycleRewriter::crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& prg){
    for(const aspc::Rule& rule : prg.getRules()){
        if(rule.isConstraint()){
            if(crossComponentPredicatesAppearsInConstraint(rule)){
                std::cout <<  "Constraints have literals in their body that belong to two different sccs of the positive cycle program\n";
                exit(180);
            }  
        }
    }
}

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

 //:-a, b where a is involved in recursion becomes a :- b (needed for symbols generation)
void PosCycleRewriter::rewriteConstraintAsGeneratorsForPredicate(const aspc::Rule* rule, unsigned predicateName){
    std::cout <<"Rewriting of constraint: \n";
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

    for(unsigned i = 0; i < rule->getArithmeticRelations().size();i++){       
        ineqs.push_back(rule->getArithmeticRelations().at(i));
        if(rule->getArithmeticRelations().at(i).isBoundedValueAssignment(posBodyVars)){
            std::string assignedVar =  rule->getArithmeticRelations().at(i).getAssignedVariable(posBodyVars);
            posBodyVars.insert(assignedVar);
        }
    }

    for(unsigned i = 0; i < rule->getArithmeticRelationsWithAggregate().size();i++){     
        aggregates.push_back(rule->getArithmeticRelationsWithAggregate().at(i));
    }
    if(!genRulesBodyPredicates.empty()){
        for(aspc::Literal lit : genRulesHeadPredicates){
            for(const std::string& headVar : lit.getVariables()){
                if(!posBodyVars.count(headVar)){
                    std::cout << "head variables of generator rules for lazy propragator must be bound by positive body vars\n";
                    exit(1);
                }
            }
            const aspc::Atom a(lit.getPredicateName(), lit.getTerms());
            std::vector<aspc::Atom> head;
            head.push_back(a);
            aspc::Rule generatorRule(head, genRulesBodyPredicates, ineqs, aggregates, false, false); 
            generatorRule.print();
            generatorProgram.addRule(generatorRule);
            
        }
    }//else constraint contains only P.P.-defined predicates (no generation of symbols is needed)
    std::cout<<"-----\n";
}

//rewrite scc rules that define recursive predicates as constraints
//a(X,Z) :-a(X,Y), c(Z) not b(X, Y) -> :- a(X,Y), c(Z), not b(X, Y), not a(X,Z).
//Remember that program is stratified
void PosCycleRewriter::rewriteComponentRulesAsConstraint(){
    for(const aspc::Rule& rule : program->getRules()){
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
    for(const aspc::Rule& rule : program->getRules()){
        if(!rule.isConstraint()){
            //bool toAdd = true;
            propagatorProgram.addRule(rule);
            // for(auto& pred : rule.getHead()){
            //     //if(recursivePredicates.count(pred.getPredicateName()) == 0){
            //     if(toAdd){
            //         generatorProgram.addRule(aspc::Rule(rule));
            //         toAdd = false;
            //     }
            //     //}
            // }
            // if(toAdd){
            //     std::cout <<"ADDING\n";
            //     propagatorProgram.addRule(aspc::Rule(rule));
            // }
        }
    }
}

std::set<std::string> PosCycleRewriter::getPredicatesDefinedInPosCycleProgram(){
    return predicatesDefinedInPosCycleProgram;
}

const std::unordered_map<std::string,unsigned> PosCycleRewriter::getPredicateToId()const {return dependencyManager.getPredicateToId();}
const std::vector<std::string> PosCycleRewriter::getIdToPredicate()const {return dependencyManager.getIdToPredicate();}
