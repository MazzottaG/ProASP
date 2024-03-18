#include "PosCycleRewriter.h"

PosCycleRewriter::PosCycleRewriter(const aspc::Program& program):program(program){
    if(!program.isStratified()){
        std::cout <<"Lazy propagator can only work with stratified programs";
        exit(1);
    }
    dependencyManager.buildDependecyGraph(program);
    sccs = dependencyManager.getSCC();
    
    //compute recursive predicates
    for (std::vector<int>& scc : sccs){
        if(scc.size() > 1){
            for(unsigned predicateName : scc){
                recursivePredicates.insert(dependencyManager.getPredicateName(predicateName));
            }
        }else{//scc made by only one literal - check self recursion
            if(dependencyManager.existsEdge(scc[0], scc[0])){
                recursivePredicates.insert(dependencyManager.getPredicateName(scc[0]));
            }
        }
    }
    rewriteConstraintsAsGeneratorRules();
    rewriteComponentRulesAsConstraint();
    addNonRecursiveComponentsToGenerator();
}

const aspc::Program& PosCycleRewriter::getGeneratorProgram()const{
    return generatorProgram;
}

void PosCycleRewriter::rewriteConstraintsAsGeneratorRules(){
    //no constraint can contain two predicates in its body defined in two distinct components
    for(const aspc::Rule& rule : program.getRules()){
        if(rule.isConstraint() && crossComponentPredicatesAppearsInConstraint(rule)){
            std::cout << "Constraints cannot contain predicates defined by two different sccs of the positive cycle program\n";
            exit(1);
        }
            
    }

    for(const aspc::Rule& rule : program.getRules()){
        if(rule.isConstraint()){
            for(const aspc::Literal& lit : rule.getBodyLiterals()){
                if(recursivePredicates.count(lit.getPredicateName())){
                    rewriteConstraintAsGeneratorsForPredicate(&rule, dependencyManager.getPredicateId(lit.getPredicateName()));
                }
            }
        }
    }
}

void PosCycleRewriter::crossComponentPredicatesAppearInConstraintForProgram(const aspc::Program& prg) const{
    for(const aspc::Rule& rule : prg.getRules()){
        if(rule.isConstraint()){
            if(crossComponentPredicatesAppearsInConstraint(rule)){
                std::cout <<  "Constraints have literals in their body that belong to two different sccs of the positive cycle program\n";
                exit(1);
            }  
        }
    }
}

bool PosCycleRewriter::crossComponentPredicatesAppearsInConstraint(const aspc::Rule& constraint) const{
    //no scc found at the moment
    int currentSCC = -1;
    //std::set<std::string> headPredicates = program.getHeadPredicates();
    for(const aspc::Literal& lit : constraint.getBodyLiterals()){
        if(std::find(recursivePredicates.begin(), recursivePredicates.end(), lit.getPredicateName()) != recursivePredicates.end()){
            for(unsigned i = 0; i < sccs.size(); ++i){
                if(std::find(sccs[i].begin(), sccs[i].end(), dependencyManager.getPredicateToId().at(lit.getPredicateName())) != sccs[i].end()){
                    if(currentSCC != -1){
                        return true;
                    }
                    currentSCC = i;
                }
            }
        }
    }
    return false;
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
            genRulesBodyPredicates.push_back(constrBodyLiterals[i]);
            generatorProgram.addPredicate(constrBodyLiterals[i].getPredicateName(), constrBodyLiterals[i].getAriety());
            if(constrBodyLiterals[i].isPositiveLiteral()){
                for(const std::string& var : constrBodyLiterals[i].getVariables()){
                    posBodyVars.insert(var);
                }
            }
        
        }
    }

    std::vector<aspc::ArithmeticRelation> ineqs;
    std::vector<aspc::ArithmeticRelationWithAggregate> aggregates;

    for(unsigned i = 0; i < rule->getArithmeticRelations().size();i++){       
        ineqs.push_back(rule->getArithmeticRelations().at(i));
            
    }

    for(unsigned i = 0; i < rule->getArithmeticRelationsWithAggregate().size();i++){     
        aggregates.push_back(rule->getArithmeticRelationsWithAggregate().at(i));
    }
    
    for(aspc::Literal lit : genRulesHeadPredicates){
        for(const std::string& headVar : lit.getVariables()){
            if(!posBodyVars.count(headVar)){
                std::cout << "head variables of generator rules for lazy propragator must be bound by positive body vars";
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
    std::cout<<"-----\n";
}

//rewrite scc rules that define recursive predicates as constraints
//a(X,Z) :-a(X,Y), c(Z) not b(X, Y) -> :- a(X,Y), c(Z), not b(X, Y), not a(X,Z).
//Remember that program is stratified
void PosCycleRewriter::rewriteComponentRulesAsConstraint(){
    for(const aspc::Rule& rule : program.getRules()){
        if(!rule.isConstraint()){
            if(recursivePredicates.count(rule.getHead()[0].getPredicateName())){
                rewriteComponentRuleAsConstraint(&rule);
            }
        }
    }
}

void PosCycleRewriter::rewriteComponentRuleAsConstraint(const aspc::Rule* rule){
    std::cout <<"Rewriting of rule: \n";
    rule->print();
    std::cout <<"Into the following constraint:\n ";
    std::vector<aspc::Literal> constrBodyPredicates;

    std::vector<aspc::Literal> ruleBodyLiterals = rule->getBodyLiterals();

    for(unsigned i = 0; i < rule->getBodyLiterals().size(); ++i){
        constrBodyPredicates.push_back(ruleBodyLiterals[i]);
        generatorProgram.addPredicate(ruleBodyLiterals[i].getPredicateName(), ruleBodyLiterals[i].getAriety());
    }

    std::vector<aspc::ArithmeticRelation> ineqs;
    std::vector<aspc::ArithmeticRelationWithAggregate> aggregates;

    for(unsigned i = 0; i < rule->getArithmeticRelations().size();i++){       
        ineqs.push_back(rule->getArithmeticRelations().at(i));
            
    }

    for(unsigned i = 0; i < rule->getArithmeticRelationsWithAggregate().size();i++){     
        aggregates.push_back(rule->getArithmeticRelationsWithAggregate().at(i));
    }
    constrBodyPredicates.push_back(aspc::Literal(true, rule->getHead()[0]));
    aspc::Rule constraint({}, constrBodyPredicates, ineqs, aggregates, false, false); 
    constraint.print();
    generatorProgram.addRule(constraint);
        
    std::cout<<"-----\n";
}

//add components defined in P.P. that are non-recursive
//In this way the lazy propagator will now have to care about them
void PosCycleRewriter::addNonRecursiveComponentsToGenerator(){
    for(const aspc::Rule& rule : program.getRules()){
        if(!rule.isConstraint()){
            if(recursivePredicates.count(rule.getHead()[0].getPredicateName()) == 0){
                generatorProgram.addRule(rule);
            }
        }
    }
}

std::set<std::string> PosCycleRewriter::getPredicatesDefinedInPosCycleProgram(){
    return program.getHeadPredicates();
}

const std::unordered_map<std::string,unsigned> PosCycleRewriter::getPredicateToId()const {return dependencyManager.getPredicateToId();}
const std::vector<std::string> PosCycleRewriter::getIdToPredicate()const {return dependencyManager.getIdToPredicate();}