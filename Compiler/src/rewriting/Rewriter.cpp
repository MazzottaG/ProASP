#include "Rewriter.h"
void Rewriter::addOriginalConstraint(){
    for(unsigned i=0; i<program.getRulesSize();i++){
        auto rule = program.getRule(i);
        if(rule.isConstraint()){
            propagatorsProgram.addRule(rule);
        }
    }
}
void Rewriter::addToGroundRule(const aspc::Rule& r){
    generatorProgram.addRule(r);
}
void Rewriter::reduceToSigleHeadForPredicate(){
    for(std::string predicate:predicateNames){
        auto rules = program.getRulesForPredicate(predicate);
        if(rules.size()>1){
            unsigned usedSupportPredicates=supportPredicates.size();
            unsigned ariety=0;
            for(int ruleIndex : rules){
                const aspc::Rule* rule = &program.getRule(ruleIndex);
                std::string supportPredicate = "sup_"+std::to_string(supportPredicates.size());
                supportPredicateId[supportPredicate]=supportPredicates.size();
                supportPredicates.push_back(supportPredicate);
                
                if(ariety == 0)
                    ariety=rule->getHead()[0].getTerms().size();
                else if(ariety != rule->getHead()[0].getTerms().size()){
                    std::cout << "Error using same predicate name with different ariety value"<<std::endl;
                    exit(180);
                }
                aspc::Rule r(
                    std::vector<aspc::Atom>({aspc::Atom(supportPredicate, rule->getHead()[0].getTerms())}),
                    rule->getBodyLiterals(),
                    rule->getArithmeticRelations(),
                    false);
                std::vector<std::string> terms;
                for(int i=0;i<ariety;i++) terms.push_back("X_"+std::to_string(i));
                aspc::Rule constraint(
                    {},
                    {aspc::Literal(false,aspc::Atom(supportPredicate,terms)),aspc::Literal(true,aspc::Atom(predicate,terms))},
                    {},
                    false);
                singleHeadForPredicate.addRule(constraint);
                labeledSingleHeadRules.push_back(true);
                singleHeadForPredicate.addRule(r);
                labeledSingleHeadRules.push_back(false);

                // adding rule a :- sup in generator only
                aspc::Rule supRule(
                    {aspc::Atom(predicate,terms)},
                    {aspc::Literal(false,aspc::Atom(supportPredicate,terms))},
                    {},
                    false);
                generatorProgram.addRule(supRule);
            }
            std::vector<aspc::Literal> constraintLiterals;
            std::vector<std::string> terms;
            for(int i=0;i<ariety;i++) terms.push_back("X_"+std::to_string(i));
            constraintLiterals.push_back(aspc::Literal(false,aspc::Atom(predicate,terms)));
            for(unsigned i=usedSupportPredicates;i<supportPredicates.size();i++){
                constraintLiterals.push_back(aspc::Literal(true,aspc::Atom("sup_"+std::to_string(i),terms)));
            }
            aspc::Rule constraint(
                {},
                constraintLiterals,
                {},
                false);
            constraint.setSupportAtom(0);
            singleHeadForPredicate.addRule(constraint);
            labeledSingleHeadRules.push_back(false);
        }else if(rules.size() == 1){
            singleHeadForPredicate.addRule(program.getRule(rules[0]));
            labeledSingleHeadRules.push_back(false);
        }
    }
    for(unsigned ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
        if(program.getRule(ruleId).isConstraint()){
            singleHeadForPredicate.addRule(program.getRule(ruleId));
            labeledSingleHeadRules.push_back(false);
        }
    }
}
void Rewriter::computeGlobalPredicates(){
    for(std::string predicate : supportPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }
    for(std::string predicate : auxPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }
}
void Rewriter::computeCompletion(){
    for(unsigned i=0; i<singleHeadForPredicate.getRulesSize(); i++){
        aspc::Rule rule = singleHeadForPredicate.getRule(i);
        if(rule.isConstraint()) {
            propagatorsProgram.addRule(rule);
            labeledPropgatorRules.push_back(labeledSingleHeadRules[i]);
            continue;
        }
        aspc::Atom head = rule.getHead()[0];
        std::unordered_set<std::string> headVariables;
        for(unsigned k = 0; k<head.getAriety(); k++){
            if(head.isVariableTermAt(k)){
                headVariables.insert(head.getTermAt(k));
            }
        }
        std::vector<aspc::Literal> bodyLiterals = rule.getBodyLiterals();
        if(rule.getBodySize() > 1){
            std::unordered_set<std::string> positiveBodyVars;
            std::vector<std::string> auxTerms;
            for(unsigned k=0; k<bodyLiterals.size(); k++){
                aspc::Literal* lit = &bodyLiterals[k];
                if(!lit->isNegated()){
                    for(unsigned t = 0; t<lit->getAriety(); t++){
                        if(lit->isVariableTermAt(t)){
                            auto it = positiveBodyVars.emplace(lit->getTermAt(t));
                            if(it.second){
                                auxTerms.push_back(lit->getTermAt(t));
                            }
                        }
                    } 

                }
            }
            unsigned size=0;
            std::vector<aspc::ArithmeticRelation> ineqs = rule.getArithmeticRelations();
            do{
                size=positiveBodyVars.size();
                for(int k=0;k<ineqs.size();k++){
                    if(ineqs[k].isBoundedValueAssignment(positiveBodyVars)){
                        std::string var = ineqs[k].getAssignedVariable(positiveBodyVars);
                        auto it = positiveBodyVars.emplace(var);
                        if(it.second){
                            auxTerms.push_back(var);
                        }
                    }
                }
            }while (size!=positiveBodyVars.size());

            std::string predicate = "";
            std::vector<std::string> terms;
            bool buildingAux = false;
            if(headVariables.size() == positiveBodyVars.size()){
                // head atom is used as auxAtom
                predicate = head.getPredicateName();
                terms = head.getTerms();
            }else{
                buildingAux = true;
                predicate = "aux_"+std::to_string(auxPredicates.size());
                auxPredicateId[predicate]=auxPredicates.size(); 
                auxPredicates.push_back(predicate);
                terms = auxTerms;
            }

            if(buildingAux){
                // Adding aux :- body in generator only
                aspc::Rule auxGenRule(
                    {aspc::Atom(predicate,terms)},
                    rule.getBodyLiterals(),
                    rule.getArithmeticRelations(),
                    false
                );
                generatorProgram.addRule(auxGenRule);
                aspc::Rule originalRule(
                    {head},
                    {aspc::Literal(false,aspc::Atom(predicate,terms))},
                    {},
                    false
                );
                //Adding head :- aux both in generator and propagator
                originalRule.setSupportAtom(originalRule.getBodySize());
                propagatorsProgram.addRule(originalRule);
                labeledPropgatorRules.push_back(false);
                generatorProgram.addRule(originalRule);                
            }else{
                // Adding head :- body in generator only 
                // head works as aux atom 
                generatorProgram.addRule(rule);
            }
            int supAtom = buildingAux ? -1 :0;
            for(unsigned k=0;k<bodyLiterals.size();k++){
                // Adding :- aux, not l in propagator only
                // if(edbPredicates.count(bodyLiterals[k].getPredicateName()))
                //     continue;
                aspc::Rule constraint(
                    {},
                    {aspc::Literal(false,aspc::Atom(predicate,terms)),aspc::Literal(!bodyLiterals[k].isNegated(),bodyLiterals[k].getAtom())},
                    {},
                    false
                );
                constraint.setSupportAtom(supAtom);
                propagatorsProgram.addRule(constraint);
                labeledPropgatorRules.push_back(false);
            }
            bodyLiterals.push_back(aspc::Literal(true,aspc::Atom(predicate,terms)));
            // Adding :- body, not aux.
            aspc::Rule constraint(
                {},
                bodyLiterals,
                rule.getArithmeticRelations(),
                false
            );
            propagatorsProgram.addRule(constraint);
            labeledPropgatorRules.push_back(true);

        }else{
            // Body of length at most one 
            // Adding orginal rule to both generator and propagator program
            generatorProgram.addRule(rule);
            rule.setSupportAtom(rule.getBodySize());
            propagatorsProgram.addRule(rule);
            labeledPropgatorRules.push_back(false);

        }
    }
}