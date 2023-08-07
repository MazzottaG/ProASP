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
std::pair<bool,std::pair<std::string,AggrSetPredicate>> Rewriter::buildBody(std::unordered_set<std::string> aggregateBodyVariables,const aspc::Rule& r,std::string auxValPred,std::vector<std::string> auxValTerm){
    // unsigned bodySize = auxValPred!="" ? r.getBodyLiterals().size()+1 : r.getBodyLiterals().size();
    unsigned bodySize = r.getBodyLiterals().size();
    bool writeRule = bodySize > 1 || r.getArithmeticRelations().size() > 0;
    std::vector<aspc::Literal> ruleBody(r.getBodyLiterals());
    std::vector<aspc::ArithmeticRelation> ruleInequalities(r.getArithmeticRelations());
    std::unordered_set<std::string> headVars;
    if(!r.isConstraint()){
        const aspc::Literal* lHead = r.getHead().empty() ? NULL : new aspc::Literal(false,r.getHead()[0]);
        lHead->addVariablesToSet(headVars);
    }
    if(!writeRule){
        // body with at most one literal
        if(!ruleBody.empty()){
            const aspc::Literal* l = &ruleBody[0];
            
            for(unsigned i=0; i<l->getAriety(); i++){
                std::string v = l->getTermAt(i);
                if(l->isVariableTermAt(i) && aggregateBodyVariables.count(v)==0 && headVars.count(v)==0){
                    writeRule=true;
                    break;
                }
            }
        }
    }

    std::string bodyPredicate = "body"+std::to_string(bodyPredicates.size());
    AggrSetPredicate body; 
    if(writeRule){
        clearData();
        std::unordered_set<std::string> distictBodyTerms;
        // if(auxValPred!=""){
        //     if(distictBodyTerms.count(auxValTerm[0])==0){
        //         distictBodyTerms.insert(auxValTerm[0]);
        //         body.addTerm(auxValTerm[0]);
        //     }
        //     buildingBody.push_back(aspc::Literal(false,aspc::Atom(auxValPred,auxValTerm)));
        // }
        if(!r.isConstraint()){
            const aspc::Literal* lHead = r.getHead().empty() ? NULL : new aspc::Literal(false,r.getHead()[0]);
            for(unsigned i=0; i<lHead->getAriety(); i++){
                if(distictBodyTerms.count(lHead->getTermAt(i))==0){
                    distictBodyTerms.insert(lHead->getTermAt(i));
                    body.addTerm(lHead->getTermAt(i));
                }
            }
        }
        for(const aspc::Literal& l : ruleBody){
            buildingBody.push_back(aspc::Literal(l));
            for(unsigned i=0; i<l.getAriety(); i++){
                if(aggregateBodyVariables.count(l.getTermAt(i))!=0 && distictBodyTerms.count(l.getTermAt(i))==0){
                    distictBodyTerms.insert(l.getTermAt(i));
                    body.addTerm(l.getTermAt(i));
                }
            }
        }
        for(const aspc::ArithmeticRelation& l : ruleInequalities){
            inequalities.push_back(aspc::ArithmeticRelation(l));
            for(std::string v : l.getLeft().getAllTerms()){
                if(isVariable(v) && aggregateBodyVariables.count(v)!=0 && distictBodyTerms.count(v)==0){
                    distictBodyTerms.insert(v);
                    body.addTerm(v);
                }
            }
            for(std::string v : l.getRight().getAllTerms()){
                if(isVariable(v) && aggregateBodyVariables.count(v)!=0 && distictBodyTerms.count(v)==0){
                    distictBodyTerms.insert(v);
                    body.addTerm(v);
                }
            }
        }
        bodyPredicates.insert(bodyPredicate);
        buildingHead.push_back(aspc::Atom(bodyPredicate,body.getTerms()));
        addRuleAfterAggregate();
    }else{
        if(!ruleBody.empty()){
            const aspc::Literal* literal = &ruleBody[0];
            bodyPredicate=literal->getPredicateName();
            for(unsigned i=0; i<literal->getAriety(); i++){
                body.addTerm(literal->getTermAt(i));
            }
        }else{
            // if(auxValPred!=""){
            //     bodyPredicate=auxValPred;
            //     body.addTerm(auxValTerm[0]);
            // }else{
            bodyPredicate="";
            // }
        }
    }
    return std::pair<bool,std::pair<std::string,AggrSetPredicate>>(writeRule,std::pair<std::string,AggrSetPredicate>(bodyPredicate,body));
}
std::pair<bool,std::pair<std::string,AggrSetPredicate>> Rewriter::buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation){
    bool writeRule = aggregareRelation.getAggregate().getAggregateLiterals().size()>1 || aggregareRelation.getAggregate().getAggregateInequalities().size()>0;
    std::vector<aspc::Literal> aggregateLiterals(aggregareRelation.getAggregate().getAggregateLiterals());
    std::vector<aspc::ArithmeticRelation> aggregateInequalities(aggregareRelation.getAggregate().getAggregateInequalities());
    std::vector<std::string> aggregateVariables(aggregareRelation.getAggregate().getAggregateVariables());
    if(!writeRule){
        const aspc::Literal* l = &aggregateLiterals[0];
        for(unsigned i=0;i<l->getAriety();i++){
            if(l->isVariableTermAt(i)){
                bool found=false;
                for(std::string v : aggregateVariables){
                    if(v == l->getTermAt(i)){
                        found=true;
                        break;
                    } 
                }
                if(!found){
                    if(bodyVariables.count(l->getTermAt(i))!=0)
                        found=true;
                    else{
                        writeRule=true;
                        break;
                    }
                }
            }
        }
        if(!writeRule){
            for(unsigned i=0;i<l->getAriety() && !writeRule;i++){
                for(unsigned j=i+1;j<l->getAriety() && !writeRule;j++){
                    if(l->isVariableTermAt(i) && l->isVariableTermAt(j) && l->getTermAt(i)==l->getTermAt(j)){
                        writeRule=true;
                    }
                }
            }
        }
    }
    std::string aggregateSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
    AggrSetPredicate aggrSet;
    if(writeRule){
        clearData();
        std::unordered_set<std::string> aggrSetDistinctTerms;
        for(std::string v :aggregareRelation.getAggregate().getAggregateVariables()){
            if(aggrSetDistinctTerms.count(v)==0){
                aggrSetDistinctTerms.insert(v);
                aggrSet.addTerm(v);
            }
        }
        for(const aspc::Literal& l:aggregateLiterals){
            for(unsigned i=0; i<l.getAriety(); i++){
                std::string v = l.getTermAt(i);
                if((!l.isVariableTermAt(i) || bodyVariables.count(v)!=0) && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            aggrSet.addLiteral(l);
            buildingBody.push_back(aspc::Literal(l));
        }
        for(const aspc::ArithmeticRelation& l:aggregateInequalities){
            
            for(std::string v : l.getLeft().getAllTerms()){
                if(isVariable(v) && bodyVariables.count(v)!=0 && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            
            for(std::string v : l.getRight().getAllTerms()){
                if(isVariable(v) && bodyVariables.count(v)!=0 && aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            inequalities.push_back(aspc::ArithmeticRelation(l));
            aggrSet.addInequality(l);
        }
        bool sharedAggrSet=false;
        for(const auto& previous:aggrSetPredicates){
            if(aggrSet == previous.second){
                aggregateSetPredicate=previous.first;
                sharedAggrSet=true;
                break;
            }
        }
        if(!sharedAggrSet){
            aggrSetPredicates[aggregateSetPredicate]=aggrSet;
            buildingHead.push_back(aspc::Atom(aggregateSetPredicate,aggrSet.getTerms()));
            addRuleAfterAggregate();
        }
        
    }else{
        //Aggregate contains only one bound literal considering body variables and aggregation variables
        const aspc::Literal* literal = &aggregateLiterals[0];
        int prevAggrVarIndex = prgPredicatAsAggSet.count(literal->getPredicateName()) != 0 ? prgPredicatAsAggSet[literal->getPredicateName()] : -1;
        int aggrVarIndex = -1;
        std::string aggrVar = aggregareRelation.getAggregate().getAggregateVariables()[0];
        for(unsigned k = 0; k<literal->getAriety(); k++){
            if(literal->isVariableTermAt(k) && literal->getTermAt(k) == aggrVar){
                if(k == prevAggrVarIndex){
                    aggrVarIndex=prevAggrVarIndex;
                    break;
                }else if(aggrVarIndex < 0){
                    aggrVarIndex = k;
                }
            }
        }
        if(prevAggrVarIndex < 0 || prevAggrVarIndex == aggrVarIndex){
            aggregateSetPredicate=literal->getPredicateName();
            prgPredicatAsAggSet[aggregateSetPredicate]=aggrVarIndex;
            for(unsigned i=0; i<literal->getAriety(); i++){
                aggrSet.addTerm(literal->getTermAt(i));
            }        
        }else{
            clearData();
            buildingHead.push_back(aspc::Atom(aggregateSetPredicate,literal->getTerms()));
            buildingBody.push_back(*literal);
            std::unordered_set<std::string> aggrSetDistinctTerms;
            for(std::string v :aggregareRelation.getAggregate().getAggregateVariables()){
                if(aggrSetDistinctTerms.count(v)==0){
                    aggrSetDistinctTerms.insert(v);
                    aggrSet.addTerm(v);
                }
            }
            for(const aspc::Literal& l:aggregateLiterals){
                for(unsigned i=0; i<l.getAriety(); i++){
                    std::string v = l.getTermAt(i);
                    if((!l.isVariableTermAt(i) || bodyVariables.count(v)!=0) && aggrSetDistinctTerms.count(v)==0){
                        aggrSetDistinctTerms.insert(v);
                        aggrSet.addTerm(v);
                    }
                }
                aggrSet.addLiteral(l);
            }      
            aggrSetPredicates[aggregateSetPredicate]=aggrSet;
            addRuleAfterAggregate();
            writeRule=true;
        }
    }
    return std::pair<bool,std::pair<std::string,AggrSetPredicate>>(writeRule,std::pair<std::string,AggrSetPredicate>(aggregateSetPredicate,aggrSet));
}
std::vector<std::string> Rewriter::writeAggrIdRule(std::pair<bool,std::pair<std::string,AggrSetPredicate>> body,std::pair<bool,std::pair<std::string,AggrSetPredicate>> aggrSet,const aspc::Rule& r){
    const aspc::ArithmeticRelationWithAggregate* aggregate = &r.getArithmeticRelationsWithAggregate()[0];
    bool plusOne = aggregate->getComparisonType() != aspc::EQ && aggregate->isPlusOne();
    std::string aggrId0;
    std::string aggrId1;
    if(aggregate->getComparisonType() != aspc::EQ){
        clearData();
        if(body.second.first != "")
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
            false,
            aggregate->getGuard(),
            aspc::Aggregate(
                {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
                {},
                aggregate->getAggregate().getAggregateVariables(),
                aggregate->getAggregate().getAggregateFunction()),
            aggregate->getComparisonType(),
            false)
        );    
        inequalitiesWithAggregate[0].setPlusOne(aggregate->isPlusOne());
        aggrId0 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
        aggrIdPredicates.insert(aggrId0);
        addRuleAfterAggregate();
    }else{
        std::cout << "Error: Equal operator not supported yet. Coming soon ..."<<std::endl;
        // aspc::ComparisonType cmp = aggregate->isNegated()  ? aspc::GT : aspc::GTE;
        // clearData();
        // if(body.second.first != "")
        //     buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        // inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
        //     false,
        //     aggregate->getGuard(),
        //     aspc::Aggregate(
        //         {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
        //         {},
        //         aggregate->getAggregate().getAggregateVariables(),
        //         aggregate->getAggregate().getAggregateFunction()),
        //     cmp,
        //     false)
        // );    
        // aggrId0 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        // buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
        // aggrIdPredicates.insert(aggrId0);
        // onRule();
        // aspc::ComparisonType cmp2 = aggregate->isNegated() ? aspc::LT : aspc::LTE;
        // if(body.second.first != "")
        //     buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        // inequalitiesWithAggregate.push_back(aspc::ArithmeticRelationWithAggregate(
        //     false,
        //     aggregate->getGuard(),
        //     aspc::Aggregate(
        //         {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
        //         {},
        //         aggregate->getAggregate().getAggregateVariables(),
        //         aggregate->getAggregate().getAggregateFunction()),
        //     cmp2,
        //     false)
        // );    
        // aggrId1 = "aggr_id"+std::to_string(aggrIdPredicates.size());
        // buildingHead.push_back(aspc::Atom(aggrId1,body.second.second.getTerms()));
        // aggrIdPredicates.insert(aggrId1);
        // onRule();
    }
    std::vector<std::string> aggrIds({aggrId0});
    if(aggrId1!=""){
        aggrIds.push_back(aggrId1);
    }
    return aggrIds;
}

void Rewriter::rewriteAggregates(){

    for(unsigned i=0; i<singleHeadForPredicate.getRulesSize(); i++){
        aspc::Rule r = singleHeadForPredicate.getRule(i);
        if(!r.containsAggregate()){
            afterAggregate.addRule(r);
            continue;
        }
        std::cout<<"Rewriting rule with aggregate"<<std::endl;
        r.print();
        //building aggr_set
        std::unordered_set<std::string> bodyVariables;
        for(const aspc::Literal& l : r.getBodyLiterals()){
            l.addVariablesToSet(bodyVariables);
        }
        for(const aspc::ArithmeticRelation& l : r.getArithmeticRelations()){
            l.addVariablesToSet(bodyVariables);
        }

        std::unordered_set<std::string> aggregateBodyVariables;
        for(const aspc::Literal& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()){
            l.addVariablesToSet(aggregateBodyVariables);
        }
        for(const aspc::ArithmeticRelation& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateInequalities()){
            l.addVariablesToSet(aggregateBodyVariables);
        }
        for(std::string v : r.getArithmeticRelationsWithAggregate()[0].getGuard().getAllTerms()){
            aggregateBodyVariables.insert(v);
        }


        auto aggrSet = buildAggregateSet(bodyVariables,r.getArithmeticRelationsWithAggregate()[0]);
        // std::string auxValPredicate="";
        // std::vector<std::string> auxValTerm;
        if(!r.getArithmeticRelationsWithAggregate()[0].isBoundedRelation(bodyVariables) && r.getArithmeticRelationsWithAggregate()[0].getComparisonType() == aspc::EQ){
            std::cout << "Equal operator not supported yet. Coming soon ..."<<std::endl;
            exit(180);
            // if(aggrSetToAuxVal.count(aggrSet.second.first)!=0){
            //     auxValPredicate=aggrSetToAuxVal[aggrSet.second.first];
            //     auxValTerm.push_back(r.getArithmeticRelationsWithAggregate()[0].getGuard().getTerm1());
            // }else{
            //     auxValPredicate="aux_val"+std::to_string(auxPossibleSumToAggrSet.size());
            //     auxPossibleSumToAggrSet[auxValPredicate]=aggrSet.second.first;
            //     aggrSetToAuxVal[aggrSet.second.first]=auxValPredicate;
            //     auxValTerm.push_back(r.getArithmeticRelationsWithAggregate()[0].getGuard().getTerm1());
            // }
        }

        // auto body = buildBody(aggregateBodyVariables,r,auxValPredicate,auxValTerm);
        auto body = buildBody(aggregateBodyVariables,r,"",{});
        std::vector<std::string> aggrIds = writeAggrIdRule(body,aggrSet,r);
        clearData();
        if(aggrIds.size() == 1){
            if(body.second.first != "")
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(r.getArithmeticRelationsWithAggregate()[0].isNegated(),aspc::Atom(aggrIds[0],body.second.second.getTerms())));
            if(r.isConstraint())
                addRuleAfterAggregate();
            else{
                buildingHead.push_back(r.getHead()[0]);
                addRuleAfterAggregate();
            }
        }else{
            std::cout << "Error: equal operator not supported yet. Coming soon ..."<<std::endl;
            exit(180);
        //     if(r.getArithmeticRelationsWithAggregate()[0].isNegated()){
        //         if(body.second.first != "")
        //             buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        //         buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIds[0],body.second.second.getTerms())));
        //         if(r.isConstraint())
        //             onConstraint();
        //         else{
        //             buildingHead.push_back(r.getHead()[0]);
        //             rewriteRule();
        //         }
        //         if(body.second.first != "")
        //             buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        //         buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIds[1],body.second.second.getTerms())));
        //         if(r.isConstraint())
        //             onConstraint();
        //         else{
        //             buildingHead.push_back(r.getHead()[0]);
        //             rewriteRule();
        //         }
        //     }else{
        //         if(body.second.first != "")
        //             buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
        //         buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIds[0],body.second.second.getTerms())));
        //         buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIds[1],body.second.second.getTerms())));
        //         if(r.isConstraint())
        //             onConstraint();
        //         else{
        //             buildingHead.push_back(r.getHead()[0]);
        //             rewriteRule();
        //         }
        //     }
        }
    }
    std::cout << "%%%%%%%%%%%%%%%% After Aggregates %%%%%%%%%%%%%%%%"<<std::endl;
    for(unsigned i=0; i<afterAggregate.getRulesSize(); i++)
        afterAggregate.getRule(i).print();
    std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;
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
                //labeledSingleHeadRules.push_back(true);
                singleHeadForPredicate.addRule(r);
                //labeledSingleHeadRules.push_back(false);

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
            //labeledSingleHeadRules.push_back(false);
        }else if(rules.size() == 1){
            singleHeadForPredicate.addRule(program.getRule(rules[0]));
            //labeledSingleHeadRules.push_back(false);
        }
    }
    for(unsigned ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
        if(program.getRule(ruleId).isConstraint()){
            singleHeadForPredicate.addRule(program.getRule(ruleId));
            //labeledSingleHeadRules.push_back(false);
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
    for(std::string predicate : aggrIdPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }
    for(auto predicate : aggrSetPredicates){
        if(predicate.first == "") continue;
        predicateId[predicate.first]=predicateNames.size();
        predicateNames.push_back(predicate.first);
    }
    for(std::string predicate : bodyPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }
    
}
void Rewriter::computeCompletion(){
    for(unsigned i=0; i<afterAggregate.getRulesSize(); i++){
        aspc::Rule rule = afterAggregate.getRule(i);
        if(rule.isConstraint()) {
            propagatorsProgram.addRule(rule);
            //labeledPropgatorRules.push_back(labeledSingleHeadRules[i]);
            continue;
        }else if(rule.containsAggregate()){
            propagatorsProgram.addRule(rule);
            assert(rule.getBodyLiterals().size() <= 1);
            const aspc::Atom* head = &rule.getHead()[0];
            const aspc::Literal* body = rule.getBodyLiterals().size() == 0 ? NULL : &rule.getBodyLiterals()[0];
            
            aspc::Rule genAggId ({aspc::Atom(head->getPredicateName(),head->getTerms())},{(body == NULL ? (aspc::Literal(false,aspc::Atom("",{}))) : aspc::Literal(*body))},{},false);
            generatorProgram.addRule(genAggId);
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
        bool analyze_body = rule.getBodySize() > 1;
        if(!analyze_body && rule.getBodyLiterals().size() >= 1){
            const aspc::Literal* literal = &rule.getBodyLiterals()[0];
            for(unsigned k = 0; k < literal->getAriety(); k++){
                for(unsigned k1 = k+1; k1 < literal->getAriety(); k1++){
                    if(literal->isVariableTermAt(k) && literal->isVariableTermAt(k1) && literal->getTermAt(k) == literal->getTermAt(k1)){
                        analyze_body=true;
                    }
                }   
            }
        } 
        if(analyze_body){
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
                //labeledPropgatorRules.push_back(false);
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
                //labeledPropgatorRules.push_back(false);
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
            //labeledPropgatorRules.push_back(true);

        }else{
            // Body of length at most one 
            // Adding orginal rule to both generator and propagator program
            generatorProgram.addRule(rule);
            rule.setSupportAtom(rule.getBodySize());
            propagatorsProgram.addRule(rule);
            //labeledPropgatorRules.push_back(false);

        }
    }
}