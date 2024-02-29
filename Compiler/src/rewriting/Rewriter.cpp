#include "Rewriter.h"
#include "Analyzer.h"

const int Rewriter::DOMAIN_RULE=1;
const int Rewriter::GROUND_RULE=2;
const int Rewriter::TO_GENERATE=3;
const int Rewriter::SUBSETSUM_RULE=4;

void Rewriter::addOriginalConstraint(){
    for(unsigned i=0; i<program.getRulesSize();i++){
        auto rule = program.getRule(i);
        if(rule.isConstraint()){
            propagatorsProgram.addRule(rule);
        }
    }
}
void Rewriter::rewriteGroundedAggregate(const aspc::Rule& r, Analyzer& analyzer, GroundedAggrData& data){
    
    // bodyVariables contains variables appearing in the body of r without the aggregate
    std::cout << "Rewriting ground rule ";r.print();
    std::unordered_set<std::string> bodyVariables;
    r.addPositiveBodyVariablesToSet(bodyVariables);

    std::vector<std::string> aggSetTerms;
    std::string aggSetPred = "";
    bool aggSetNegated = false;

    for(const aspc::Formula* f : r.getFormulas()){
        // TODO: Add support for multiple aggregates in the same rule
        if(f->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* aggrRelation = (const aspc::ArithmeticRelationWithAggregate*) f;
            bool isBoudedValueAssignment = aggrRelation->isBoundedValueAssignment(bodyVariables);
            std::vector<aspc::Literal> aggregateLiterals(aggrRelation->getAggregate().getAggregateLiterals());
            std::vector<aspc::ArithmeticRelation> aggregateInequalities(aggrRelation->getAggregate().getAggregateInequalities());
            std::vector<std::string> aggregateVariables(aggrRelation->getAggregate().getAggregateVariables());

            std::vector<std::string> aggIdTerms;
            std::unordered_set<std::string> distinctAggIdTerms;
            std::string aggrId = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrId);

            //distinctAggIdTerms contains all the variables appearing in the aggregate body and in the body of the rule
            r.addSharedVars(bodyVariables,aggIdTerms,distinctAggIdTerms,aggrRelation,false);
            // "Guard" is a placeHolder for the aggregate bound
            aggIdTerms.push_back("Guard");

            // if(aggrRelation->isBoundedValueAssignment(bodyVariables)){
            //     // if the aggregate gives the bound to some variable, then this variable is the last term unless it is already added
            //     std::string assignedVar = aggrRelation->getAssignedVariable(bodyVariables);
            //     if(!distinctAggIdTerms.count(assignedVar)){
            //         distinctAggIdTerms.insert(assignedVar);
            //         aggIdTerms.push_back(assignedVar);
            //     }
            // }else if(aggrRelation->getComparisonType() == aspc::EQ){
            //     if(!aggrRelation->getGuard().isSingleTerm() || !isVariable(aggrRelation->getGuard().getTerm1())){
            //     }

            // }
            
            unsigned countIDB = 0;
            bool boundIDB = true;
            for(unsigned i=0; i<aggregateLiterals.size(); i++){
                if(!analyzer.isEDB(aggregateLiterals[i].getPredicateName())){
                    countIDB++;
                    if(countIDB==1) {
                        aggSetTerms=aggregateLiterals[i].getTerms();
                        aggSetPred=aggregateLiterals[i].getPredicateName();
                        aggSetNegated= aggregateLiterals[i].isNegated();
                    }
                }
            }
            if(countIDB == 1){
                std::unordered_set<std::string> idbBounds(bodyVariables);
                for(std::string var : aggrRelation->getAggregate().getAggregateVariables()){
                    if(isVariable(var)) idbBounds.insert(var);
                }
                boundIDB = aspc::Literal(aggSetNegated,aspc::Atom(aggSetPred,aggSetTerms)).isBoundedLiteral(idbBounds);
            }
            std::string aggregateSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
            AggrSetPredicate aggrSet;
            if(countIDB > 1 || !boundIDB){
                std::cout << "   Writing aggSet rule"<<std::endl;
                clearData();
                std::unordered_set<std::string> aggrSetDistinctTerms;
                for(std::string v :aggrRelation->getAggregate().getAggregateVariables()){
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
                SharedVars sharedVarData = aggrRelation->getAggregate().getSharedBody(bodyVariables,r.getBodyLiterals(),r.getArithmeticRelations());
                for(const auto& previous:aggrSetPredicates){
                    if(aggrSet == previous.second){
                        auto it = aggSetToSharedVars.find(previous.first);
                        if(( it == aggSetToSharedVars.end() && sharedVarData.empty()) || (it != aggSetToSharedVars.end() && sharedVarData == aggrSharedVarsPredicate[it->second])){
                            aggregateSetPredicate=previous.first;
                            sharedAggrSet=true;
                            break;
                        }
                    }
                }
                
                if(!sharedAggrSet){
                    if(!sharedVarData.empty() && !aggrRelation->isSafeAggSet()){
                        std::string sharedVarsPredicate = "sharedVar"+std::to_string(sharedVarsPredicates.size());
                        bool defined = false;
                        for(auto pair : aggrSharedVarsPredicate){
                            if(pair.second == sharedVarData){
                                sharedVarsPredicate=pair.first;
                                defined = true;
                                break;
                            }
                        }
                        if(!defined){
                            //declaring new predicated sharedVars
                            aggrSharedVarsPredicate[sharedVarsPredicate]=sharedVarData;
                            sharedVarsPredicateId[sharedVarsPredicate]=sharedVarsPredicates.size();
                            sharedVarsPredicates.push_back(sharedVarsPredicate);

                            //mapping sharedVars to currentAggSet
                            aggSetToSharedVars[aggregateSetPredicate]=sharedVarsPredicate;

                            //adding domain rule
                            domainRules.push_back(aspc::Rule({aspc::Atom(sharedVarsPredicate,sharedVarData.getTerms())},r.getBodyLiterals(),r.getArithmeticRelations(),false));
                        }
                        buildingBody.push_back(aspc::Literal(false,aspc::Atom(sharedVarsPredicate,sharedVarData.getTerms())));
                    }
                    aggrSetPredicates[aggregateSetPredicate]=aggrSet;
                    buildingHead.push_back(aspc::Atom(aggregateSetPredicate,aggrSet.getTerms()));
                    data.rules.push_back(aspc::Rule(buildingHead,buildingBody,inequalities,inequalitiesWithAggregate,false,false));

                }
                clearData();
                
                for(const aspc::Literal& l : r.getBodyLiterals())
                    buildingBody.push_back(l);
                for(const aspc::ArithmeticRelation& rel : r.getArithmeticRelations())
                    inequalities.push_back(rel);
                inequalitiesWithAggregate.push_back(
                    aspc::ArithmeticRelationWithAggregate(
                        false,
                        aggrRelation->getGuard(),
                        aspc::Aggregate(
                            {aspc::Literal(false,aspc::Atom(aggregateSetPredicate,aggrSet.getTerms()))},
                            {},
                            aggrRelation->getAggregate().getAggregateVariables(),
                            aggrRelation->getAggregate().getAggregateFunction()
                        ),
                        aggrRelation->getComparisonType(),
                        aggrRelation->isNegated())
                );
                inequalitiesWithAggregate.back().setPlusOne(aggrRelation->isPlusOne());
                for(const aspc::Atom& h : r.getHead()) buildingHead.push_back(h);

                data.rules.push_back(aspc::Rule(buildingHead,buildingBody,inequalities,inequalitiesWithAggregate,false,false));
                data.setAggId(aspc::Atom(aggrId,aggIdTerms));
                data.setEqual(inequalitiesWithAggregate.back().getComparisonType() == aspc::EQ);
                data.setGenBound(isBoudedValueAssignment);
                data.setAggSet(aspc::Literal(false,aspc::Atom(aggregateSetPredicate,aggrSet.getTerms())));
                return;

            }else if(countIDB == 1){
                std::cout << "   exactly one IDB in aggregate body"<<std::endl;
                std::cout << "   Adding rule "; r.print();

                data.rules.push_back(r);
                data.setAggId(aspc::Atom(aggrId,aggIdTerms));
                data.setEqual(aggrRelation->getComparisonType() == aspc::EQ);
                data.setGenBound(isBoudedValueAssignment);
                data.setAggSet(aspc::Literal(aggSetNegated,aspc::Atom(aggSetPred,aggSetTerms)));
                return;

            }else{
                std::cout << "Error: unable to find idb literal for aggregate body"<<std::endl;
                exit(180);
            }
        }
    }
    assert(false);
}
void Rewriter::addSubSetSumRule(std::vector<int>& generatorRuleLabel){
    for(unsigned ruleId=0; ruleId < subSetSumRules.size(); ruleId++){
        generatorProgram.addRule(subSetSumRules[ruleId]);
        generatorRuleLabel.push_back(SUBSETSUM_RULE);
    }
}
void Rewriter::addDomainRule(std::vector<int>& generatorRuleLabel){
    for(unsigned ruleId=0; ruleId < domainRules.size(); ruleId++){
        generatorProgram.addRule(domainRules[ruleId]);
        generatorRuleLabel.push_back(DOMAIN_RULE);
    }
}
void Rewriter::addToGroundRule(const aspc::Rule& r,std::vector<int>& generatorRuleLabel, Analyzer& analyzer){
    if(r.containsAggregate()){
        GroundedAggrData data;

        rewriteGroundedAggregate(r,analyzer,data);
        std::cout << "Added rule for grounding aggregate {\n";
        for(const aspc::Rule& rule : data.rules){
            std::cout << "   ";
            rule.print();
            if(rule.containsAggregate()){
                aggregateGroundingMapping[generatorRuleLabel.size()]=aggregateGrounding.size();
                aggregateGrounding.push_back(data);
            }
            generatorProgram.addRule(rule);
            generatorRuleLabel.push_back(GROUND_RULE);
        }
        std::cout << "}\n";
        return;
    }
    generatorProgram.addRule(r);
    generatorRuleLabel.push_back(GROUND_RULE);

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
                if(l->isVariableTermAt(i) && aggregateBodyVariables.count(v)==0 && headVars.count(v)==0 ){
                    writeRule=true;
                    break;
                }
            }
        }
    }

    std::string bodyPredicate = "body"+std::to_string(bodyPredicates.size());
    AggrSetPredicate body;
    //TODO: Add body predicate sharing
    if(writeRule){
        clearData();
        std::unordered_set<std::string> distictBodyTerms;
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
std::pair<bool,std::pair<std::string,AggrSetPredicate>> Rewriter::buildAggregateSet(std::unordered_set<std::string> bodyVariables,const aspc::ArithmeticRelationWithAggregate& aggregareRelation,const std::vector<aspc::Literal>& bodyLits,const std::vector<aspc::ArithmeticRelation>& bodyIneqs){
    bool writeRule = aggregareRelation.getAggregate().getAggregateLiterals().size()>1 || aggregareRelation.getAggregate().getAggregateInequalities().size()>0;
    std::vector<aspc::Literal> aggregateLiterals(aggregareRelation.getAggregate().getAggregateLiterals());
    std::vector<aspc::ArithmeticRelation> aggregateInequalities(aggregareRelation.getAggregate().getAggregateInequalities());
    std::vector<std::string> aggregateVariables(aggregareRelation.getAggregate().getAggregateVariables());
    if(!writeRule){
        assert(aggregareRelation.getAggregate().getAggregateLiterals().size() > 0);
        const aspc::Literal* l = &aggregateLiterals[0];
        if(l->isNegated()) writeRule = true;
        else{
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
                            std::cout << "   Variables "<<l->getTermAt(i)<<"Not found neither in body vars not in aggregate vars"<<std::endl;
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
                            std::cout << "   Found duplicated Variable "<<l->getTermAt(i)<<std::endl;
                            writeRule=true;
                        }
                    }
                }
            }
            if(!writeRule){
                const aspc::Literal* literal = &aggregateLiterals[0];
                int prevAggrVarIndex = prgPredicatAsAggSet.count(literal->getPredicateName()) != 0 ? prgPredicatAsAggSet[literal->getPredicateName()] : -1;
                int aggrVarIndex = -1;
                std::string aggrVar = aggregareRelation.getAggregate().getAggregateVariables()[0];
                for(unsigned k = 0; k<literal->getAriety(); k++){
                    if(literal->isVariableTermAt(k) && literal->getTermAt(k) == aggrVar){
                        aggrVarIndex=k;
                        break;
                    }
                }
                std::cout << "------ Checking rule ";aggregareRelation.print();std::cout << " ------"<<std::endl;
                if(prevAggrVarIndex >= 0) std::cout << "   " << literal->getPredicateName() << " already appeared as aggSet and it is indexed on term "<<prevAggrVarIndex<<std::endl;
                std::cout << "   " << literal->getPredicateName() << " is appearing as aggSet and it should be indexed on term "<<aggrVarIndex<<std::endl;
                if(prevAggrVarIndex >= 0 && prevAggrVarIndex != aggrVarIndex) writeRule=true;
            }
        }
    }

    std::string aggregateSetPredicate="aggr_set"+std::to_string(aggrSetPredicates.size());
    AggrSetPredicate aggrSet;
    if(writeRule){
        std::cout << "   Writing agg_set rule "<<std::endl;
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
        SharedVars sharedVarData = aggregareRelation.getAggregate().getSharedBody(bodyVariables,bodyLits,bodyIneqs);
        bool sharedAggrSet=false;
        for(const auto& previous:aggrSetPredicates){
            if(aggrSet == previous.second){
                auto it = aggSetToSharedVars.find(previous.first);
                if(( it == aggSetToSharedVars.end() && sharedVarData.empty()) || (it != aggSetToSharedVars.end() && sharedVarData == aggrSharedVarsPredicate[it->second])){
                    aggregateSetPredicate=previous.first;
                    sharedAggrSet=true;
                    break;
                }
            }
        }
        if(!sharedAggrSet){
            if(!sharedVarData.empty()){
                if(!aggregareRelation.isSafeAggSet()){
                    std::string sharedVarsPredicate = "sharedVar"+std::to_string(sharedVarsPredicates.size());
                    bool defined = false;
                    for(auto pair : aggrSharedVarsPredicate){
                        if(pair.second == sharedVarData){
                            sharedVarsPredicate=pair.first;
                            defined = true;
                            break;
                        }
                    }
                    if(!defined){
                        //declaring new predicated sharedVars
                        aggrSharedVarsPredicate[sharedVarsPredicate]=sharedVarData;
                        sharedVarsPredicateId[sharedVarsPredicate]=sharedVarsPredicates.size();
                        sharedVarsPredicates.push_back(sharedVarsPredicate);

                        //mapping sharedVars to currentAggSet
                        aggSetToSharedVars[aggregateSetPredicate]=sharedVarsPredicate;

                        //adding domain rule
                        domainRules.push_back(aspc::Rule({aspc::Atom(sharedVarsPredicate,sharedVarData.getTerms())},bodyLits,bodyIneqs,false));
                    }
                    buildingBody.push_back(aspc::Literal(false,aspc::Atom(sharedVarsPredicate,sharedVarData.getTerms())));
                }
            }
            aggrSetPredicates[aggregateSetPredicate]=aggrSet;
            buildingHead.push_back(aspc::Atom(aggregateSetPredicate,aggrSet.getTerms()));
            addRuleAfterAggregate();
        }

    }else{
        //Aggregate contains only one bound literal considering body variables and aggregation variables
        std::cout << "   Not Writing agg_set rule "<<std::endl;

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
        assert(prevAggrVarIndex < 0 || prevAggrVarIndex == aggrVarIndex);
        aggregateSetPredicate=literal->getPredicateName();
        prgPredicatAsAggSet[aggregateSetPredicate]=aggrVarIndex;
        for(unsigned i=0; i<literal->getAriety(); i++){
            aggrSet.addTerm(literal->getTermAt(i));
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
        aggrIdPredicates.insert(aggrId0);
        buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
        addRuleAfterAggregate();
    }else{
        assert(aggregate->getComparisonType() == aspc::EQ);
        {
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
                aspc::GTE,
                false)
            );
            aggrId0 = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrId0);
            buildingHead.push_back(aspc::Atom(aggrId0,body.second.second.getTerms()));
            addRuleAfterAggregate();
        }
        {
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
                aspc::LTE,
                false)
            );
            aggrId1 = "aggr_id"+std::to_string(aggrIdPredicates.size());
            aggrIdPredicates.insert(aggrId1);
            buildingHead.push_back(aspc::Atom(aggrId1,body.second.second.getTerms()));
            addRuleAfterAggregate();
        }
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
        r.addBodyVars(bodyVariables);

        std::unordered_set<std::string> aggregateBodyVariables;
        for(const aspc::Literal& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()){
            l.addVariablesToSet(aggregateBodyVariables);
        }
        for(const aspc::ArithmeticRelation& l : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateInequalities()){
            l.addOccurringVariables(aggregateBodyVariables);
        }
        for(std::string v : r.getArithmeticRelationsWithAggregate()[0].getGuard().getAllTerms()){
            if(isVariable(v)) aggregateBodyVariables.insert(v);
        }


        auto aggrSet = buildAggregateSet(bodyVariables,r.getArithmeticRelationsWithAggregate()[0],r.getBodyLiterals(),r.getArithmeticRelations());
        // std::string auxValPredicate="";
        // std::vector<std::string> auxValTerm;
        // if(!r.getArithmeticRelationsWithAggregate()[0].isBoundedRelation(bodyVariables) && r.getArithmeticRelationsWithAggregate()[0].getComparisonType() == aspc::EQ){
        if(r.getArithmeticRelationsWithAggregate()[0].isBoundedValueAssignment(bodyVariables)){
            assert(!r.getArithmeticRelationsWithAggregate()[0].isNegated());
            std::cout << "Guard: "<<r.getArithmeticRelationsWithAggregate()[0].getGuard()<<std::endl;
            std::cout << "Aggregate set atom: "; aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()).print(); std::cout << std::endl;
            std::cout << "Aggregate variables:";
            for(std::string variable : r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateVariables()){
                std::cout << " " << variable;
            }
            std::cout << std::endl;
            std::string ssumPredicate = "ssum_"+std::to_string(subSetSumPredicates.size());
            subSetSumPredicateToId[ssumPredicate]=subSetSumPredicates.size();
            subSetSumPredicates.push_back(ssumPredicate);
            
            std::vector<std::string> headTerms;
            for(std::string term: aggrSet.second.second.getTerms()){
                if(bodyVariables.count(term))
                    headTerms.push_back(term);
            }
            headTerms.push_back(r.getArithmeticRelationsWithAggregate()[0].getAssignedVariable(bodyVariables));

            std::string aggrVar = r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateVariables()[0];
            
            subSetSumRules.push_back(aspc::Rule(
                {aspc::Atom(ssumPredicate,headTerms)},
                {aspc::Literal(false,aspc::Atom(aggrSet.second.first,aggrSet.second.second.getTerms()))},
                {aspc::ArithmeticRelation(aspc::ArithmeticExpression(aggrVar),aspc::ArithmeticExpression(r.getArithmeticRelationsWithAggregate()[0].getAggregate().isSum() ? "sum": "count"),aspc::EQ)},
                false
            ));
            std::cout << "SubSetSum rule: ";subSetSumRules.back().print();
            bodyVariables.insert(headTerms.back());
            r.addBodyLiteral(aspc::Literal(false,aspc::Atom(ssumPredicate,headTerms)));
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
            if(body.second.first != "")
                buildingBody.push_back(aspc::Literal(false,aspc::Atom(body.second.first,body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(false,aspc::Atom(aggrIds[0],body.second.second.getTerms())));
            buildingBody.push_back(aspc::Literal(true,aspc::Atom(aggrIds[1],body.second.second.getTerms())));
            if(r.isConstraint())
                addRuleAfterAggregate();
            else{
                buildingHead.push_back(r.getHead()[0]);
                addRuleAfterAggregate();
            }
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
                    std::cout << "Error using same predicate name with different ariety value: "<<rule->getHead()[0].getPredicateName()<<std::endl;
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
    for(std::string predicate : sharedVarsPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }
    for(std::string predicate : subSetSumPredicates){
        predicateId[predicate]=predicateNames.size();
        predicateNames.push_back(predicate);
    }

}
void Rewriter::printSharedVars(){
    for(auto pair : aggrSharedVarsPredicate){
        pair.second.print(pair.first);
    }
}
void Rewriter::computeCompletion(){
    DependencyManager dependencyManager;

    dependencyManager.buildDependecyGraph(afterAggregate);
    auto scc = dependencyManager.getSCC();
    std::unordered_set<unsigned >skipRule;

    aspc::Program completionProgram;

    std::cout << "Applying negative loop completion on:"<<std::endl;
    for(int componentId = scc.size()-1; componentId >=0; componentId--){
        auto pair = dependencyManager.checkComponent(afterAggregate,componentId);
        std::cout << "   Component:";
        for(int predicate : scc[componentId]) std::cout << " " <<dependencyManager.getPredicateName(predicate);
        std::cout << std::endl;
        if(pair.second){
            for(auto ruledata : pair.first){
                skipRule.insert(ruledata.second);
            }
            std::string predicate_1 = dependencyManager.getPredicateName(scc[componentId][0]);
            std::string predicate_2 = dependencyManager.getPredicateName(scc[componentId][1]);

            std::vector<aspc::Literal> extractionLiterals;
            std::vector<aspc::ArithmeticRelation> extractionIneqs;

            for(const aspc::Formula* f : pair.first[0].first.getFormulas()){
                if(!f->isLiteral()){
                    extractionIneqs.push_back(*((const aspc::ArithmeticRelation*) f));
                }else {
                    const aspc::Literal* lit = (const aspc::Literal*) f;
                    if(lit->getPredicateName() != predicate_1 && lit->getPredicateName() != predicate_2){
                        extractionLiterals.push_back(*lit);
                    }
                }
            }
            bool datalogBody = true;
            for(aspc::Literal l: extractionLiterals) if(!analyzer->isEDB(l.getPredicateName())) datalogBody = false;
            bool extract = extractionLiterals.size() > 1 || extractionIneqs.size() > 0;
            aspc::Literal headLit(false,pair.first[0].first.getHead()[0]);
            if(extract){
                // extracting propagator rule dom :- shared body
                std::string dom_pred = "Dom_"+predicate_1+"_"+predicate_2;
                aspc::Atom projected_head(dom_pred,headLit.getTerms());
                aspc::Rule domainRule ({projected_head},extractionLiterals,extractionIneqs,false);
                auto it = predicateId.emplace(dom_pred,predicateNames.size());
                if(it.second) predicateNames.push_back(dom_pred);
                if(datalogBody){
                    analyzer->addDatalogRule(domainRule);
                }else{
                    completionProgram.addRule(domainRule);
                }
//                std::cout << "Propagator rule ";domainRule.print();
                extractionLiterals.clear();
                extractionLiterals.push_back(aspc::Literal(false,projected_head));
                extractionIneqs.clear();
            }
            // extraction literals contains the unique body literal; extraction ineqs is empty

            // generating rule a :- body na :- body
            aspc::Rule generateP1 ({aspc::Atom(predicate_1,headLit.getTerms())},extractionLiterals,extractionIneqs,false);
//            std::cout << "Generator rule ";generateP1.print();
            generatorProgram.addRule(generateP1);
            aspc::Rule generateP2 ({aspc::Atom(predicate_2,headLit.getTerms())},extractionLiterals,extractionIneqs,false);
//            std::cout << "Generator rule ";generateP2.print();
            generatorProgram.addRule(generateP2);
            // ---------------------------------------------------

            assert(extractionLiterals.size() == 1 && extractionIneqs.empty());
            std::unordered_set<std::string> headVars;
            headLit.addVariablesToSet(headVars);
            bool edb = analyzer->isEDB(extractionLiterals[0].getPredicateName()) || (datalogBody && extractionLiterals[0].getPredicateName().substr(0,4)=="Dom_");
            bool bound = extractionLiterals[0].isBoundedLiteral(headVars);
            aspc::Atom p1_head(predicate_1,headLit.getTerms());
            aspc::Atom p2_head(predicate_2,headLit.getTerms());

            // Adding constraint :- a, na.
            aspc::Rule bothTrue ({},{aspc::Literal(false,p1_head),aspc::Literal(false,p2_head)},{},false);
            completionProgram.addRule(bothTrue);
//            std::cout << "Propagator constraint ";bothTrue.print();

            if(!bound){
                // Adding projection rule proj :- body
                // if body is edb than this rule is evaluated as Datalog rule
                // otherwise it will be a propagator rule
                std::string proj_pred = "Proj_"+extractionLiterals[0].getPredicateName();
                aspc::Atom projected_head(proj_pred,headLit.getTerms());
                auto it = predicateId.emplace(proj_pred,predicateNames.size());
                if(it.second) predicateNames.push_back(proj_pred);

                aspc::Rule projectionRule ({projected_head},{extractionLiterals[0]},{},false);
                completionProgram.addRule(projectionRule);
//                std::cout << (edb ? "Datalog rule " : "Propagator rule ");projectionRule.print();
                extractionLiterals.clear();
                extractionLiterals.push_back(aspc::Literal(false,projected_head));
            }

            // extractionLiterals contains the body literal projected on head variables
            // Adding constraint :-body, not a, not na.
            aspc::Rule bothFalse ({},{extractionLiterals[0],aspc::Literal(true,p1_head),aspc::Literal(true,p2_head)},{},false);
//            std::cout << "Propagator constraint ";bothFalse.print();
            completionProgram.addRule(bothFalse);
            if(!edb && !analyzer->isJoinPredicate(extractionLiterals[0].getPredicateName())){
                // add constraint :- a, not body :-na, not body
                aspc::Literal support_literal(true,extractionLiterals[0].getAtom());
                aspc::Literal head_p1(false,aspc::Atom(predicate_1,headLit.getTerms()));
                aspc::Literal head_p2(false,aspc::Atom(predicate_2,headLit.getTerms()));

                aspc::Rule constraint_1({},{head_p1,support_literal},{},false);
                aspc::Rule constraint_2({},{head_p2,support_literal},{},false);

                completionProgram.addRule(constraint_1);
                completionProgram.addRule(constraint_2);

//                std::cout << "Propagator constraint ";constraint_1.print();
//                std::cout << "Propagator constraint ";constraint_2.print();
            }
        }
    }
    for(unsigned i=0; i<afterAggregate.getRulesSize(); i++) {
        if (skipRule.count(i)) continue;
        completionProgram.addRule(afterAggregate.getRule(i));
    }
    std::cout << "Applying standard completion on:"<<std::endl;
    for(unsigned i=0; i<completionProgram.getRulesSize(); i++){
        aspc::Rule rule = completionProgram.getRule(i);
        if(rule.isConstraint()) {
            propagatorsProgram.addRule(rule);
            //labeledPropgatorRules.push_back(labeledSingleHeadRules[i]);
            continue;
        }else if(rule.containsAggregate()){
            propagatorsProgram.addRule(rule);
            assert(rule.getBodyLiterals().size() <= 1);
            const aspc::Atom* head = &rule.getHead()[0];
            const aspc::Literal* body = rule.getBodyLiterals().size() == 0 ? NULL : &rule.getBodyLiterals()[0];

            aspc::Rule genAggId ({aspc::Atom(head->getPredicateName(),head->getTerms())},(body == NULL ? std::vector<aspc::Literal>({}) : std::vector<aspc::Literal>({*body})),{},false);
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
                if(analyzer->isEDB(bodyLiterals[k].getPredicateName()))
                    continue;
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