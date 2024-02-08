//
// Created by giuseppe mazzotta on 06/02/24.
//

#include "DependencyManager.h"
void DependencyManager::buildDependecyGraph(const aspc::Program& program){
    predicateToId.clear();
    idToPredicate.clear();
    dependencyGraph = GraphWithTarjanAlgorithm();

    for(unsigned ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
        const aspc::Rule* rule = &program.getRule(ruleId);
        // Map predicates to nodes
        const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
        for(unsigned bId = 0; bId<body->size(); bId++){
            // if(!body->at(bId)->isLiteral() && !body->at(bId)->containsAggregate()) continue;
            if(body->at(bId)->isLiteral()){
                const aspc::Literal* literal = (const aspc::Literal*) body->at(bId);
                if(!predicateToId.count(literal->getPredicateName())){
                    predicateToId[literal->getPredicateName()]=idToPredicate.size();
                    dependencyGraph.addNode(idToPredicate.size());
                    idToPredicate.push_back(literal->getPredicateName());
                }
            }else if(body->at(bId)->containsAggregate()){
                addAggregatePredicates((const aspc::ArithmeticRelationWithAggregate*)body->at(bId));
            }

        }
        if(rule->isConstraint()) continue;
        const std::vector<aspc::Atom>* head = &rule->getHead();
        for(unsigned hId = 0; hId<head->size(); hId++){
            const aspc::Atom* h = &head->at(hId);
            if(!predicateToId.count(h->getPredicateName())){
                predicateToId[h->getPredicateName()]=idToPredicate.size();
                dependencyGraph.addNode(idToPredicate.size());
                idToPredicate.push_back(h->getPredicateName());
            }
        }
        // Add body to head dependencies
        for(unsigned bId = 0; bId<body->size(); bId++){
            if(body->at(bId)->isLiteral()){
                const aspc::Literal* literal = (const aspc::Literal*) body->at(bId);
                int bPredId = predicateToId[literal->getPredicateName()];
                for(unsigned hId = 0; hId<head->size(); hId++){
                    const aspc::Atom* h = &head->at(hId);
                    int hPredId = predicateToId[h->getPredicateName()];
                    dependencyGraph.addEdge(bPredId,hPredId);
                }
            }else if(body->at(bId)->containsAggregate()){
                addAggregateDependency(head,(const aspc::ArithmeticRelationWithAggregate*)body->at(bId));
            }
        }
    }
    scc = dependencyGraph.SCC();
}
void DependencyManager::addAggregatePredicates(const aspc::ArithmeticRelationWithAggregate* aggrRelation){
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        if(!predicateToId.count(literal.getPredicateName())){
            predicateToId[literal.getPredicateName()]=idToPredicate.size();
            dependencyGraph.addNode(idToPredicate.size());
            idToPredicate.push_back(literal.getPredicateName());
        }
    }
}
void DependencyManager::addAggregateDependency(const std::vector<aspc::Atom>* head,const aspc::ArithmeticRelationWithAggregate* aggrRelation){
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        int bPredId = predicateToId[literal.getPredicateName()];
        for(unsigned hId = 0; hId<head->size(); hId++){
            const aspc::Atom* h = &head->at(hId);
            int hPredId = predicateToId[h->getPredicateName()];
            dependencyGraph.addEdge(bPredId,hPredId);
        }
    }
}
std::pair<std::vector<std::pair<aspc::Rule,unsigned> >,bool> DependencyManager::checkComponent(const aspc::Program& prg, int component_id){
    aspc::Program inputProgram(prg);
//    std::cout << "Checking component:";
//    for(int pred : scc[component_id]) std::cout << " " << getPredicateName(pred);
//    std::cout << std::endl;
    bool rewrite = scc[component_id].size() == 2;
    std::vector<std::pair<aspc::Rule,unsigned> > result;
    if(!rewrite) return std::make_pair(result,false);
    std::string pred_1 = getPredicateName(scc[component_id][0]);
    std::string pred_2 = getPredicateName(scc[component_id][1]);
    auto rules_p1 = inputProgram.getRulesForPredicate(pred_1);
    auto rules_p2 = inputProgram.getRulesForPredicate(pred_2);
    if(rules_p1.size()!=1 || rules_p2.size()!=1)
        return std::make_pair(result,false);

    const aspc::Rule* r_p1 = &inputProgram.getRule(rules_p1[0]);
    const aspc::Rule* r_p2 = &inputProgram.getRule(rules_p2[0]);

    if(r_p1->getHead()[0].getAriety() != r_p2->getHead()[0].getAriety())
        return std::make_pair(result,false);
    if(r_p1->containsAggregate() || r_p2->containsAggregate())
        return std::make_pair(result,false);
    if(r_p1->getFormulas().size() != r_p2->getFormulas().size())
        return std::make_pair(result,false);
    std::vector< std::unordered_map<std::string,int> > predicate_occurrences;
    std::vector<const aspc::Rule*> rules;
    rules.push_back(r_p1);
    rules.push_back(r_p2);
    for(const aspc::Rule* rule :  rules){
        std::string searchPred = rule->getHead()[0].getPredicateName() == pred_1 ? pred_2 : pred_1;
        int count = 0;
        predicate_occurrences.push_back(std::unordered_map<std::string,int>());
        for(const aspc::Literal& literal: rule->getBodyLiterals()){
            if(literal.getPredicateName() == searchPred){
                if(literal.isPositiveLiteral()) { return std::make_pair(result,false);}
                if(++count > 1) {return std::make_pair(result,false);}
            }
            if(literal.getPredicateName() == pred_1 || literal.getPredicateName() == pred_2 || literal.isNegated())
                continue;
            auto it = predicate_occurrences.back().find(literal.getPredicateName());
            if(it == predicate_occurrences.back().end())
                predicate_occurrences.back()[literal.getPredicateName()]=1;
            else
                predicate_occurrences.back()[literal.getPredicateName()]=it->second+1;
        }
        if(!rewrite || count == 0){return std::make_pair(result,false);}
    }
    for(unsigned i=0; i<predicate_occurrences.size(); i++){
        for(unsigned j=0; j<predicate_occurrences.size(); j++) {
            if(i!=j){
                for(auto pair:predicate_occurrences[i])
                    if(predicate_occurrences[j][pair.first]!=pair.second)
                        return std::make_pair(result,false);
            }
        }
    }

    auto pair = getVariableMapping(r_p1,r_p2);
    if(pair.second){
        std::unordered_set<std::string> preds;
        preds.insert(pred_1);
        preds.insert(pred_2);
        if(r_p1->cloneWithRenamedVariables(pair.first).equalBodyExpect(*r_p2,preds)){
//            std::cout << "Variable renaming applied for:"<<std::endl;
//            std::cout << "   ";r_p1->print();
//            std::cout << "   ";r_p2->print();

            std::vector<aspc::Literal> lits;
            for(const aspc::Literal& lit : r_p2->getBodyLiterals()){
                if(lit.getPredicateName() == pred_1 || lit.getPredicateName() == pred_2) continue;
                lits.push_back(lit);
            }
            aspc::Literal not_head_r_p2 (true,r_p2->getHead()[0]);
            aspc::Atom head_clone_r_p1 (pred_1,r_p2->getHead()[0].getTerms());

            lits.push_back(not_head_r_p2);
            std::vector<aspc::Atom> head;
            head.push_back(head_clone_r_p1);
            aspc::Rule clone_r_p1(head,lits,r_p2->getArithmeticRelations(),false);
//            std::cout << "Otained rules:"<<std::endl;
//            std::cout << "   ";clone_r_p1.print();
//            std::cout << "   ";r_p2->print();

            result.push_back(std::make_pair(clone_r_p1,rules_p1[0]));
            result.push_back(std::make_pair(*r_p2,rules_p2[0]));
            return std::make_pair(result,true);
        }
    }
    return std::make_pair(result,false);
}
std::pair<std::unordered_map<std::string,std::string>,bool> DependencyManager::getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const{
    std::unordered_map<std::string,std::string> variableMapping;
    bool foundMapping = true;
    std::vector< std::unordered_map< std::string,std::multiset<int> > > ruleVariableMapping;
    std::unordered_set<std::string> component;
    component.insert(r1->getHead()[0].getPredicateName());
    component.insert(r2->getHead()[0].getPredicateName());

    std::unordered_map<std::string,int> indexMapping;
    std::vector<std::string> indices;

    std::vector<const aspc::Rule*> rules;
    rules.push_back(r1);
    rules.push_back(r2);
    std::string pred_prefix = "h_"+r1->getHead()[0].getPredicateName()+"_"+r2->getHead()[0].getPredicateName();
    for(const aspc::Rule* rule : rules){
        ruleVariableMapping.push_back(std::unordered_map< std::string,std::multiset<int> >());
        for(const aspc::Literal& literal : rule->getBodyLiterals()){
            if(!literal.isNegated()){
                for(unsigned k=0;k<literal.getAriety();k++){
                    if(literal.isVariableTermAt(k)){
                        std::string index = literal.getPredicateName()+"_"+std::to_string(k);
                        auto it = indexMapping.find(index);
                        int indexId=-1;
                        if(it == indexMapping.end()){
                            indexId=indices.size();
                            indexMapping[index]=indices.size();
                            indices.push_back(index);
                        }else indexId = it->second;

                        ruleVariableMapping.back()[literal.getTermAt(k)].insert(indexId);
                    }
                }
            }
        }
        aspc::Atom head_atom(rule->getHead()[0]);
        for(unsigned k=0;k<head_atom.getAriety();k++){
            if(head_atom.isVariableTermAt(k)){
                std::string index = pred_prefix+"_"+std::to_string(k);
                auto it = indexMapping.find(index);
                int indexId=-1;
                if(it == indexMapping.end()){
                    indexId=indices.size();
                    indexMapping[index]=indices.size();
                    indices.push_back(index);
                }else indexId = it->second;

                ruleVariableMapping.back()[head_atom.getTermAt(k)].insert(indexId);
            }
        }
        //std::cout << "Rule variable mapping computed"<<std::endl;
    }
    std::map<std::vector<int>,std::vector< std::vector<std::string> > > indicesToVariable;
    for(unsigned rule_index = 0; rule_index<ruleVariableMapping.size(); rule_index++){
        /*std::cout << "rule "<<rule_index<<" ";
        if(rule_index == 0) r1->print();
        else r2->print();*/

        for(auto pair : ruleVariableMapping[rule_index]){
            std::string variable = pair.first;
            std::vector<int> foundIndices(pair.second.begin(),pair.second.end());
            /*std::cout << "  "<<variable << "-> {";
            for(int i: foundIndices) std::cout << " "<<indices[i];
            std::cout << "}\n";*/
            auto it = indicesToVariable.find(foundIndices);
            std::vector<std::string> emptyVars;
            std::vector< std::vector<std::string> > init;
            init.push_back(emptyVars);
            init.push_back(emptyVars);

            if(it == indicesToVariable.end()){
                indicesToVariable[foundIndices]=init;
            }
            indicesToVariable[foundIndices][rule_index].push_back(variable);
        }
    }
    for(auto pair: indicesToVariable){
        if(pair.second[0].size()!=1 || pair.second[1].size()!=1){
            return std::make_pair(variableMapping,false);
        }
        variableMapping[pair.second[0][0]]=pair.second[1][0];
        /*
        std::cout << "      {";
        for(int i : pair.first) std::cout << " " << indices[i];
        std::cout << "} -> [";
        for(int i=0;i<pair.second.size();i++){
            if(i>0) std::cout << ", ";
            std::cout << "[";
            for(int j=0;j<pair.second[i].size();j++){
                if(j>0) std::cout << ", ";
                std::cout << pair.second[i][j];
            }
            std::cout << "]";
        }
        std::cout << "]"<<std::endl;
        */

    }
    return std::make_pair(variableMapping,true);
}