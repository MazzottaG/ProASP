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