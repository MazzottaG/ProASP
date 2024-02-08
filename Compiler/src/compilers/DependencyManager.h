//
// Created by giuseppe mazzotta on 06/02/24.
//

#ifndef COMPILER_DEPENDENCYMANAGER_H
#define COMPILER_DEPENDENCYMANAGER_H
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../language/Program.h"

class DependencyManager {

    private:
        GraphWithTarjanAlgorithm dependencyGraph;
        std::vector<std::string> idToPredicate;
        std::unordered_map<std::string,unsigned> predicateToId;

        void addAggregatePredicates(const aspc::ArithmeticRelationWithAggregate* aggrRelation);
        void addAggregateDependency(const std::vector<aspc::Atom>* head,const aspc::ArithmeticRelationWithAggregate* aggrRelation);
        std::vector< std::vector<int> > scc;

    public:
        DependencyManager(){}
        void buildDependecyGraph(const aspc::Program& p);
        std::vector< std::vector<int> > getSCC()const {return scc;}
        std::string getPredicateName(int pred) {return idToPredicate[pred];}
        int getPredicateId(std::string pred) {return predicateToId[pred];}
        bool existsEdge(unsigned from,unsigned to){return dependencyGraph.existsEdge(from,to);}
        void addNewPredicate(std::string predicate){
            predicateToId[predicate]=idToPredicate.size();
            idToPredicate.push_back(predicate);
        }
        std::pair< std::vector<std::pair<aspc::Rule,unsigned> >,bool> checkComponent(const aspc::Program& inputProgram, int component_id);
        std::pair<std::unordered_map<std::string,std::string>,bool> getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const;
        const std::unordered_map<std::string,unsigned> getPredicateToId()const {return predicateToId;}
        const std::vector<std::string> getIdToPredicate()const {return idToPredicate;}

};


#endif //COMPILER_DEPENDENCYMANAGER_H
