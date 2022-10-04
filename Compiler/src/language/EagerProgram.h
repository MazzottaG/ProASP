/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
/*
 *
 *  Copyright 2016 Bernardo Cuteri, Francesco Ricca.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

#ifndef EAGERPROGRAM_H_ASPC
#define EAGERPROGRAM_H_ASPC
#include <vector>
#include <map>
#include <list>
#include <set>
#include "Rule.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "Program.h"

namespace aspc {

class GeneratorGraph{
    private:
        GraphWithTarjanAlgorithm generatorDG;
        std::vector<std::vector<int>> generatorScc;
        bool buildGeneratorSCC=true;
        std::unordered_map<std::string, int> predicateIDs;
        std::unordered_map<int, std::string> predicateByID;
    public:
        void addNode(std::string pred){
            if(predicateIDs.count(pred)==0){
                predicateByID[predicateIDs.size()]=pred;
                predicateIDs[pred]=predicateIDs.size();
            }
            generatorDG.addNode(predicateIDs[pred]);
        }
        void addDependency(std::string head,std::string body){
            if(predicateIDs.count(head)==0){
                predicateByID[predicateIDs.size()]=head;
                predicateIDs[head]=predicateIDs.size();
            }
            if(predicateIDs.count(body)==0){
                predicateByID[predicateIDs.size()]=body;
                predicateIDs[body]=predicateIDs.size();
            }
            generatorDG.addEdge(predicateIDs[body],predicateIDs[head]);
        }
        void addRuleDependencies(const aspc::Rule& r){
            for(const aspc::Atom& h : r.getHead()){
                for(const aspc::Literal& b: r.getBodyLiterals()){
                    if(b.isPositiveLiteral()){
                        addDependency(h.getPredicateName(),b.getPredicateName());
                    }
                }
            }
        }
        GraphWithTarjanAlgorithm& getDG(){return generatorDG;}
        std::string getPredicateName(int predId){return predicateByID[predId];}
        int getPredicateId(std::string pred){return predicateIDs[pred];}
};
    class EagerProgram {
    public:
        EagerProgram();
        virtual ~EagerProgram();
        void addRule(const aspc::Rule & r,bool saveAggregateDependencies=false);
        void addDependencies(const aspc::Rule& r,bool saveAggregateDependencies=false);

        const std::vector<std::vector<int>>& positiveSCC();
        const std::vector<std::vector<int>>& SCC();

        int size()const {return rules.size();}
        const aspc::Rule& getRule(int id)const {if(id < size()) return rules[id];}
        std::vector<aspc::Rule> getRules()const {return rules;}
        GraphWithTarjanAlgorithm& getDG() {return DG;}
        GraphWithTarjanAlgorithm& getPositiveDG() {return positiveDG;}
        std::string getPredicateName(int predId){return predicateByID[predId];}
        int getPredicateId(std::string pred){return predicateIDs[pred];}
        std::unordered_map<int,std::unordered_set<std::string>> getRecursiveComponents();
        std::unordered_map<std::string,int> getRulesCountForPredicates();
        void print()const;
        void printComponent()const;
        void addGeneratorDependenciesForRule(const aspc::Rule& r){genGraph.addRuleDependencies(r);}
        void addGeneratorDependecy(std::string head,std::string body){genGraph.addDependency(head,body);}
        void addGeneratorNode(std::string pred){genGraph.addNode(pred);}
        GraphWithTarjanAlgorithm& getGeneratorDG(){return genGraph.getDG();}
        std::string getGenPredicateName(int predId){return genGraph.getPredicateName(predId);}
        int getGeneratorPredicateId(std::string pred){return genGraph.getPredicateId(pred);}
    private:
        std::vector<aspc::Rule> rules; //only rules are compiled
        std::unordered_map<std::string, int> predicateIDs;
        std::unordered_map<int, std::string> predicateByID;

        GraphWithTarjanAlgorithm positiveDG;
        std::vector<std::vector<int>> positiveScc;
        bool buildPositiveSCC=true;
        
        GraphWithTarjanAlgorithm DG;
        std::vector<std::vector<int>> scc;
        bool buildSCC=true;
        
        GeneratorGraph genGraph;
    };
}

#endif

