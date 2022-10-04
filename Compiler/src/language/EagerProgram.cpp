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

#include <map>
#include <list>
#include <set>
#include <iostream>
#include "EagerProgram.h"

using namespace std;

aspc::EagerProgram::EagerProgram() {

}

aspc::EagerProgram::~EagerProgram() {

}

void aspc::EagerProgram::addRule(const Rule & r,bool saveAggregateDependencies) {
    rules.push_back(r);
    
    //adding edges to dependency graph
    for (const aspc::Atom& a : r.getHead()) {
        int currentHeadId = predicateIDs.size();
        unordered_map<string, int>::iterator i = predicateIDs.find(a.getPredicateName());
        if (i != predicateIDs.end())
            currentHeadId = i->second;
        else {
            predicateIDs[a.getPredicateName()] = currentHeadId;
            predicateByID[currentHeadId] = a.getPredicateName();
        }
    }
    for (const aspc::Literal& l : r.getBodyLiterals()) {
        int currentBodyId = predicateIDs.size();
        unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
        if (i != predicateIDs.end())
            currentBodyId = i->second;
        else {
            predicateIDs[l.getPredicateName()] = currentBodyId;
            predicateByID[currentBodyId] = l.getPredicateName();
        }
    }
                
        
    for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
        for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
            int currentBodyId = predicateIDs.size();
            unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
            if (i != predicateIDs.end())
                currentBodyId = i->second;
            else {
                predicateIDs[l.getPredicateName()] = currentBodyId;
                predicateByID[currentBodyId] = l.getPredicateName();
            }
        }
    }
    if(!r.isConstraint()) addDependencies(r,saveAggregateDependencies);
}

void aspc::EagerProgram::addDependencies(const aspc::Rule& r,bool saveAggregateDependencies){
    
    if(!r.containsAggregate()||saveAggregateDependencies){
        for (const aspc::Atom& a : r.getHead()) {
            int currentHeadId = predicateIDs.size();
            unordered_map<string, int>::iterator i = predicateIDs.find(a.getPredicateName());
            currentHeadId = i->second;
            for (const aspc::Literal& l : r.getBodyLiterals()) {
                int currentBodyId = predicateIDs.size();
                unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
                currentBodyId = i->second;
                if(l.isPositiveLiteral()){
                    positiveDG.addEdge(currentBodyId, currentHeadId);
                }
                DG.addEdge(currentBodyId, currentHeadId);
            }
            
            for(const aspc::ArithmeticRelationWithAggregate& aggrRelation: r.getArithmeticRelationsWithAggregate()){
                for (const aspc::Literal& l : aggrRelation.getAggregate().getAggregateLiterals()) {
                    int currentBodyId = predicateIDs.size();
                    unordered_map<string, int>::iterator i = predicateIDs.find(l.getPredicateName());
                    currentBodyId = i->second;
                    if(l.isPositiveLiteral())
                        positiveDG.addEdge(currentBodyId, currentHeadId);
                    DG.addEdge(currentBodyId, currentHeadId);
                }
            }
        }
    }
}

const std::vector<std::vector<int>>& aspc::EagerProgram::positiveSCC(){
    if(buildPositiveSCC){
        positiveScc=positiveDG.SCC();
        buildPositiveSCC=false;
    }
    return positiveScc;
}
const std::vector<std::vector<int>>& aspc::EagerProgram::SCC(){
    if(buildSCC){
        scc=DG.SCC();
        buildSCC=false;
    }
    return scc;
}
std::unordered_map<int,std::unordered_set<std::string>> aspc::EagerProgram::getRecursiveComponents(){
    std::unordered_map<int,std::unordered_set<std::string>> recursive;
    auto components = positiveSCC();
    for(int i=components.size()-1;i>=0; i--){
        bool add=false;
        if(components[i].size()>1)
            add=true;
        else{
            for(int adj : positiveDG.getAdjForNode(components[i][0])){
                if(adj == components[i][0]){
                    add=true;
                    break;
                }
            }
        }
        if(add){
            recursive.insert({i,std::unordered_set<std::string>()});
            for(int pred : components[i]){
                auto it = predicateByID.find(pred);
                if(it!=predicateByID.end()){
                    recursive[i].insert(it->second);
                }
            }
        }
        
    }

    return recursive;

}
std::unordered_map<std::string,int> aspc::EagerProgram::getRulesCountForPredicates(){
    std::unordered_map<std::string,int> result;
    for(int i=0; i< rules.size(); i++){
        if(!rules[i].isConstraint()){
            const aspc::Atom* head = &rules[i].getHead()[0];
            if(result.count(head->getPredicateName())==0)
                result.insert({head->getPredicateName(),0});
            result[head->getPredicateName()]+=1;
        }
    }    
    return result;
}
void aspc::EagerProgram::print()const{
    std::cout << "Program" << std::endl;
    for(const aspc::Rule& r : rules){
        r.print();
    }
}
void aspc::EagerProgram::printComponent()const{
    for(int component = scc.size()-1;component>=0;component--){
        std::cout << "Component "<<component<<": ";
        for(int pred : scc.at(component)){
            auto it =predicateByID.find(pred);
            if(it!=predicateByID.end()){
                std::cout << it->second<<" ";
            }
        }
        std::cout<<std::endl;
    }
}

