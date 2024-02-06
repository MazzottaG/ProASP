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
#include "Program.h"

using namespace std;

aspc::Program::Program():rules({}),facts({}),predicates({}),aggregatePredicates({}),rulesForPredicate({}),rules_by_type({}),stratified(true),tight(true) {
}
aspc::Program::Program(const aspc::Program& p):facts(p.facts),predicates(p.predicates),aggregatePredicates(p.aggregatePredicates),stratified(p.stratified),tight(p.tight){
    for(int i=0;i<p.getRulesSize();i++){
        addRule(p.getRule(i));
    }
    for(auto pair: p.rulesForPredicate){
        rulesForPredicate[pair.first]=pair.second;
    }
    for(auto pair: p.rules_by_type){
        rules_by_type[pair.first]=pair.second;
    }
}

aspc::Program::~Program() {

}
bool aspc::Program::isHeadPredicate(std::string predicate){
    return rulesForPredicate.find(predicate) != rulesForPredicate.end();
}
const std::vector<unsigned>& aspc::Program::getRulesForPredicate(std::string predicate) {
    return rulesForPredicate[predicate];
}
void aspc::Program::addRule(const Rule & r) {
    for(const aspc::Atom& a: r.getHead()){
        rulesForPredicate[a.getPredicateName()].push_back(rules.size());
    }
    rules.push_back(r);
    for (const Literal & literal : r.getBodyLiterals()) {
        rules_by_type[r.getType()][literal.getPredicateName()].insert(rules.size()-1);
    }

}

void aspc::Program::addFact(const aspc::Atom & r) {
    facts.push_back(r);
}

const aspc::Rule & aspc::Program::getRule(unsigned i) const {
    return rules[i];
}

unsigned aspc::Program::getRulesSize() const {
    return rules.size();
}

const vector<aspc::Rule>& aspc::Program::getRules() const{
    return rules;
}

vector<aspc::Rule>& aspc::Program::getRules() {
    return rules;
}

const aspc::Atom & aspc::Program::getFact(unsigned i) const {
    return facts[i];
}

const vector<aspc::Atom>& aspc::Program::getFacts() const {
    return facts;
}

unsigned aspc::Program::getFactsSize() const {
    return facts.size();
}

const map<RuleType, map<string, set<unsigned> > >& aspc::Program::getRulesByType() const {
    return rules_by_type;
}


const set<unsigned> & aspc::Program::getRulesByTypeAndPredicateName(const string & predicateName, RuleType type) const {
    return rules_by_type.at(type).at(predicateName);
}

void aspc::Program::clearFacts() {
    facts.clear();
}
void aspc::Program::printRuleForComponent()const{
    for(auto pair : rulesForPredicate){
        std::cout << "Predicate "<<pair.first<<std::endl;
        for(unsigned ruleIndex : pair.second){
            rules[ruleIndex].print();
        }
    }
}
void aspc::Program::print() const {
    for (const Rule & rule : rules) {
        rule.print();
    }
}

void aspc::Program::addPredicate(const string& name, const unsigned ariety) {
    predicates.insert(pair<string, unsigned>(name,ariety));
}

const set<pair<string, unsigned> >& aspc::Program::getPredicates() const {
    return predicates;
}
const std::set< std::pair<std::string, unsigned> >& aspc::Program::getAggregatePredicates() const{
    return aggregatePredicates;
}
void aspc::Program::addAggregatePredicate(const std::string& name, const unsigned ariety){
    aggregatePredicates.insert(pair<string, unsigned>(name,ariety));
}
void aspc::Program::addArithmeticRelationToRule(unsigned index,aspc::ArithmeticRelationWithAggregate r){
    rules[index].addArithmeticRelationsWithAggregate(r);
}
void aspc::Program::changeCompareTypeToRule(unsigned index,int aggrIndex,aspc::ComparisonType type){
    rules[index].changeCompareTypeToAggregate(aggrIndex,type);
}
set<string> aspc::Program::getBodyPredicates() const {

    set<string> res;
    for(const Rule & r:rules) {
       for(const Literal & l: r.getBodyLiterals()) {
           res.insert(l.getPredicateName());
       }
       //added for aggregate
       for(ArithmeticRelationWithAggregate aggr : r.getArithmeticRelationsWithAggregate()){
           for(Literal l : aggr.getAggregate().getAggregateLiterals()){
               res.insert(l.getPredicateName());
           }
       }
    }
    return res;
}

set<string> aspc::Program::getHeadPredicates() const {

    set<string> res;
    for(const Rule & r:rules) {
       for(const Atom & a: r.getHead()) {
           res.insert(a.getPredicateName());
       }
    }
    return res;
}
bool aspc::Program::hasConstraintWithLiteral() const{
    for(const Rule & r: rules) {
        if(r.isConstraint() && r.containsLiteral()) {
            return true;
        }
    }
    return false;
}

bool aspc::Program::hasConstraint() const {
    for(const Rule & r: rules) {
        if(r.isConstraint()) {
            return true;
        }
    }
    return false;

}

bool aspc::Program::clear(){
    rules.clear();
    facts.clear(); 
    predicates.clear();
    aggregatePredicates.clear();
    rules_by_type.clear();

}
