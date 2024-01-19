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
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   ArithmeticRelationWithAggregate.cpp
 * Author: BLIND
 * 
 * Created on 20 marzo 2020, 9.57
 */

#include "ArithmeticRelationWithAggregate.h"
#include "../utils/SharedFunctions.h"
aspc::ArithmeticRelationWithAggregate::ArithmeticRelationWithAggregate(const aspc::ArithmeticRelationWithAggregate& other ){
    formulaIndex = other.formulaIndex;
    aggregate = other.aggregate;
    guard = other.guard;
    comparisonType = other.comparisonType;
    negated = other.negated;
    plusOne = other.plusOne;
}
aspc::ArithmeticRelationWithAggregate::ArithmeticRelationWithAggregate(bool isLower, const aspc::ArithmeticExpression & expression, const aspc::Aggregate & aggregate_, aspc::ComparisonType compare,bool isNegated):aggregate(aggregate_.getAggregateLiterals(),aggregate_.getAggregateInequalities(),aggregate_.getAggregateVariables(),aggregate_.getAggregateFunction()),guard(expression),negated(isNegated){
    //guard = aspc::ArithmeticExpression(expression);

    plusOne=false;
    if(isLower){
        if(compare == aspc::GT)
            comparisonType = aspc::LT;
        else if(compare == aspc::GTE)
            comparisonType = aspc::LTE;
        else if(compare == aspc::LT)
            comparisonType = aspc::GT;
        else if(compare == aspc::LTE)
            comparisonType = aspc::GTE;
        else comparisonType = compare;
    }else{
        comparisonType = compare;
    }
    if(comparisonType == aspc::GT){
        comparisonType = aspc::GTE;
        plusOne=true;
    }else if(comparisonType == aspc::LT){
        std::cout << "Switching sign: it was " << (negated ? "" : " not ") << "negated and now it is " << (!negated ? "" : " not ") << "negated" << std::endl;
        negated=!negated;
        comparisonType = aspc::GTE;
    }else if(comparisonType==aspc::LTE){
        std::cout << "Switching sign: it was " << (negated ? "" : " not ") << "negated and now it is " << (!negated ? "" : " not ") << "negated" << std::endl;
        negated=!negated;
        comparisonType = aspc::GTE;
        plusOne=true;
    }

    /*for(const aspc::ArithmeticRelation& r : aggregate_.getAggregateNormalizedInequalities()){
        if(guard.getTerm1() == r.getLeft().getStringRep() && guard.getTerm1()[0]>='A'&& guard.getTerm1()[0]<='Z'){
           guard.setTerm1(r.getRight().getStringRep()); 
        }else if(!guard.isSingleTerm() && guard.getTerm2() == r.getLeft().getStringRep() && guard.getTerm2()[0]>='A'&& guard.getTerm2()[0]<='Z'){
            guard.setTerm2(r.getRight().getStringRep());
        }
    }*/

}           

bool aspc::ArithmeticRelationWithAggregate::isBoundedRelation(const std::unordered_set<std::string> & boundVariables) const {
    
    for (const std::string & v : guard.getAllTerms()) {
        if (isVariable(v) && !boundVariables.count(v)) {
            return false;
        }
    }
    
    return true;
}

bool aspc::ArithmeticRelationWithAggregate::isBoundedLiteral(const std::unordered_set<std::string> &) const {
    
    return false;
}
bool aspc::ArithmeticRelationWithAggregate::isBoundedValueAssignment(const std::unordered_set<std::string> & boundVariables) const {
    
    //#count{..}=X #count{..}=X+5 se X non è bound è un boundedValueAssignment 
    //#count{..}=X+Y se entrambe non sono bound allora non è un boundedValueAssignment
    
    if(this->comparisonType != aspc::EQ )
        return false;
    
    if(guard.isProduct())
        return false;

    unsigned unassignedVariables=0;
    for (const std::string & v : guard.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            unassignedVariables++;
        }
    }
    return unassignedVariables == 1;
    
}
std::string aspc::ArithmeticRelationWithAggregate::getAssignedVariable(std::unordered_set<std::string> & set) const {
    assert(isBoundedValueAssignment(set));
    if(guard.isSingleTerm()){
        if(isVariable(guard.getTerm1()) && set.count(guard.getTerm1())==0)
            return guard.getTerm1();
    }else{
        if(isVariable(guard.getTerm1()) && set.count(guard.getTerm1())==0)
            return guard.getTerm1();
        else if(isVariable(guard.getTerm2()) && set.count(guard.getTerm2())==0)
            return guard.getTerm2();
    }
    return "";
}
std::string aspc::ArithmeticRelationWithAggregate::getAssignmentAsString(std::unordered_set<std::string> & set) const {
    assert(isBoundedValueAssignment(set));
    
    if(guard.isSingleTerm()){
        if(isVariable(guard.getTerm1()) && set.count(guard.getTerm1())==0)
            return guard.getTerm1()+" = sum";
    }else{
        if(isVariable(guard.getTerm1()) && set.count(guard.getTerm1())==0)
            return guard.getTerm1()+" = sum "+(guard.getOperation() == '+' ? "-" : "+")+guard.getTerm2();
        else if(isVariable(guard.getTerm2()) && set.count(guard.getTerm2())==0)
            if(guard.getOperation() == '-')
                return guard.getTerm2() +" = "+ guard.getTerm1()+" - sum";
            return guard.getTerm2() +" = sum + "+ guard.getTerm1();
    }
    return "";
}
bool aspc::ArithmeticRelationWithAggregate::isSafeAggSet() const {
    std::unordered_set<std::string> occuringVariables;
    addPositiveBodyVariablesToSet(occuringVariables);
    for(const aspc::Literal& l : aggregate.getAggregateLiterals()){
        if(l.isNegated() && !l.isBoundedLiteral(occuringVariables)) return false;
    }
    for(const aspc::ArithmeticRelation& ineq: aggregate.getAggregateInequalities()){
        if(!ineq.isBoundedRelation(occuringVariables)) return false;
    }
    return true;
}
void aspc::ArithmeticRelationWithAggregate::addPositiveBodyVariablesToSet(std::unordered_set<std::string> & set) const {
    for(const aspc::Literal& l : aggregate.getAggregateLiterals()){
        if(l.isNegated()) continue;
        l.addVariablesToSet(set);
    }
    bool added=true;
    while(added){
        added=false;
        for(const aspc::ArithmeticRelation& ineq: aggregate.getAggregateInequalities()){
            if(ineq.isBoundedValueAssignment(set)){
                std::string var = ineq.getAssignedVariable(set);
                auto it = set.emplace(var);
                if(it.second)
                    added=true;
            }
        }
    }
}
void aspc::ArithmeticRelationWithAggregate::addVariablesToSet(std::unordered_set<std::string> & set) const {
    for(const aspc::Literal& l : aggregate.getAggregateLiterals()){
        l.addVariablesToSet(set);
    }
    for(const aspc::ArithmeticRelation& ineq: aggregate.getAggregateInequalities()){
        ineq.addVariablesToSet(set);
    }
    for(std::string term: guard.getAllTerms()){
        if(isVariable(term)){
            set.insert(term);
        }
    }
}
bool aspc::ArithmeticRelationWithAggregate::isPositiveLiteral() const {
    return false;
}
void aspc::ArithmeticRelationWithAggregate::print() const {
    std::string negation = negated ? "not":"";
    std::cout<<negation<<" ";
    aggregate.print();
    std::cout << " " << aspc::ArithmeticRelation::comparisonType2String[comparisonType] << " " << guard;
    std::string plus = plusOne ? "+1":"";
    std::cout<<plus;
    
}
bool aspc::ArithmeticRelationWithAggregate::isLiteral() const {
    return false;
}
bool aspc::ArithmeticRelationWithAggregate::containsAggregate() const{
    return true;
}
unsigned aspc::ArithmeticRelationWithAggregate::firstOccurrenceOfVariableInLiteral(const std::string &) const{
    return -1;
}
std::string aspc::ArithmeticRelationWithAggregate::getStringRep() const{
    std::string rep;
    for(std::string v: aggregate.getAggregateVariables()){
        rep+=v+"_";
    }
    rep+=getJoinTupleName();
    for(const aspc::ArithmeticRelation& ineq : aggregate.getAggregateInequalities()){
        rep+=ineq.getStringRep();
    }
    rep+=getCompareTypeAsString()+guard.getStringRep();
    return rep;
}

aspc::ArithmeticRelationWithAggregate::~ArithmeticRelationWithAggregate() {
}

