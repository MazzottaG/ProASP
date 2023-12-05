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
 * File:   Aggregate.cpp
 * Author: BLIND
 * 
 * Created on 17 marzo 2020, 17.20
 */

#include "Aggregate.h"
#include <iostream>
#include "../utils/SharedFunctions.h"


std::map<std::string,aspc::AggregateFunction> string2AggregateFunction = {
    {"#count", aspc::COUNT},
    {"#sum", aspc::SUM},
    {"#max", aspc::MAX},
    {"#min", aspc::MIN}

};

std::map<aspc::AggregateFunction,std::string> aggregateFunction2String = {
    {aspc::COUNT,"#count"},
    {aspc::SUM,"#sum"},
    {aspc::MAX,"#max"},
    {aspc::MIN,"#min"}

};
aspc::Aggregate::Aggregate(){
    
}


aspc::Aggregate::Aggregate(const std::vector<aspc::Literal> & literals, const std::vector<aspc::ArithmeticRelation>& inequalities_, const std::vector<std::string> & variables, std::string function): aggregateVariables(variables), aggregateFunction(string2AggregateFunction[function]){ 
    for(const aspc::Literal& l : literals){
        aggregateLiterals.push_back(aspc::Literal(l));
    }
    for(const aspc::ArithmeticRelation& ineq : inequalities_){
        inequalities.push_back(aspc::ArithmeticRelation(ineq.getLeft(),ineq.getRight(),ineq.getComparisonType()));
    }
}
aspc::Aggregate& aspc::Aggregate::operator=(const aspc::Aggregate& o){
    this->aggregateLiterals.clear();
    for(aspc::Literal l : o.aggregateLiterals){
        this->aggregateLiterals.push_back(l);
    }
    this->inequalities.clear();
    for(aspc::ArithmeticRelation ineq : o.inequalities){
        this->inequalities.push_back(ineq);
    }
    this->normalized_inequalities.clear();
    for(aspc::ArithmeticRelation ineq : o.normalized_inequalities){
        this->normalized_inequalities.push_back(ineq);
    }
    this->aggregateVariables.clear();
    for(std::string v: o.aggregateVariables)
        this->aggregateVariables.push_back(v);
    
    this->aggregateFunction = o.aggregateFunction;
    this->tupleName = o.tupleName;
    this->aggregateLiteralsProjection.clear();
    for(std::string proj: o.aggregateLiteralsProjection){
        this->aggregateLiteralsProjection.push_back(proj);
    }
    return *this;
}
std::string aspc::Aggregate::aggrVarsToString()const{
    std::string aggrVars;
    for(std::string v : aggregateVariables){
        aggrVars+=v+"_";
    }
    return aggrVars;
}   
std::unordered_map<aspc::ComparisonType,std::string> convertToWord={
    {aspc::GT,"GT"},
    {aspc::GTE,"GTE"},
    {aspc::LTE,"LTE"},
    {aspc::LT,"LT"},
    {aspc::EQ,"EQ"},
    {aspc::NE,"NE"}
};
std::unordered_map<char,std::string> convertToWordArithmeticOp={
    {'+',"PLUS"},
    {'-',"MINUS"},
    {'*',"TIMES"},
    {'/',"DIV"}
};
unsigned aspc::Aggregate::getFirstVarIndex()const{
    for(int k =0; k<aggregateLiterals[0].getAriety();k++){
        if(aggregateLiterals[0].isVariableTermAt(k) && aggregateLiterals[0].getTermAt(k) == aggregateVariables[0])
            return k;
    }
    return 0;
}
void aspc::Aggregate::computeJoinTupleName(){
    tupleName="";
    // for(std::string v : aggregateVariables){
    //     tupleName+=v+"_";
    // }
    for(const aspc::Literal& l : aggregateLiterals){
        if(l.isNegated())
            tupleName+="not_";
        tupleName+=l.getPredicateName()+"_";
        for(int i=0;i<l.getAriety();i++){
            if(!l.isVariableTermAt(i) && l.getTermAt(i)[0]=='-')
                tupleName+="n"+l.getTermAt(i).substr(1);
            else
                tupleName+=l.getTermAt(i)+"_";
        }
    }
    for(const aspc::ArithmeticRelation& inequality: inequalities){
        tupleName+=inequality.getLeft().getTerm1();
        if(!inequality.getLeft().isSingleTerm()){
            tupleName+=convertToWordArithmeticOp[inequality.getLeft().getOperation()]+inequality.getLeft().getTerm2();
        }

        tupleName+=convertToWord[inequality.getComparisonType()];
        tupleName+=inequality.getRight().getTerm1();
        if(!inequality.getRight().isSingleTerm()){
            tupleName+=convertToWordArithmeticOp[inequality.getRight().getOperation()]+inequality.getRight().getTerm2();
        }
        tupleName+="_";
    }
}
std::string aspc::Aggregate::getJoinTupleName()const{ 
    return tupleName;
}
void aspc::Aggregate::normalizeArithmeticRelation(const std::unordered_set<std::string> sharedVariables){
    int inequality_index=0;
    std::set<unsigned int> normalized_relation_indices;
    // std::cout<<sharedVariables.size()<<std::endl;
    for(aspc::ArithmeticRelation& r : inequalities){
        if(r.getComparisonType() == aspc::EQ){
            if(r.getLeft().isSingleTerm() && r.getRight().isSingleTerm()){
                if(sharedVariables.count(r.getLeft().getTerm1())>0 && sharedVariables.count(r.getRight().getTerm1())>0)
                    break;
                // Z = Y
                for(aspc::Literal& l : aggregateLiterals){
                    for(int i=0;i<l.getAriety();i++){
                        // l.print();
                        
                        if(l.isVariableTermAt(i) && l.getTermAt(i) == r.getLeft().getTerm1() && sharedVariables.count(r.getLeft().getTerm1())<=0){
                            // std::cout<<"Mapping "<<l.getTermAt(i) << " to "<<r.getRight()<<std::endl;
                            l.setTermAt(i,r.getRight().getTerm1());
                        }else if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0){
                            
                            if(l.isVariableTermAt(i) && l.getTermAt(i) == r.getRight().getTerm1()){
                                // std::cout<<"Maps "<<l.getTermAt(i) << " to "<<r.getLeft()<<std::endl;
                                l.setTermAt(i,r.getLeft().getTerm1());
                            }
                        }
                        
                    }
                }
                for(int i=0;i<aggregateVariables.size();i++){
                    if(aggregateVariables[i] == r.getLeft().getTerm1() && isVariable(r.getRight().getTerm1())){
                        if(sharedVariables.count(aggregateVariables[i])<=0)
                            aggregateVariables[i]=r.getRight().getTerm1();
                    }else if(aggregateVariables[i] == r.getRight().getTerm1() && isVariable(r.getLeft().getTerm1()) && sharedVariables.count(r.getLeft().getTerm1())>0){
                        aggregateVariables[i]=r.getLeft().getTerm1();
                    }
                }
                // X = Y,X in body, Z > X
                for(int i=0;i<inequalities.size();i++){
                    if(i!=inequality_index){
                        int term=0;
                        for(std::string& t : inequalities[i].getLeft().getAllTerms()){
                            if(t == r.getLeft().getTerm1()){

                                if(sharedVariables.count(t)<=0)
                                    inequalities[i].setTermAtExpression(0,term,r.getRight().getTerm1());
                                
                            }else if(t == r.getRight().getTerm1()){ 

                                if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0)
                                    inequalities[i].setTermAtExpression(0,term,r.getLeft().getTerm1());

                            }
                            term++;
                        }
        
                        term=0;
                        for(std::string& t : inequalities[i].getRight().getAllTerms()){
                            if(t == r.getLeft().getTerm1()){
                                if(sharedVariables.count(t)<=0)
                                    inequalities[i].setTermAtExpression(1,term,r.getRight().getTerm1());
                            }else if(t == r.getRight().getTerm1()){ 
                                if(!isVariable(r.getLeft().getTerm1()) || sharedVariables.count(r.getLeft().getTerm1())>0)
                                    inequalities[i].setTermAtExpression(1,term,r.getLeft().getTerm1());
                            }
                            term++;
                        }
                    }
                }
                normalized_inequalities.push_back(aspc::ArithmeticRelation(r));
                normalized_relation_indices.insert(inequality_index);
            }
        }

        inequality_index++;
    }
    unsigned int removed_inequalities=0;
    for(unsigned int index : normalized_relation_indices){
        inequalities.erase(inequalities.begin()+(index-removed_inequalities));
        removed_inequalities++;
    }
    computeJoinTupleName();
}

bool aspc::Aggregate::isBoundedRelation(const std::unordered_set<std::string>& set) const {
    
    return true;
}

bool aspc::Aggregate::isBoundedLiteral(const std::unordered_set<std::string>&) const {
    return false;
}

bool aspc::Aggregate::isBoundedValueAssignment(const std::unordered_set<std::string>& boundVariables) const {

    return false;
}

void aspc::Aggregate::addVariablesToSet(std::unordered_set<std::string>& set) const {

}

bool aspc::Aggregate::isPositiveLiteral() const {
    return false;
}
std::string aspc::Aggregate::getTermAt(unsigned int termIndex)const{
    std::unordered_set<std::string> boundVars;
    int term=0;
    for(const aspc::Literal& l : aggregateLiterals){
        for(int i=0;i<l.getAriety();i++){
            if(l.isVariableTermAt(i))
                boundVars.insert(l.getTermAt(i));
            if(term == termIndex)
                return l.getTermAt(i);
            term++;
        }
    }
    for(const aspc::ArithmeticRelation& inequality : inequalities){
        if(inequality.isBoundedValueAssignment(boundVars)){
            if(term == termIndex)
                return inequality.getAssignedVariable(boundVars);
            boundVars.insert(inequality.getAssignedVariable(boundVars));
            term++;
        }
    }
    return "";
}
std::string aspc::Aggregate::getStringRep()const{
    std::string result;
    for(const std::string& v: aggregateVariables){
        result+=v+",";
    }
    for(const aspc::Literal& l : aggregateLiterals){
        result+=l.getPredicateName()+",";
        for(int i=0;i<l.getAriety();i++){
            result+=l.getTermAt(i)+",";
        }
    }
    for(const aspc::ArithmeticRelation& r : inequalities){
        result+=r.getLeft().getStringRep()+",";
        result+=r.getRight().getStringRep()+",";
    }
    
    return result.substr(0,result.length()-1);
}
std::string aspc::Aggregate::getAggregateFunction()const{
    return aggregateFunction2String[aggregateFunction];
}


bool aspc::Aggregate::isSum()const{
    return aggregateFunction==aspc::SUM;
}



void aspc::Aggregate::print() const {
    
    
    std::cout<<aggregateFunction2String[this->aggregateFunction]<<"{";
    
    unsigned size=this->aggregateVariables.size();
    int j=0;
    for(std::string s:aggregateVariables){
        std::cout<<s;
        if(j<size-1)
            std::cout<<", ";
    }
    std::cout<<" : ";
    size=this->aggregateLiterals.size();

    for(unsigned i=0;i<size;++i){
        
        if(aggregateLiterals[i].isNegated())
        std::cout << "not ";
        std::cout<<aggregateLiterals[i].getPredicateName()<<"(";
        
        std::vector<std::string> terms = aggregateLiterals[i].getAtom().getTerms();
        unsigned num_terms = terms.size();
        
        for(unsigned j=0;j<num_terms;++j){
            std::cout<<terms[j];
            if(j<num_terms-1)
                std::cout<<", ";
        }
        std::cout<<")";
        if(i<size-1)
            std::cout<<", ";
    }

    for(const aspc::ArithmeticRelation& r : inequalities){
        std::cout<<", " << r.getStringRep();
    }
    std::cout<<"}";
    
}
void aspc::Aggregate::getOrderedAggregateBody(std::vector<aspc::Formula*>& orderedBody,std::unordered_set<std::string> boundVars)const{
    std::unordered_set<std::string> boundVariables(boundVars);
    std::unordered_set<unsigned> selectedLiterals;
    std::unordered_set<unsigned> selectedInequalities;
    while(orderedBody.size()<aggregateLiterals.size()+inequalities.size()){
        unsigned selectedIndex=-1;
        bool isBoundFormula=false;
        bool isPositiveLiteralSelected=false;
        bool isBoundedValueAssignmentSelected=false;
        for(unsigned i=0;i<inequalities.size();i++){
            if(selectedInequalities.count(i)==0){
                if(inequalities[i].isBoundedRelation(boundVariables)){
                    selectedIndex=i;
                    isBoundFormula=true;
                    break;
                }else if(inequalities[i].isBoundedValueAssignment(boundVariables)){
                    if(!isBoundedValueAssignmentSelected){
                        selectedIndex=i;
                        isBoundedValueAssignmentSelected=true;
                    }
                }
            }
        }
        if(selectedIndex==-1){
            for(unsigned i=0;i<aggregateLiterals.size();i++){
                if(selectedLiterals.count(i)==0){
                    if(aggregateLiterals[i].isBoundedLiteral(boundVariables)){
                        selectedIndex=i;
                        isBoundFormula=true;
                        break;
                    }if(aggregateLiterals[i].isPositiveLiteral()){
                        if(!isPositiveLiteralSelected){
                            selectedIndex=i;
                            isPositiveLiteralSelected=true;
                        }
                    }
                }
            }
        }else{
            inequalities[selectedIndex].addVariablesToSet(boundVariables);
            selectedInequalities.insert(selectedIndex);
            orderedBody.push_back(new aspc::ArithmeticRelation(inequalities[selectedIndex]));
            continue;
        }
        if(selectedIndex!=-1){
            aggregateLiterals[selectedIndex].addVariablesToSet(boundVariables);
            selectedLiterals.insert(selectedIndex);
            orderedBody.push_back(new aspc::Literal(aggregateLiterals[selectedIndex]));
        }
    }
}
bool aspc::Aggregate::isLiteral() const {
    return false;
}

unsigned aspc::Aggregate::firstOccurrenceOfVariableInLiteral(const std::string &) const {
    return 1;
}

aspc::Aggregate::~Aggregate(){
    
}

SharedVars aspc::Aggregate::getSharedBody(const std::unordered_set<std::string>& bodyVars, const std::vector<aspc::Literal>& bodyLits, const std::vector<aspc::ArithmeticRelation>& bodyIneqs)const {
    std::unordered_set<std::string> sharedTerms;
    SharedVars sharedData;
    for(const aspc::Literal& lit : aggregateLiterals){
        for(unsigned k = 0; k<lit.getAriety(); k++){
            std::string term = lit.getTermAt(k);
            if(lit.isVariableTermAt(k) && bodyVars.count(term)){
                auto it = sharedTerms.emplace(term);
                if(it.second){
                    sharedData.addTerm(term);
                }
            }
        }
    }
    for(const aspc::ArithmeticRelation& ineq : inequalities){
        for(const aspc::ArithmeticExpression& exp : {ineq.getRight(), ineq.getLeft()}){
            for(std::string term : exp.getAllTerms()){
                if(isVariable(term) && bodyVars.count(term)){
                    auto it = sharedTerms.emplace(term);
                    if(it.second){
                        sharedData.addTerm(term);
                    }
                }
            }
        }
    }
    for(const auto& lit : bodyLits){
        sharedData.addLiteral(lit);
    }
    for(const auto& ineq : bodyIneqs){
        sharedData.addInequality(ineq);
    }
    return sharedData;
}

