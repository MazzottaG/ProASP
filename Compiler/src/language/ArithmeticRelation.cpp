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
 * File:   ArithmeticRelation.cpp
 * Author: bernardo
 * 
 * Created on March 16, 2018, 5:07 PM
 */

#include "ArithmeticRelation.h"
#include "../utils/SharedFunctions.h"
#include "Rule.h"
#include <iostream>
#include <cassert>

using namespace std;

std::map<aspc::ComparisonType, std::string> aspc::ArithmeticRelation::comparisonType2String = {
    {GT, ">"},
    {EQ, "=="},
    {LT, "<"},
    {GTE, ">="},
    {LTE, "<="},
    {NE, "!="}

};

std::map<std::string,aspc::ComparisonType> aspc::ArithmeticRelation::string2ComparisonType = {
    {">",GT},
    {"=",EQ},
    {"<",LT},
    {">=",GTE},
    {"<=",LTE},
    {"!=",NE}
};
aspc::ArithmeticRelation::ArithmeticRelation(const aspc::ArithmeticExpression& left_, const aspc::ArithmeticExpression& right_, aspc::ComparisonType comparisonType_) : left(left_), right(right_), comparisonType(comparisonType_) {
    
}
aspc::ArithmeticRelation::ArithmeticRelation(const aspc::ArithmeticRelation & other): left(other.getLeft()),right(other.getRight()),comparisonType(other.getComparisonType()){

}
bool aspc::ArithmeticRelation::operator==(const aspc::ArithmeticRelation& other)const{
    if(comparisonType!=other.comparisonType)
        return false;
    if(right == other.right && left == other.left)
        return true;
    return false;
    
}

void aspc::ArithmeticRelation::addOccurringVariables(std::unordered_set<std::string>& set) const {
    //assert(isBoundedValueAssignment(set));
    for(std::string v : left.getAllTerms()){
        if(isVariable(v)) set.insert(v);
    }
    for(std::string v : right.getAllTerms()){
        if(isVariable(v)) set.insert(v);
    }

}
void aspc::ArithmeticRelation::addVariablesToSet(std::unordered_set<std::string>& set) const {
    //assert(isBoundedValueAssignment(set));
    if(isBoundedValueAssignment(set)) {
        set.insert(getAssignedVariable(set));
    }

}

bool aspc::ArithmeticRelation::isBoundedRelation(const std::unordered_set<std::string>& set) const {
    for (const std::string & t : left.getAllTerms()) {
        if (isVariable(t) && !set.count(t)) {
            return false;
        }
    }
    for (const std::string & t : right.getAllTerms()) {
        if (isVariable(t) && !set.count(t)) {
            return false;
        }
    }
    return true;
}

bool aspc::ArithmeticRelation::isBoundedLiteral(const std::unordered_set<std::string>&) const {
    return false;
}

bool aspc::ArithmeticRelation::isBoundedValueAssignment(const std::unordered_set<std::string>& boundVariables) const {

    //    if (comparisonType == aspc::EQ && left.isSingleTerm() && isVariable(left.getTerm1()) && !set.count(left.getTerm1())) {
    //        for (const string & t : right.getAllTerms()) {
    //            if (isVariable(t) && !set.count(t)) {
    //                return false;
    //            }
    //        }
    //        return true;
    //    }
    //    return false;
    if (comparisonType != aspc::EQ) {
        return false;
    }
    unsigned unassignedVariables = 0;
    for (const std::string & v : left.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            if(left.isProduct()) return false;
            unassignedVariables++;
        }
    }
    for (const std::string & v : right.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            if(right.isProduct()) return false;
            unassignedVariables++;
        }
    }
    return unassignedVariables == 1;
}

std::string aspc::ArithmeticRelation::getAssignedVariable(const unordered_set<std::string>& boundVariables) const {
    assert(isBoundedValueAssignment(boundVariables));
    for (const std::string & v : left.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            return v;
        }
    }
    for (const std::string & v : right.getAllTerms()) {
        if (!boundVariables.count(v) && isVariable(v)) {
            return v;
        }
    }
    throw std::runtime_error("error in assignment");
    
}


void aspc::ArithmeticRelation::print() const {
    std::cout << left << " " << comparisonType2String[comparisonType] << " " << right;

}

bool aspc::ArithmeticRelation::isPositiveLiteral() const {
    return false;
}

bool aspc::ArithmeticRelation::isLiteral() const {
    return false;
}

unsigned aspc::ArithmeticRelation::firstOccurrenceOfVariableInLiteral(const string &) const {
    return -1;
}

string aspc::ArithmeticRelation::getStringRep() const {
    return left.getStringRep() + " " + comparisonType2String[comparisonType] + " " + right.getStringRep();
}


string invertOperation(char op) {
    switch(op) {
        case '+':
            return "-";
        case '-':
            return "+";
        case '*':
            return "/";
        case '/':
            return "*";
    }
    throw std::runtime_error("unsupported operation "+op);
}

string aspc::ArithmeticRelation::getAssignmentStringRep(const unordered_set<string>& boundVariables) const {
    //    return left.getStringRep() + " = " + right.getStringRep();
    bool containsProduct = false;
    for(auto exp : {left,right}) {
        if(left.isProduct())
            containsProduct=true;
    }
    if(!containsProduct){
        string res = "";
        bool leftContainsUnassigned = true;
        string unassigned;
        for (const string & v : left.getAllTerms()) {
            if (!boundVariables.count(v) && isVariable(v)) {
                res += v;
                unassigned = v;
            }
        }
        for (const string & v : right.getAllTerms()) {
            if (!boundVariables.count(v) && isVariable(v)) {
                res += v;
                unassigned = v;
                leftContainsUnassigned = false;
            }
        }

        res += " = ";



        ArithmeticExpression evalLeft = left;
        ArithmeticExpression evalRight = right;

        if (!leftContainsUnassigned) {
            evalLeft = right;
            evalRight = left;
        }

        //don't use right and left anymore
        if (evalLeft.isSingleTerm()) {
            return evalLeft.getStringRep() + " = " + evalRight.getStringRep();
        }


        if (!evalLeft.isSingleTerm()) {
            if (evalLeft.getOperation() == '+') {
                if (evalLeft.getTerm1() == unassigned) {
                    return res + evalRight.getStringRep() + " - " + evalLeft.getTerm2();
                }
                else {
                    return res + evalRight.getStringRep() + " - " + evalLeft.getTerm1();
                }
            }
            else if (evalLeft.getOperation() == '-') {
                if (evalLeft.getTerm1() == unassigned) {
                    return res + evalRight.getStringRep() + " + " + evalLeft.getTerm2();
                }
                else {
                    return res + " -"+evalRight.getTerm1() + " + " + evalLeft.getTerm1();
                }
                //TODO implement assignment on / and *
            } else {
                throw std::runtime_error("unsupported assignment "+getStringRep());
            }
        }



        throw std::runtime_error("unable to getAssignmentStringRep");
    }else{
        if(!left.isProduct() && right.isProduct()){
            std::string res = "";
            if(left.isSingleTerm()){
                res = left.getTerm1();
            }else{
                std::string left_1 = left.getTerm1();
                std::string left_2 = left.getTerm2();
                bool bound_left_1 = !isVariable(left_1) || boundVariables.count(left_1)==1;
                bool bound_left_2 = !isVariable(left_2) || boundVariables.count(left_2)==1;
                if(!bound_left_1 && !bound_left_2){
                    throw std::runtime_error("unable to getAssignmentStringRep");
                }
                res = !bound_left_1 ? left_1 : left_2; 
            }
            std::string right_1 = right.getTerm1();
            std::string right_2 = right.getTerm2();

            bool bound_right_1 = !isVariable(right_1) || boundVariables.count(right_1)==1;
            bool bound_right_2 = !isVariable(right_2) || boundVariables.count(right_2)==1;

            if(!bound_right_1 || !bound_right_2){
                throw std::runtime_error("unable to getAssignmentStringRep");
            }
            if(left.isSingleTerm()){
                return res + " = " + right_1 + " * " + right_2; 
            }else{
                std::string left_1 = left.getTerm1();
                std::string left_2 = left.getTerm2();
                return res + " = (" + right_1 + " * " + right_2 +") "+ (left.getOperation() == '+' ? "-" : "+") + (left_1 != res ? left_1 : left_2); 

            }
        }else if(!right.isProduct() && left.isProduct()){
            std::string res = "";
            if(right.isSingleTerm()){
                res = right.getTerm1();
            }else{
                std::string right_1 = right.getTerm1();
                std::string right_2 = right.getTerm2();

                bool bound_right_1 = !isVariable(right_1) || boundVariables.count(right_1)==1;
                bool bound_right_2 = !isVariable(right_2) || boundVariables.count(right_2)==1;
                if(!bound_right_1 && !bound_right_2){
                    throw std::runtime_error("unable to getAssignmentStringRep");
                }
                res = !bound_right_1 ? right_1 : right_2; 
            }
            std::string left_1 = left.getTerm1();
            std::string left_2 = left.getTerm2();
            bool bound_left_1 = !isVariable(left_1) || boundVariables.count(left_1)==1;
            bool bound_left_2 = !isVariable(left_2) || boundVariables.count(left_2)==1;

            if(!bound_left_1 || !bound_left_2){
                throw std::runtime_error("unable to getAssignmentStringRep");
            }
            if(right.isSingleTerm()){
                return res + " = " + left_1 + " * " + left_2; 
            }else{
                std::string right_1 = right.getTerm1();
                std::string right_2 = right.getTerm2();
                return res + " = (" + left_1 + " * " + left_2 +") "+ (right.getOperation() == '+' ? "-" : "+") + (right_1 != res ? right_1 : right_2); 
            }
        }
    }
    

}
