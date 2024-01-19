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
 * File:   ArithmeticRelation.h
 * Author: bernardo
 *
 * Created on March 16, 2018, 5:07 PM
 */

#ifndef ARITHMETICRELATION_H
#define ARITHMETICRELATION_H
#include "Formula.h"
#include "ArithmeticExpression.h"
#include <string>
#include <map>

namespace aspc {
    

    enum ComparisonType {
        GTE = 0, LTE, GT, LT, NE, EQ, UNASSIGNED
    };

    class ArithmeticRelation : public Formula {
    public:
        static std::map<aspc::ComparisonType, std::string> comparisonType2String;
        static std::map<std::string, aspc::ComparisonType> string2ComparisonType;



    public:
        ArithmeticRelation(const aspc::ArithmeticExpression & left, const aspc::ArithmeticExpression & right, aspc::ComparisonType comparisonType);
        ArithmeticRelation(const aspc::ArithmeticRelation & other);
        bool operator==(const aspc::ArithmeticRelation& other)const;
        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
        void addOccurringVariables(std::unordered_set<std::string> &)const ;
        virtual bool isPositiveLiteral() const override;
        virtual void print() const override;
        virtual bool isLiteral() const override;
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const override;

        virtual ~ArithmeticRelation() {

        }
        
        aspc::ComparisonType getComparisonType() const {
            return comparisonType;
        }

        aspc::ArithmeticExpression getLeft() const {
            return left;
        }
        void setTermAtExpression(int expression, int term_index, std::string new_term){
            if(expression == 0){
                if(term_index == 0){
                    left.setTerm1(new_term);
                }else{
                    left.setTerm2(new_term);
                }
            }else{
                if(term_index == 0){
                    right.setTerm1(new_term);
                }else{
                    right.setTerm2(new_term);
                }
            }
        }
        aspc::ArithmeticExpression getRight() const {
            return right;
        }

        std::string getStringRep() const;
        
        std::string getAssignmentStringRep(const std::unordered_set<std::string>& boundVariables) const;
        
        std::string getAssignedVariable(const std::unordered_set<std::string>& boundVariables) const;



    private:
        aspc::ArithmeticExpression left;
        aspc::ArithmeticExpression right;
        aspc::ComparisonType comparisonType;


    };
}

#endif /* ARITHMETICRELATION_H */

