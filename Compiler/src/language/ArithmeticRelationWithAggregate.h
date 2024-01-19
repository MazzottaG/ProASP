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
 * File:   ArithmeticRelationWithAggregate.h
 * Author: BLIND
 *
 * Created on 20 marzo 2020, 9.57
 */

#ifndef ARITHMETICRELATIONWITHAGGREGATE_H
#define ARITHMETICRELATIONWITHAGGREGATE_H

#include "ArithmeticExpression.h"
#include "Aggregate.h"
#include "ArithmeticRelation.h"

namespace aspc {
    class ArithmeticRelationWithAggregate: public Formula{
        
        public:
            
            ArithmeticRelationWithAggregate(bool isLower, const aspc::ArithmeticExpression & expression, const aspc::Aggregate & aggregate, aspc::ComparisonType comparisonType,bool isNegated);
            ArithmeticRelationWithAggregate(const aspc::ArithmeticRelationWithAggregate& );
            virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
            virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
            virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
            virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
            void addPositiveBodyVariablesToSet(std::unordered_set<std::string> &) const;
            bool isSafeAggSet() const;

            bool operator==(const ArithmeticRelationWithAggregate& other){
                if(!(aggregate == other.aggregate)) return false;
                if(!(guard == other.guard)) return false;
                if(!(comparisonType == other.comparisonType)) return false;
                if(!(negated == other.negated)) return false;
                if(!(plusOne == other.plusOne)) return false;
                return true;
            }

            virtual bool isPositiveLiteral() const override;
            virtual void print() const override;
            virtual bool isLiteral() const override;
            virtual bool containsAggregate() const override;
            virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const override;
            virtual ~ArithmeticRelationWithAggregate();
            std::string getStringRep() const;
            bool isLessOrLessEqual() const{ return comparisonType == aspc::LT ||comparisonType == aspc::LTE;}
            void setFormulaIndex(unsigned formulaIndex){this->formulaIndex = formulaIndex;}
            unsigned getFormulaIndex()const{return this->formulaIndex;}
            const aspc::Aggregate & getAggregate() const {return aggregate;}
            aspc::ArithmeticExpression getGuard() const{return guard;}
            std::string getCompareTypeAsString()const{return aspc::ArithmeticRelation::comparisonType2String[comparisonType];}
            std::string getAssignedVariable(std::unordered_set<std::string> & set) const;
            std::string getAssignmentAsString(std::unordered_set<std::string> & set) const;
            bool isNegated()const{return negated;}
            bool isPlusOne() const {return plusOne;}
            void setPlusOne(bool isPlusOne){
                this->plusOne=isPlusOne;
            }
            void setNegated(bool isNegated){
                this->negated=isNegated;
            }
            void setCompareType(aspc::ComparisonType type){
                comparisonType=type;
            }
            void normalizeAggregateRelations(std::unordered_set<std::string> sharedVars){
                aggregate.normalizeArithmeticRelation(sharedVars);
            }
            std::string getJoinTupleName()const{
                return aggregate.getJoinTupleName();
            }
            std::string getAggrLitProj(int litIndex)const {return aggregate.getAggrLitProj(litIndex);}
            std::string getTermAt(unsigned int termIndex)const {return aggregate.getTermAt(termIndex);}
            void setJoinTupleName(std::string joinTupleName){
                aggregate.setJoinTupleName(joinTupleName);
            }
            void computeJoinTupleName(){
                aggregate.computeJoinTupleName();
            }
            aspc::ComparisonType getComparisonType()const{
                return comparisonType;
            }
            std::string getAggrVarAsString()const{return aggregate.aggrVarsToString();}
            void clearAggregateLiterals(){aggregate.clearAggregateLiterals();}
            void addAggregateLiteral(aspc::Literal l) {aggregate.addLiteral(l);}
            void getOrderedAggregateBody(std::vector<aspc::Formula*>& orderedAggrBody,std::unordered_set<std::string> boundVariables)const{aggregate.getOrderedAggregateBody(orderedAggrBody,boundVariables);}
        private:
            unsigned formulaIndex;
            aspc::Aggregate aggregate;
            aspc::ArithmeticExpression guard;
            aspc::ComparisonType comparisonType;
            bool negated;
            bool plusOne;
        };  
};

#endif /* ARITHMETICRELATIONWITHAGGREGATE_H */

