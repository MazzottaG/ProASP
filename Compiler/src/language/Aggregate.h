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
 * File:   Aggregate.h
 * Author: BLIND
 *
 * Created on 17 marzo 2020, 17.20
 */

#ifndef AGGREGATE_H
#define AGGREGATE_H
#include "Formula.h"
#include "Literal.h"
#include "ArithmeticRelation.h"
#include "../utils/SharedVars.h"
#include <map>
#include <vector>
#include <set>


namespace aspc {
    
    enum AggregateFunction {
        COUNT = 0, SUM, MAX, MIN, UNKNOWN
    };
    
    class Aggregate : public Formula{
    
    public:
        Aggregate();
        Aggregate(const std::vector<aspc::Literal> & literals,const std::vector<aspc::ArithmeticRelation>& inequalities, const std::vector<std::string> & variables, std::string function);
        aspc::Aggregate& operator=(const aspc::Aggregate&);
        bool operator==(const aspc::Aggregate& other){
            if(aggregateLiterals.size() != other.aggregateLiterals.size()) return false;
            for(unsigned i = 0; i < aggregateLiterals.size(); i++) if(!(aggregateLiterals[i] == other.aggregateLiterals[i])) return false;
            if(inequalities.size() != other.inequalities.size()) return false;
            for(unsigned i = 0; i < inequalities.size(); i++) if(!(inequalities[i] == other.inequalities[i])) return false;
            if(aggregateVariables.size() != other.aggregateVariables.size()) return false;
            for(unsigned i = 0; i < aggregateVariables.size(); i++) if(!(aggregateVariables[i] == other.aggregateVariables[i])) return false;
            if(aggregateFunction != other.aggregateFunction) return false;
            return true;
        }
        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
        virtual bool isPositiveLiteral() const override;
        virtual void print() const override;
        virtual bool isLiteral() const override;
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const override;
        const std::vector<aspc::Literal> & getAggregateLiterals()const{return aggregateLiterals;}
        const std::vector<std::string>& getAggregateVariables()const {return aggregateVariables;}
        int containsVar(std::string v)const{
            for(int i=0;i<aggregateVariables.size();i++)
                if(v == aggregateVariables[i])
                    return i;
            return -1;
        }
        const std::vector<aspc::ArithmeticRelation> & getAggregateInequalities()const{return inequalities;}
        const std::vector<aspc::ArithmeticRelation> & getAggregateNormalizedInequalities()const{return normalized_inequalities;}
        void normalizeArithmeticRelation(const std::unordered_set<std::string> sharedVariables);
        std::string getJoinTupleName()const;
        void computeJoinTupleName();
        std::string aggrVarsToString()const;
        void setJoinTupleName(std::string joinTupleName){
            tupleName=joinTupleName;
        }
        bool isSum()const;
        std::string getAggrLitProj(int litIndex)const {return aggregateLiteralsProjection[litIndex];}
        std::string getAggregateFunction()const;
        std::string getTermAt(unsigned int termIndex)const;
        std::string getStringRep()const;
        void clearAggregateLiterals(){aggregateLiterals.clear();}
        void addLiteral(aspc::Literal l){aggregateLiterals.push_back(l);}
        void getOrderedAggregateBody(std::vector<aspc::Formula*>& orderedBody,std::unordered_set<std::string>)const;
        virtual ~Aggregate();
        unsigned getFirstVarIndex()const;
        bool isAggregateBodySafe(std::unordered_set<std::string> boundVars){
            for(const aspc::Literal& l : aggregateLiterals){
            }
        }
        SharedVars getSharedBody(const std::unordered_set<std::string>&, const std::vector<aspc::Literal>&, const std::vector<aspc::ArithmeticRelation>&)const;
    private:
        std::vector<aspc::Literal> aggregateLiterals;
        std::vector<aspc::ArithmeticRelation> inequalities;
        std::vector<aspc::ArithmeticRelation> normalized_inequalities;
        std::vector<std::string> aggregateVariables;
        aspc::AggregateFunction aggregateFunction;
        std::string tupleName;
        std::vector<std::string> aggregateLiteralsProjection;
        
    };
}
#endif /* AGGREGATE_H */

