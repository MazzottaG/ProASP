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
 * File:   Formula.h
 * Author: bernardo
 *
 * Created on March 16, 2018, 3:20 PM
 */

#ifndef FORMULA_H
#define FORMULA_H
#include <unordered_set>
#include <string>
#include <cassert>

namespace aspc {

    class Formula {
    public:
        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const = 0;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const = 0;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const = 0;
        virtual bool isPositiveLiteral() const = 0;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const = 0;
        virtual void print() const = 0;
        virtual bool isLiteral() const = 0;
        virtual bool containsAggregate() const{
            return false;
        }
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string &) const = 0;
        virtual ~Formula(){};


    };
}

#endif /* FORMULA_H */

