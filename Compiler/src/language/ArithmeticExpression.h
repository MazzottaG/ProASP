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
 * File:   ArithmeticExpression.h
 * Author: bernardo
 *
 * Created on March 7, 2017, 2:22 PM
 */

#ifndef ARITHMETICEXPRESSION_H
#define ARITHMETICEXPRESSION_H

#include<string>
#include<ostream>
#include<unordered_set>
#include<string>
#include<vector>

namespace aspc {

    class Rule;
    
    class ArithmeticExpression {

        friend std::ostream & operator<<(std::ostream & out, const ArithmeticExpression & e) {
            out << e.term1;
            if (!e.singleTerm) {
                out << e.operation << e.term2;
            }
            return out;
        }
    public:

        ArithmeticExpression();
        ArithmeticExpression(const aspc::ArithmeticExpression& expr);
        ArithmeticExpression(const std::string &, const std::string &, char operation);
        ArithmeticExpression(const std::string &);
        bool operator==(const aspc::ArithmeticExpression& expr)const;
        aspc::ArithmeticExpression& operator=(const aspc::ArithmeticExpression&);
        bool isSingleTerm() const;

        const std::string & getTerm1() const {
            return term1;
        }

        const std::string & getTerm2() const {
            return term2;
        }

        char getOperation() const {
            return operation;
        }
        void setTerm1(std::string term){
            term1=term;
        }
        void setTerm2(std::string term){
            term2=term;
        }
        std::vector<std::string> getAllTerms() const;
        
        std::string getStringRep() const;
        

    private:
        std::string term1;
        std::string term2;
        char operation;
        bool singleTerm;

    };
}

#endif /* ARITHMETICEXPRESSION_H */
