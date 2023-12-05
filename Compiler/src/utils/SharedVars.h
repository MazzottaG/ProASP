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
#ifndef SHAREDVARS_H
#define	SHAREDVARS_H

#include <unordered_map>
#include <vector>
#include <string>
#include <unordered_set>
#include "../language/Literal.h"
#include "../language/ArithmeticRelation.h"

class SharedVars {
    private:
        //projection terms
        std::vector<std::string> terms;

        //body literals
        std::vector<aspc::Literal> literals;
        //body inequalities
        std::vector<aspc::ArithmeticRelation> inequalities;
    public:
        SharedVars(const SharedVars& p){
            for(std::string t : p.terms)
                this->terms.push_back(t);

            for(aspc::Literal l : p.literals){
                this->literals.push_back(l);
            }
            for(aspc::ArithmeticRelation ineq : p.inequalities){
                this->inequalities.push_back(ineq);
            }
        }
        SharedVars(){}

        bool empty()const{
            return terms.empty();
        }

        void addTerm(std::string t){terms.push_back(t);}
        void addLiteral(aspc::Literal l){literals.push_back(l);}
        void addInequality(aspc::ArithmeticRelation r){inequalities.push_back(r);}

        std::vector<std::string> getTerms()const{return terms;}

        SharedVars& operator=(const SharedVars& p){
            this->terms.clear();
            for(std::string t : p.terms)
                this->terms.push_back(t);

            this->literals.clear();
            for(aspc::Literal l : p.literals){
                this->literals.push_back(l);
            }
            this->inequalities.clear();
            for(aspc::ArithmeticRelation ineq : p.inequalities){
                this->inequalities.push_back(ineq);
            }
            return *this;
        }
        bool operator==(const SharedVars& predicate){
            if(this->terms.size() != predicate.terms.size()){
                return false;
            }

            for(unsigned i=0; i<terms.size(); i++){
                if(terms[i]!=predicate.terms[i])
                    return false;
            }

            if(this->literals.size() != predicate.literals.size()){
                return false;
            }
            for(unsigned i=0; i<literals.size(); i++){
                if(literals[i]==predicate.literals[i]){
                }else{
                    return false;
                }
            }

            if(this->inequalities.size() != predicate.inequalities.size()){
                return false;
            }
            for(unsigned i=0; i<inequalities.size(); i++){
                if(inequalities[i]==predicate.inequalities[i]){
                }else{
                    return false;
                }
            }
            return true;

        }
        void print(std::string predicate){
            std::cout << predicate << ": {\n";

            std::cout<<"   Terms:";
            for(std::string t : terms){
                std::cout<<" "<<t;
            }
            std::cout<<std::endl<<"   Literals:";
            for(const aspc::Literal& l : literals){
                std::cout << " ";
                l.print();
            }
            std::cout<<std::endl<<"   Inequalities:";
            for(const aspc::ArithmeticRelation& l : inequalities){
                std::cout << " ";
                l.print();
            }
            std::cout << std::endl << "}\n";
        }
};
#endif
