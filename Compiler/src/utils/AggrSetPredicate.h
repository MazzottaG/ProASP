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
#ifndef AGGRSETPREDICATE_H
#define	AGGRSETPREDICATE_H

#include <unordered_map>
#include <vector>
#include <string>
#include <unordered_set>
#include "../language/Literal.h"
#include "../language/ArithmeticRelation.h"

class AggrSetPredicate {
    private:
        std::vector<std::string> terms;
        std::vector<aspc::Literal> literals;
        std::vector<aspc::ArithmeticRelation> inequalities;
        std::string bodyDomainPredicate;
    public:
        AggrSetPredicate(const AggrSetPredicate& p){
            for(std::string t : p.terms)
                this->terms.push_back(t);

            for(aspc::Literal l : p.literals){
                this->literals.push_back(l);
            }
            for(aspc::ArithmeticRelation ineq : p.inequalities){
                this->inequalities.push_back(ineq);
            }
            this->bodyDomainPredicate=p.bodyDomainPredicate;
        }
        AggrSetPredicate(){bodyDomainPredicate="";}
        void addTerm(std::string t){terms.push_back(t);}
        void addLiteral(aspc::Literal l){literals.push_back(l);}
        void addInequality(aspc::ArithmeticRelation r){inequalities.push_back(r);}
        void setBodyDomain(std::string needDomain){bodyDomainPredicate=needDomain;}

        std::vector<std::string> getTerms()const{return terms;}
        std::string getBodyDomain()const{return bodyDomainPredicate;}
        // AggrSetPredicate(){}
        // AggrSetPredicate(const AggrSetPredicate& other){
        //     for(std::string t : other.terms){
        //         terms.push_back(t);
        //     }
        //     for(aspc::Literal l : other.literals){
        //         literals.push_back(l);
        //     }
        //     for(aspc::ArithmeticRelation r : other.inequalities){
        //         inequalities.push_back(r);
        //     }
        // }
        AggrSetPredicate& operator=(const AggrSetPredicate& p){
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
        bool operator==(const AggrSetPredicate& predicate){
            std::cout<<"operator =="<<std::endl;
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
        void print(){
            std::cout<<"Terms:";
            for(std::string t : terms){
                std::cout<<" "<<t;
            }
            std::cout<<std::endl<<"Literals:"<<std::endl;
            for(const aspc::Literal& l : literals){
                l.print();
            }
            std::cout<<"Inequalities:"<<std::endl;
            for(const aspc::ArithmeticRelation& l : inequalities){
                l.print();
            }
        }
};
#endif
