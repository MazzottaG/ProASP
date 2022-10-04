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
#ifndef ASSIGNEDBODY_H
#define	ASSIGNEDBODY_H

#include <unordered_map>
#include <vector>
#include <string>
#include <unordered_set>
#include "../language/Literal.h"
#include "../language/ArithmeticRelation.h"

class AssignedBody {
    private:
        std::vector<std::string> terms;
        std::vector<aspc::Literal> literals;
        std::vector<aspc::ArithmeticRelation> ineqs;
    public:
        AssignedBody(const AssignedBody& p){
            for(std::string t : p.terms)
                this->terms.push_back(t);

            for(aspc::Literal l : p.literals){
                this->literals.push_back(l);
            }
            for(aspc::ArithmeticRelation ineq : p.ineqs){
                this->ineqs.push_back(ineq);
            }
        }
        AssignedBody(){}
        
        void addTerm(std::string t){terms.push_back(t);}
        void addLiteral(aspc::Literal l){literals.push_back(l);}
        void addInequality(aspc::ArithmeticRelation r){ineqs.push_back(r);}
        
        void clearLiterals(){literals.clear();}
        void clearIneqs(){ineqs.clear();}
        void setTerms(std::vector<std::string> terms){this->terms=terms;}

        std::vector<std::string> getTerms()const{return terms;}
        std::vector<aspc::Literal> getLiterals()const{return literals;}
        AssignedBody& operator=(const AssignedBody& p){
            this->terms.clear();
            for(std::string t : p.terms)
                this->terms.push_back(t);

            this->literals.clear();
            for(aspc::Literal l : p.literals){
                this->literals.push_back(l);
            }
            this->ineqs.clear();
            for(aspc::ArithmeticRelation ineq : p.ineqs){
                this->ineqs.push_back(ineq);
            }
            return *this;
        }
        bool operator==(const AssignedBody& b){
            if(literals.size() != b.literals.size())
                return false;
            if(ineqs.size() != b.ineqs.size())
                return false;
            if(terms.size() != b.terms.size())
                return false;

            return strictCheck(b);
            

        }
        bool strictCheck(const AssignedBody& b){
            for(int i=0;i<literals.size();i++){
                if(literals[i]==b.literals[i]){
                }else return false;
            }

            for(int i=0;i<ineqs.size();i++){
                if(ineqs[i]==b.ineqs[i]){
                }else return false;
            }

            for(int i=0; i< terms.size();i++){
                if(terms[i]==b.terms[i]){
                }else return false;
            }

            return true;
        }
        bool relaxedCheck(const AssignedBody& b){
            for(int i=0;i<literals.size();i++){
                bool found=false;
                for(int j=0;j<b.literals.size();j++){
                    if(literals[i]==b.literals[j]){
                        found = true;
                    }
                }
                if(!found) return false;
            }
            for(int i=0;i<b.literals.size();i++){
                bool found=false;
                for(int j=0;j<literals.size();j++){
                    if(b.literals[i]==literals[j]){
                        found = true;
                    }
                }
                if(!found) return false;
            }

            for(int i=0;i<ineqs.size();i++){
                bool found = false;
                for(int j=0;j<b.ineqs.size();j++){
                    if(ineqs[i]==b.ineqs[j]){
                        found = false;
                    }
                }
                if(!found) return false;
            }
            for(int i=0;i<b.ineqs.size();i++){
                bool found = false;
                for(int j=0;j<ineqs.size();j++){
                    if(b.ineqs[i]==ineqs[j]){
                        found = false;
                    }
                }
                if(!found) return false;
            }
            for(int i=0; i< terms.size();i++){
                bool found = false;
                for(int j=0; j< b.terms.size();j++){
                    if(terms[i]==b.terms[j])
                        found=true;
                }
                if(!found) return false;
            }

            for(int i=0; i< b.terms.size();i++){
                bool found = false;
                for(int j=0; j< terms.size();j++){
                    if(b.terms[i]==terms[j])
                        found=true;
                }
                if(!found) return false;
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
            for(const aspc::ArithmeticRelation& l : ineqs){
                l.print();
            }
        }
};
#endif
