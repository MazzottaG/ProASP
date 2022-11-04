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
#ifndef SMARTTUPLE_H
#define SMARTTUPLE_H
#include <vector>
#include <string>
#include <unordered_set>
#include "TupleLight.h"
#include <iostream>

using namespace std;
class SmartTuple {
    public:
        SmartTuple(const SmartTuple& t):realTuple(t.realTuple){

        }
        SmartTuple(TupleLight* t):realTuple(t){

        }
        SmartTuple(){
            realTuple=NULL;
        }
        bool isNull(){
            return realTuple==NULL;
        }

        bool operator==(const TupleLight& right) const {
            return realTuple->operator==(right);
        }
        bool operator==(const SmartTuple& right) const {
            return realTuple->operator==(*right.realTuple);
        }
        
        TupleLight& operator=(const TupleLight& right){
            return realTuple->operator=(right);
        }
        SmartTuple& operator=(const SmartTuple& right){
            *realTuple=*right.realTuple;
            return *this;
        }
        int& operator[](unsigned i)const{
            return realTuple->operator[](i);
        }
        int& at(unsigned i)const{
            return realTuple->operator[](i);
        }
        int getPredicateName() const {
            return realTuple->getPredicateName();
        }

        unsigned getId() const {
            return realTuple->getId();
        }

        void setId(unsigned id) const {
            realTuple->setId(id);
        }
        
        void print() const {
            realTuple->print();
        }
        
        unsigned size()const{
            return realTuple->size();
        }

        TupleLight* getReal()const {return realTuple;}

    private:
        TupleLight* realTuple;

};

struct SmartTuplesHash {

    inline std::size_t operator()(const SmartTuple & v) const {
        std::size_t seed = 0;
        for (int i=0; i<v.size(); i++) {
            seed ^= v[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

#endif /* TUPLE_H */

