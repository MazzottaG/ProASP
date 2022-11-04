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
#ifndef BODYTOAGGREGATE_H
#define BODYTOAGGREGATE_H
#include <vector>
#include <map>
#include <unordered_set>
#include <cmath>
#include "TupleWithoutReasons.h"

class BodyToAggregate {
    
    public:
        void addAggrKeyToBody(const std::vector<int>& k,int id){
            keys[k].insert(id);
        }
        void eraseAggrKeyFromBody(const std::vector<int>& k,int id){
            if(keys.find(k)!=keys.end()){
                keys[k].erase(id);
            }
        }
        bool bodyContainsAggrKey(const std::vector<int>& k,int id){
            if(keys.find(k)==keys.end())
                return false;
            
            return keys[k].find(id) != keys[k].end();   
        }
        
    private:
        std::map<std::vector<int>,std::unordered_set<int>> keys;
};
#endif 

