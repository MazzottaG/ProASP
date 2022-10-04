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
#ifndef TUPLEFACTORY_H
#define TUPLEFACTORY_H
#include <unordered_map>
#include <list>
#include <cassert>
#include "TupleLight.h"
#include "IndexedSet.h"
// #include "AggregateSetCmp.h"
#include <variant>
#include <bitset>
#include <cmath>

const int HALF_INT_MAX = INT_MAX/2; 
struct TuplePointerHash {
    inline std::size_t operator()(const TupleLight* v) const {
        std::size_t seed=0;
        int size =v->size();
        bool even = size%2==1;
        int start= even ? 1 : 0;
        if(even)
            seed ^= v->at(0) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        for (int i=start; i < size-1; i+=2) {
            seed ^= ((std::size_t)v->at(i)) + (((std::size_t)v->at(i+1))<<32) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};

struct TuplePointerEq {
   bool operator()(const TupleLight *val1, const TupleLight* val2) const{
      return *val1 == *val2;
   }
};
class TupleFactory{

    private:
        TupleFactory(/* args */){
            storage.push_back(TupleLight());
            internalIDToTuple.push_back(&storage.back());
            // AggregateSetCmp::factory=this;
            generated=false;
        }
        std::vector<std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>> tupleToInternalVarSets;
        std::vector<TupleLight*> internalIDToTuple;
        std::unordered_map<int,TupleLight*> waspIDToTuple;
        std::list<TupleLight> storage;
        std::unordered_map<int,unsigned> aggregateSetToIndex;
        bool generated;
        TupleFactory(const TupleFactory& t) = delete;
        
    public:
        
        static TupleFactory& getInstance() {
            static TupleFactory instance;
            return instance;
        }
        static TupleLight bufferTuple;
        void setBufferedTupleStorage(int* vectorData,int size,int predName){
            bufferTuple.setContent(vectorData,size,predName);
        }
        void addPredicate(){
            tupleToInternalVarSets.push_back(std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>());
        }
        
        
        ~TupleFactory(){
        }
        void removeFromCollisionsList(int id){
            if(id < internalIDToTuple.size()){
                TupleLight* tupleToRemove = internalIDToTuple[id];
                std::vector<std::pair<std::variant< std::vector<int>, IndexedSet >*,unsigned>>* collisionsLists = &tupleToRemove->getCollisionsLists();
                for (unsigned i=0; i<collisionsLists->size(); i++) {
                    std::variant< std::vector<int>, IndexedSet >* collisionList = collisionsLists->at(i).first;
                    unsigned index = collisionsLists->at(i).second;

                    if(std::holds_alternative<std::vector<int>>(*collisionList)){
                        std::vector<int>& collisionVector = std::get<std::vector<int>>(*collisionList);
                        collisionVector[index] = collisionVector[collisionVector.size() - 1];
                        internalIDToTuple[collisionVector[index]]->setCollisionListIndex(collisionList, index,i);
                        collisionVector.pop_back();
                    }else{
                        IndexedSet& collisionSet = std::get<IndexedSet>(*collisionList);
                        collisionSet.erase(id); 
                    }
                }
                tupleToRemove->clearCollisionsList();
            }
        }
        void setId(TupleLight* t,unsigned id){
            if(t->getId()!=id){ 
                if(id < internalIDToTuple.size()){
                    t->setId(id);
                    internalIDToTuple[id]=t;
                }
            }
        }
        //store new wasp tuple and return a smart reference to it
        TupleLight* addNewTuple(std::vector<int> terms,int predName, unsigned id){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                storage.push_back(bufferTuple);
                TupleLight* reference = &storage.back();
                tupleToInternalVar.insert(reference);
                internalIDToTuple.push_back(reference);
                waspIDToTuple.insert({id,reference});
                reference->setWaspID(id);
                reference->setId(storage.size()-1);
                bufferTuple.clearContent();
                // std::cout<<reference->getWaspID()<<" "<<reference->getId()<<" ";reference->print();std::cout<<" "<<id<<std::endl;
                return &storage.back();
            }
            bufferTuple.clearContent();
            // std::cout<<"Already added"<<std::endl;
            // assert(it->getWaspID() == id);
            return *it;
        }
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,int predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                
                storage.push_back(bufferTuple);
                TupleLight* trueReference = &storage.back();
                tupleToInternalVar.insert(trueReference);
                internalIDToTuple.push_back(trueReference);
                trueReference->setId(storage.size()-1);
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();

            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(std::vector<int> terms,int predName){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                bufferTuple.clearContent();
                return NULL;
            }
            bufferTuple.clearContent();
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* find(const TupleLight& t){
            TupleLight* tuple = const_cast<TupleLight *>(&t);
            auto& tupleToInternalVar=tupleToInternalVarSets[tuple->getPredicateName()];
            auto it = tupleToInternalVar.find(tuple);
            if(it==tupleToInternalVar.end()){
                // std::cout<<"Not found"<<std::endl;
                return NULL;
            }
            // assert(it->second == -1);
            return *it;
        }
        TupleLight* getTupleFromWASPID(int id){
            if(waspIDToTuple.count(id)!=0)
                return waspIDToTuple[id];
            return NULL;

        }

        TupleLight* getTupleFromInternalID(int id)const{
            if(id<internalIDToTuple.size())
                return internalIDToTuple[id];
            return NULL;
        }

        void printModelAsConstraint()const {
            std::cout<<"Tuple factory"<<std::endl;
            for(auto tuple : storage){
                if(tuple.getWaspID()!=0){
                    tuple.printAsConstraint();
                }
                
            }
        }
        void print()const {
            std::cout<<"Tuple factory"<<std::endl;
            bool first=true;
            for(auto tuple : storage){
                if(!first)
                    tuple.print();
                else
                    first=false;
            }
        }
        unsigned size(){
            return storage.size();
        }
        void printSize(){
            std::cout<<storage.size()<<std::endl;
        }
        unsigned getIndexForAggrSet(int pred)const{
            auto it = aggregateSetToIndex.find(pred);
            if(it != aggregateSetToIndex.end()){
                return it->second;
            }
            return 0;
        }
        void setIndexForAggregateSet(unsigned index,int pred){
            aggregateSetToIndex.emplace(pred,index);
        }
        const std::vector<TupleLight*>& getTuples()const {return internalIDToTuple;}
        float loadFactor()const{
            // std::cout << "STATS FACTORY Bucket count: "<<tupleToInternalVar.bucket_count() << std::endl;
            // std::cout << "STATS FACTORY Total Tuple Count: "<<tupleToInternalVar.size() << std::endl;
            // std::vector<int> buckets;
            // buckets.resize(tupleToInternalVar.bucket_count());
            // for(TupleLight* t : tupleToInternalVar){
            //     t->printAsObject();
            //     buckets[tupleToInternalVar.bucket(t)]++;
            // }
            // int sum=0;
            // int count=0;
            // int min=0;
            // int min_bucket=0;
            // int max=0;
            // int max_bucket=0;
            // for(int i=0; i<tupleToInternalVar.bucket_count(); i++){
            //     if(buckets[i] > 0){
            //         sum+=buckets[i];
            //         count++;
            //         if(buckets[i]<min || min==0){
            //             min=buckets[i];
            //             min_bucket=i;
            //         }
            //         if(buckets[i]>max){
            //             max=buckets[i];
            //             max_bucket=i;
            //         }
            //     }
            // }
            // int avg=sum/count;
            // int avg_bucket=0;
            // for(int i=0; i<tupleToInternalVar.bucket_count(); i++){
            //     if(buckets[i] > avg - 5 && buckets[i] < avg + 5){
            //         avg_bucket=i;
            //         break;
            //     }
            // }
            // std::cout << "Avg Bucket: "<<avg_bucket<<" "<<buckets[avg_bucket]<<std::endl;
            // for(TupleLight* t : tupleToInternalVar){
            //     if(tupleToInternalVar.bucket(t) == avg_bucket)
            //         t->print();
            // }
            // std::cout << "STATS FACTORY Not Empty buckets count: "<< count <<std::endl;
            // std::cout << "STATS FACTORY Empty buckets percentage: "<<100-(100*count/tupleToInternalVar.bucket_count())<<std::endl;
            // std::cout << "STATS FACTORY Min load for non empty buckets: "<<min<<std::endl;
            // std::cout << "STATS FACTORY Average load for non empty buckets: "<<avg<<std::endl;
            // std::cout << "STATS FACTORY Max load for non empty buckets: "<<max<<std::endl;
            
            return 0;
        }
        void rehash(){
            for(int i=0;i<tupleToInternalVarSets.size();i++){
                auto& set = tupleToInternalVarSets[i];
                set.rehash(set.bucket_count()*2);
            }
        }
            
        void printStats(){
            std::cout << "FACTORY::TupleCount "<<storage.size()<<std::endl;
            for(int i=0; i<1;i++){
                std::cout << "FACTORY::Predicate    "<<i<<std::endl;
            
                auto& tupleToInternalVar = tupleToInternalVarSets[i];
                
                std::cout << "   FACTORY::BucketCount             "<<tupleToInternalVar.bucket_count()<<std::endl;
                std::vector<int> bucketsLoad(tupleToInternalVar.bucket_count(),0);
                for(TupleLight* t : tupleToInternalVar){
                    bucketsLoad[tupleToInternalVar.bucket(t)]++;
                }
                float countNotEmptyBucket=0;
                float avgLoadForNotEmptyBucket=0;
                int mostLoadedBucket=0;
                int maxLoad=0;
                int minLoadedBucket=0;
                int minLoad=0;
                for(int i=0; i<tupleToInternalVar.bucket_count();i++){
                    if(bucketsLoad[i]>0){
                        countNotEmptyBucket+=1;
                        avgLoadForNotEmptyBucket+=bucketsLoad[i];
                        if(bucketsLoad[i]>maxLoad){
                            maxLoad=bucketsLoad[i];
                            mostLoadedBucket=i;
                        }
                        if(bucketsLoad[i]<minLoad || minLoad ==0){
                            minLoad=bucketsLoad[i];
                            minLoadedBucket=i;
                        }
                    }

                }
                std::vector<int> bucketCountForLoading(maxLoad+1);
                for(int i=0; i<tupleToInternalVar.bucket_count();i++){
                    if(bucketsLoad[i]>0){
                        bucketCountForLoading[bucketsLoad[i]]++;
                    }
                }
                for(int i=1;i<bucketCountForLoading.size();i++){
                    std::cout << "   FACTORY::BucketCountOfLength"<<i<<"         "<<bucketCountForLoading[i]<<std::endl;
                }
                avgLoadForNotEmptyBucket/=countNotEmptyBucket;

                std::cout << "   FACTORY::NonEmptyBucket%         "<<(countNotEmptyBucket/(float)bucketsLoad.size())*100<<std::endl;
                std::cout << "   FACTORY::AvgLoadNonEmptyBucket   "<<avgLoadForNotEmptyBucket<<std::endl;
                
                std::cout << "   FACTORY::MinLoadedBucketSize     "<<minLoad<<std::endl;
                std::cout << "   FACTORY::MaxLoadedBucketSize     "<<maxLoad<<std::endl;
            }
        }
        bool isGenerated()const {return generated;}
        void setGenerated(bool gen){this->generated=gen;}
};

#endif