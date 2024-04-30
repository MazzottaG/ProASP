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
#include <algorithm>

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
namespace Glucose{
    class Solver;
    class Lit;
}
class AbstractPropagator;
class TupleFactory{

    private:
        TupleFactory(/* args */):generatorClauseSet(NULL),clauseIDToTuple(NULL),clauseIDToLength(NULL){
            //storage.push_back(TupleLight());
            addExtraSymbol();
            generated=false;
        }
        std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>* generatorClauseSet;
        std::vector<TupleLight*>* clauseIDToTuple;
        std::vector<unsigned>* clauseIDToLength;

        std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>* generatorConstraint;
        std::vector<TupleLight*>* constraintIDToTuple;
        std::vector<unsigned>* constraintIDToLength;

        std::vector<std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>> tupleToInternalVarSets;
        std::vector<TupleLight*> internalIDToTuple;

        std::unordered_map<int,std::set<int>> auxAtomsForLiteral;
        std::unordered_map<int,std::set<int>> atomsForLiteral;
        std::unordered_set<int> trackedForSupport;

        // std::vector<std::vector<AbstractPropagator*>> negativeWatcher;
        // std::vector<std::vector<AbstractPropagator*>> positiveWatcher;
        // static std::vector<AbstractPropagator*> EMPTY_WATCHER;

        std::vector<std::vector<unsigned>> negativeWatcher;
        std::vector<std::vector<unsigned>> positiveWatcher;
        static std::vector<unsigned> EMPTY_WATCHER;

        std::vector<unsigned> visibleTuple;
        std::unordered_map<int,int> actualSum;
        std::unordered_map<int,int> possibleSum;

        //TODO Remove
        std::unordered_map<int,TupleLight*> waspIDToTuple;
        //-----------
        
        // std::list<TupleLight> storage;
        
        std::unordered_map<int,unsigned> aggregateSetToIndex;
        bool generated;
        TupleFactory(const TupleFactory& t) = delete;
        unsigned factSize;
        
    public:
        int getLastId() const{
            return internalIDToTuple.size()-1;
        }
        std::unordered_map<int,std::set<int>>& getAuxsForLiteral(){
            return auxAtomsForLiteral;
        }
        void addAuxForLiteral(int var,int auxVar){
            auxAtomsForLiteral[var].insert(auxVar);
        }
        std::unordered_map<int,std::set<int>>& getAtomsForLiteral(){
            return atomsForLiteral;
        }
        void addAtomForLiteral(int var,int atom){
            atomsForLiteral[var].insert(atom);
        }
        int addExtraSymbol(){
            internalIDToTuple.push_back(new TupleLight());
            internalIDToTuple.back()->setId(internalIDToTuple.size()-1);
            return internalIDToTuple.size()-1;
        }
        void trackLiteral(int lit){
            trackedForSupport.insert(lit);
        }
        void untrackLiteral(int lit){
            trackedForSupport.erase(lit);
        }
        bool isTracked(int lit){
            return trackedForSupport.count(lit) > 0;
        }
        void destroyPredicate(int pred_id){

        }
        void cleanupPredicate(int pred){
            assert(tupleToInternalVarSets.size()>pred);
            std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq> empty;
            for(TupleLight* t : tupleToInternalVarSets[pred])
                t->cleanUpCollisionsList();
            empty.swap(tupleToInternalVarSets[pred]);
        }
        void printUsedMemory(){
            unsigned total = 0;
            unsigned totalBytes = 0;
            for(unsigned i=0;i<tupleToInternalVarSets.size(); i++){
                std::cout << "Predicate "<<i<<std::endl;
                std::cout << "   Number of tuple: "<<tupleToInternalVarSets[i].size()<<std::endl;
                total += tupleToInternalVarSets[i].size();
                unsigned long usedBytes = 0;
                for(const auto& tuple : tupleToInternalVarSets[i]){
                    usedBytes+=tuple->getBytesCount();
                }
                totalBytes+=usedBytes;
                std::cout << "   Used Bytes: "<<usedBytes<<std::endl;
            }
            std::cout << "Total number: "<<total<<std::endl;
            std::cout << " Total bytes: "<<totalBytes<<std::endl;

            std::cout << "auxAtomsForLiteral size: "<<auxAtomsForLiteral.size()<<std::endl;
            std::cout << "   atomsForLiteral size: "<<atomsForLiteral.size()<<std::endl;
            std::cout << " trackedForSupport size: "<<trackedForSupport.size()<<std::endl;
            std::cout << "   negativeWatcher size: "<<negativeWatcher.size()<<std::endl;
            std::cout << "   positiveWatcher size: "<<positiveWatcher.size()<<std::endl;

            total = 0;
            for(auto pair : auxAtomsForLiteral) total+=pair.second.size();
            std::cout << "auxAtomsForLiteral sets size: "<<total<<std::endl;

            total = 0;
            for(auto pair : atomsForLiteral) total+=pair.second.size();
            std::cout << "   atomsForLiteral sets size: "<<total<<std::endl;

            total = 0;
            for(auto elem : negativeWatcher) total+=elem.size();
            std::cout << "   negativeWatcher vec size: "<<total<<std::endl;
            total = 0;
            for(auto elem : positiveWatcher) total+=elem.size();
            std::cout << "   positiveWatcher vec size: "<<total<<std::endl;

        }
        std::pair<bool,int> popTracked(){
            bool empty = trackedForSupport.empty();
            int elem = empty ? 0 : *trackedForSupport.begin();
            if(!empty) trackedForSupport.erase(elem);
            return std::make_pair(!empty, elem);
        }
        bool hasName(int id)const{
            return internalIDToTuple[id]->getPredicateName() != -1;
        }
        int& getActualSumForLit(int lit){
            return actualSum[lit];
        }

        int& getPossibleSumForLit(int lit){
            return possibleSum[lit];
        }

        void incrementActualSumForLit(int lit,int val){
            if(actualSum.count(lit)) actualSum[lit]+=val;
        }

        void incrementPossibleSumForLit(int lit,int val){
            if(possibleSum.count(lit)) possibleSum[lit]+=val;
        }
        
        void decrementActualSumForLit(int lit,int val){
            if(actualSum.count(lit)) actualSum[lit]-=val;
        }

        void decrementPossibleSumForLit(int lit,int val){
            if(possibleSum.count(lit)) possibleSum[lit]-=val;
        }
        std::unordered_map<int,int>& possibleSums(){
            return possibleSum;
        }
        Glucose::vec<Glucose::Lit>& explain(unsigned var){
            assert(var<internalIDToTuple.size());
            return internalIDToTuple[var]->getReasonLits();
        }

        static TupleFactory& getInstance() {
            static TupleFactory instance;
            return instance;
        }
        static TupleLight bufferTuple;
        static bool usedFindNoSet;
        void setBufferedTupleStorage(int* vectorData,int size,int predName){
            bufferTuple.setContent(vectorData,size,predName);
        }
        
        void addPredicate(){
            tupleToInternalVarSets.push_back(std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>());
        }
        std::vector<unsigned>& getVisibleAtoms(){return visibleTuple;}
        
        ~TupleFactory(){
            for(TupleLight* tuple : internalIDToTuple) delete tuple;
            bufferTuple.clearContent();
        }
        
        void destroyTuples(){
            for(TupleLight* tuple : internalIDToTuple) delete tuple;
        }
        void printAvgWatcherSize(int term){
            // TupleLight* t = find({1,term},4);
            // int id = t->getId();
            // std::cout << (id >= positiveWatcher.size() ? "No watchers for sup_1(1,g)" : "Watcher count for sup_1(1,g): "+std::to_string(positiveWatcher[id].size()))<<std::endl;
            // std::cout << (id >= negativeWatcher.size() ? "No watchers for not sup_1(1,g)" : "Watcher count for not sup_1(1,g): "+std::to_string(negativeWatcher[id].size()))<<std::endl;
        }
        // void addWatcher(AbstractPropagator* prop,int id,bool negated){
        void addWatcher(unsigned prop,int id,bool negated){
            if(negated){
                if(id >= negativeWatcher.size())
                    negativeWatcher.resize(id+1,std::vector<unsigned>());
                    // negativeWatcher.resize(id+1,std::vector<AbstractPropagator*>());
                negativeWatcher[id].push_back(prop);
            }
            else{
                if(id >= positiveWatcher.size())
                    positiveWatcher.resize(id+1,std::vector<unsigned>());
                    // positiveWatcher.resize(id+1,std::vector<AbstractPropagator*>());
                positiveWatcher[id].push_back(prop);
            }
        }
        // std::vector<AbstractPropagator*>& getWatcher(unsigned var,bool negated){
        std::vector<unsigned>& getWatcher(unsigned var,bool negated){
            if(negated)
                return var < negativeWatcher.size() ? negativeWatcher[var] : EMPTY_WATCHER;
            else
                return var < positiveWatcher.size() ? positiveWatcher[var] : EMPTY_WATCHER;
        }

        bool isFact(unsigned id){return id < factSize;}
        void storeFactSize(){factSize = internalIDToTuple.size();}
        void removeFromCollisionsList(int id){
            if(id < internalIDToTuple.size()){
                TupleLight* tupleToRemove = internalIDToTuple[id];
                std::pair<std::variant< std::vector<int>, IndexedSet >*,unsigned>* collisionsLists = tupleToRemove->getCollisionsLists();
                if(collisionsLists != nullptr){
                    int collisionsListSize = tupleToRemove->getCollisionsListsSize();
                    for (unsigned i=0; i<collisionsListSize; i++) {
                        std::variant< std::vector<int>, IndexedSet >* collisionList = collisionsLists[i].first;
                        unsigned index = collisionsLists[i].second;

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
                // storage.push_back(bufferTuple);
                // TupleLight* reference = &storage.back();
                TupleLight* reference = new TupleLight(bufferTuple);
                tupleToInternalVar.insert(reference);
                internalIDToTuple.push_back(reference);
                waspIDToTuple.insert({id,reference});
                reference->setWaspID(id);
                // reference->setId(storage.size()-1);
                reference->setId(internalIDToTuple.size()-1);
                bufferTuple.clearContent();

                // std::cout<<reference->getWaspID()<<" "<<reference->getId()<<" ";reference->print();std::cout<<" "<<id<<std::endl;
                // return &storage.back();
                return reference;
            }
            bufferTuple.clearContent();
            // std::cout<<"Already added"<<std::endl;
            // assert(it->getWaspID() == id);
            return *it;
        }
        void cleanupCompletionStruct(){
            cleanupConstraints();
            cleanupClauses();
        }
        // %%%%%%%%%%%%%%%%%%%%%%%%% Constraint Grounding Methods %%%%%%%%%%%%%%%%%%%%%%%%%
        void initConstraintGen(){
            if(generatorConstraint == NULL)
                generatorConstraint = new std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>();
            if(constraintIDToTuple == NULL)
                constraintIDToTuple = new std::vector<TupleLight*>();
            if(constraintIDToLength == NULL)
                constraintIDToLength = new std::vector<unsigned>();
        }
        void addNewInternalConstraint(std::vector<int> terms){
            std::sort(terms.begin(),terms.end());
            bufferTuple.setContent(terms.data(),terms.size(),-1);
            auto it = generatorConstraint->find(&bufferTuple);
            if(it==generatorConstraint->end()){
                TupleLight* trueReference = new TupleLight(bufferTuple);
                generatorConstraint->insert(trueReference);
                constraintIDToTuple->push_back(trueReference);
                constraintIDToLength->push_back(terms.size());
                trueReference->setId(constraintIDToTuple->size()-1);
                bufferTuple.clearContent();
                return;
            }
            bufferTuple.clearContent();
            // assert(it->second == -1);
            return ;
        }

        //WARNING Returned tuple should be destroyed by the method caller
        std::pair<TupleLight*,unsigned> popConstraint()const{
            TupleLight * res = constraintIDToTuple==NULL || constraintIDToTuple->size() == 0 ? NULL : constraintIDToTuple->back();
            unsigned res_len = constraintIDToLength==NULL || constraintIDToLength->size() == 0 ? 0 : constraintIDToLength->back();
            if(res != NULL) {
                constraintIDToTuple->pop_back();
                constraintIDToLength->pop_back();
            }
            return std::make_pair(res,res_len);
        }
        void cleanupConstraints(){
            if(constraintIDToTuple!=NULL){
                std::pair<TupleLight*,unsigned> pair = popConstraint();
                while(pair.first != NULL){
                    delete pair.first;
                    pair = popConstraint();
                }
            }
        }
        void destroyConstraints(){
            //std::cout << "Destroying"<<std::endl;
            assert(constraintIDToTuple!=NULL && constraintIDToTuple->size() == 0);
            delete constraintIDToTuple;
            delete constraintIDToLength;
            delete generatorConstraint;
            constraintIDToTuple=NULL;
            constraintIDToLength=NULL;
            generatorConstraint=NULL;
        }
        // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


        // %%%%%%%%%%%%%%%%%%%%%%%%% Rule Grounding Methods %%%%%%%%%%%%%%%%%%%%%%%%%
        void initClauseGen(){
            if(generatorClauseSet == NULL)
                generatorClauseSet = new std::unordered_set<TupleLight*,TuplePointerHash,TuplePointerEq>();
            if(clauseIDToTuple == NULL)
                clauseIDToTuple = new std::vector<TupleLight*>();
            if(clauseIDToLength == NULL)
                clauseIDToLength = new std::vector<unsigned>();
        }
        
        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalClause(std::vector<int> terms){
            std::sort(terms.begin(),terms.end());
            bufferTuple.setContent(terms.data(),terms.size(),-1);
            auto it = generatorClauseSet->find(&bufferTuple);
            if(it==generatorClauseSet->end()){
                TupleLight* trueReference = new TupleLight(bufferTuple);
                generatorClauseSet->insert(trueReference);
                clauseIDToTuple->push_back(trueReference);
                clauseIDToLength->push_back(terms.size());
                trueReference->setId(clauseIDToTuple->size()-1);
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();
            return *it;
        }
        //WARNING Returned tuple should be destroyed by the method caller
        std::pair<TupleLight*,unsigned> popClause()const{
            TupleLight * res = clauseIDToTuple==NULL || clauseIDToTuple->size() == 0 ? NULL : clauseIDToTuple->back();
            unsigned res_len = clauseIDToLength==NULL || clauseIDToLength->size() == 0 ? 0 : clauseIDToLength->back();
            if(res != NULL) {
                clauseIDToTuple->pop_back();
                clauseIDToLength->pop_back();
            }
            return std::make_pair(res,res_len);
        }
        void cleanupClauses(){
            if(clauseIDToTuple!=NULL){
                std::pair<TupleLight*,unsigned> pair = popClause();
                while(pair.first != NULL){
                    delete pair.first;
                    pair = popClause();
                }
            }
        }
        void destroyClauses(){
            //std::cout << "Destroying Clauses"<<std::endl;
            assert(clauseIDToTuple!=NULL && clauseIDToTuple->size() == 0);
            delete clauseIDToTuple;
            delete clauseIDToLength;
            delete generatorClauseSet;
            clauseIDToTuple=NULL;
            clauseIDToLength=NULL;
            generatorClauseSet=NULL;
        }
        // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


        //store new internal tuple and return smart reference to it
        TupleLight* addNewInternalTuple(std::vector<int> terms,int predName,bool hidden=false){
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            auto& tupleToInternalVar=tupleToInternalVarSets[predName];
            auto it = tupleToInternalVar.find(&bufferTuple);
            if(it==tupleToInternalVar.end()){
                
                // storage.push_back(bufferTuple);
                // TupleLight* trueReference = &storage.back();
                TupleLight* trueReference = new TupleLight(bufferTuple);
                tupleToInternalVar.insert(trueReference);
                internalIDToTuple.push_back(trueReference);
                // trueReference->setId(storage.size()-1);
                trueReference->setId(internalIDToTuple.size()-1);
                if(!hidden) visibleTuple.push_back(trueReference->getId());
                bufferTuple.clearContent();
                return trueReference;
            }
            bufferTuple.clearContent();

            // assert(it->second == -1);
            return *it;
        }
        TupleLight* findNoSet(std::vector<int> terms,int predName){
            if(!TupleFactory::usedFindNoSet) std::cout << "WARNING: FindNoSet should be used only for debug"<<std::endl;
            TupleFactory::usedFindNoSet=true;
            bufferTuple.setContent(terms.data(),terms.size(),predName);
            for(TupleLight* tuple : internalIDToTuple){
                if(*tuple == bufferTuple)
                    return tuple;
            }
            return NULL;
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
            // std::cout<<"Tuple factory"<<std::endl;
            // for(auto tuple : storage){
            //     if(tuple.getWaspID()!=0){
            //         tuple.printAsConstraint();
            //     }
                
            // }
        }
        std::vector<TupleLight*>* getAtoms() {
            return &internalIDToTuple;
        }
        void print()const {
            // std::cout<<"Tuple factory"<<std::endl;
            // bool first=true;
            // for(auto tuple : storage){
            //     if(!first)
            //         tuple.print();
            //     else
            //         first=false;
            // }
        }
        unsigned size(){
            // return storage.size();
            return internalIDToTuple.size();
        }
        void printSize(){
            // std::cout<<storage.size()<<std::endl;
            std::cout<<internalIDToTuple.size()<<std::endl;

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

        int predicateSize(int pred){
            if(pred >= tupleToInternalVarSets.size())
                return 0;
            return tupleToInternalVarSets[pred].size();
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
            // std::cout << "FACTORY::TupleCount "<<storage.size()<<std::endl;
            std::cout << "FACTORY::TupleCount "<<internalIDToTuple.size()<<std::endl;
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