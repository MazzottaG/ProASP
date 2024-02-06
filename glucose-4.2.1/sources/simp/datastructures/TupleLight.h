/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://w  ww.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
#ifndef TUPLELIGHT_H
#define TUPLELIGHT_H
#include <vector>
#include <string>
#include <cstring>
#include <unordered_set>
#include <unordered_map>
#include <iostream>
#include <climits>
#include <variant>
#include <set>
// #include "AggregateSetCmp.h"
// #include "../utils/ConstantsManager.h"
#include "IndexedSet.h"
#include "../../core/SolverTypes.h"
#include "../../mtl/Vec.h"

enum TruthStatus {
    True = 0, False, Undef, UNKNOWN
};
// class AggregateSetCmp;
class TupleLight {
public:
    static Glucose::vec<Glucose::Lit> EMPTY_REASON_LITS;

    TupleLight() : predicateName(-1),id(0),size_(0),content(NULL),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
    }

    TupleLight(int predicateName, bool negated = false, int waspID = 0) : predicateName(predicateName),id(0),size_(0),content(NULL),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
    }
    TupleLight(int predicateName,std::vector<int> v, bool negated = false, int waspID = 0) : predicateName(predicateName),/*std::vector<int>(v),*/ id(0),size_(v.size()),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
        content = new int[v.size()];
        std::copy(v.begin(), v.end(), content);
    }
    
    TupleLight(const TupleLight& orig) : size_(orig.size()), /*std::vector<int>(orig),*/ predicateName(orig.predicateName), id(orig.id), status(orig.status),collisionsListsSize(0),collisionsLists(nullptr) {
        
        content = new int[orig.size_];
        std::memcpy(content,orig.content,orig.size_*sizeof(int));
        
        // WARNING missing initialization for collisionsList
    }

    virtual ~TupleLight() {
        if(content != NULL){
            delete [] content;
            content = NULL;
        }

        if(collisionsLists != nullptr) {
            delete[] collisionsLists;
            collisionsLists = nullptr;
        }
    }

    TupleLight(const std::initializer_list<int> & l, bool negated = false, int waspID = 0) :
    /*std::vector<int>(l),*/ size_(l.size()), predicateName(-1), id(0),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    TupleLight(const std::initializer_list<int> & l, int predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), id(0),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }
    
    TupleLight(const std::vector<int> & l, int predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), predicateName(predicateName), id(0),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    //WARNING: require l to be created on the fly new int[]{...}
    TupleLight(int* l, int size, int predicateName, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(size), predicateName(predicateName), id(0),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr){
        content = l;
    }
    TupleLight(const std::vector<int> & l, bool negated = false, int waspID = 0) :
    /*vector<int>(l),*/ size_(l.size()), id(0),status(UNKNOWN),collisionsListsSize(0),collisionsLists(nullptr) {
        content = new int[l.size()];
        std::copy(l.begin(), l.end(), content);
    }

    void initCollisionList(unsigned collisionsListCount){
        assert(collisionsLists == nullptr);
        collisionsLists = new std::pair< std::variant< std::vector<int>, IndexedSet >*,unsigned>[collisionsListCount];
        collisionsListsSize = 0; 
    }

    //WARNING use only with bufferedTuple in TupleFactory
    inline void setContent(int* vectorData,int size,const int predName){
        content = vectorData;
        size_=size;
        predicateName=predName;
    }
    //WARNING use only with bufferedTuple in TupleFactory
    inline void clearContent(){
        content = NULL;
    }
    //WARNING use only with bufferedTuple in TupleFactory
    inline int* getContent()const{
        return content ;
    }
    
    int getPredicateName() const {
        return predicateName;
    }
    int size()const {return size_;}
    void setSize(int s){size_=s;}

    int getId() const {
        return id;
    }

    void setId(int id) const {
        this->id = id;
    }
    
    void setCollisionListIndex(std::variant< std::vector<int>, IndexedSet >* collisionList, unsigned index,int internalIndex=-1)const {
        assert(collisionsLists != nullptr);

        if(internalIndex>=0){
            if(collisionsLists[internalIndex].first!=collisionList){
                std::cout<<"Error in swaping position in collision list"<<std::endl;
                exit(180);
            }
            collisionsLists[internalIndex].second=index;
            return;
        }
        // if(collisionsListsSize>=collisionsLists.size()){
        //     collisionsLists.push_back(std::pair<std::variant< std::vector<int>, IndexedSet >*,unsigned>(collisionList,index));
        //     collisionsListsSize++;
        //     return;
        // }
        collisionsLists[collisionsListsSize]=std::make_pair(collisionList,index);
        collisionsListsSize++;
    }

    // void removeFromCollisionsLists(const TupleFactory& factory) const ;
    std::pair<std::variant< std::vector<int>, IndexedSet >*,unsigned>* getCollisionsLists()const{return collisionsLists;}
    int getCollisionsListsSize(){ return collisionsListsSize;}

    void clearCollisionsList(){
        collisionsListsSize=0;
    }
    inline int operator[](const unsigned& i)const{
        return content[i];
    }
    inline int at(const unsigned& i)const{
        return content[i];
    }

    inline int& operator[](const unsigned& i){
        return content[i];
    }
    inline int& at(const unsigned& i){
        return content[i];
    }
    
    bool operator==(const TupleLight& right) const {

        if (predicateName != right.predicateName || size_ != right.size_) {
            return false;
        }
        for (unsigned i = 0; i < size_; i++) {
            if (operator[](i) != right[i]) {
                return false;
            }
        }
        return true;
    }
    unsigned long getBytesCount(){
        // unsigned long totalSize = sizeof(predicateName);
        // totalSize += sizeof(status);
        // totalSize += sizeof(id);
        // totalSize += sizeof(waspID);
        // totalSize += sizeof(size_);
        // totalSize += sizeof(content);
        // for(int i=0;i<size_;i++) totalSize+=sizeof(content[i]);
        // totalSize += sizeof(collisionsListsSize);
        // totalSize += sizeof(collisionsLists);
        // for(const auto& pair : collisionsLists){
        //     totalSize += sizeof(pair.first);
        //     totalSize += sizeof(pair.second);
        // }
        unsigned long totalSize = 4; //sizeof(predicateName);
        totalSize += 4; //sizeof(status);
        totalSize += 4; //sizeof(id);
        totalSize += 4; //sizeof(waspID);
        totalSize += 4; //sizeof(size_);
        totalSize += 8; //sizeof(content);
        for(int i=0;i<size_;i++) totalSize+=4; //sizeof(content[i]);
        totalSize += 4; //sizeof(collisionsListsSize);
        totalSize += 24; //sizeof(collisionsLists);
        // for(const auto& pair : collisionsLists){
        //     totalSize += 8;
        //     totalSize += 4;
        // }
        #ifdef PURE_PROP
        Glucose::vec<Glucose::Lit> reason;
        #endif
        return totalSize;
    }
    TupleLight& operator=(const TupleLight& right) {
        assert(false);
        if (this == &right)
            return *this;
        predicateName = right.predicateName;

        if(collisionsLists != nullptr){
            delete [] collisionsLists;
            collisionsLists = nullptr;
        }
        id = right.id;

        size_=right.size_;
        if(content!=NULL)
            delete [] content;
        content = new int[right.size_];
        memcpy ( content, right.content, size_ );
        return *this;
    }
    std::string toString()const{
        std::string tuple2String="";
        
        // tuple2String+= Executor::predicateIds[predicateName] + "(";
        // for (unsigned i = 0; i < size_; i++) {
        //     if (i > 0) {
        //         tuple2String+= ",";
        //     }
        //     tuple2String+= std::to_string(operator[](i));
        // }
        // tuple2String+= ")";
        return tuple2String;
    }

    void print() const {
        // if(status == False)
        //     std::cout << "not ";
        // std::cout << Executor::predicateIds[predicateName] << "(";
        // for (unsigned i = 0; i < size_; i++) {
        //     if (i > 0) {
        //         std::cout << ",";
        //     }
        //     int term = operator[](i);
        //     if(term>=INT_MAX / 2){
        //         std::cout << ConstantsManager::getInstance().unmapConstant(term); 
        //     }else{
        //         std::cout << term;
        //     }
        // }
        // std::cout << ")" <<std::endl;
    }
    void printAsConstraint() const {
        // std::string sign = status == True ? "not" : "";
        // std::cout << ":-" << sign << " " <<Executor::predicateIds[predicateName]<< "(";
        // for (unsigned i = 0; i < size_; i++) {
        //     if (i > 0) {
        //         std::cout << ",";
        //     }
        //     std::cout << operator[](i);
        // }
        // std::cout << ")." <<std::endl;
    }
    void printAsObject() const {
        // std::string sign = status == True ? "not" : "";
        // std::cout << "TupleLight" << id << "({";
        // for (unsigned i = 0; i < size_; i++) {
        //     if (i > 0) {
        //         std::cout << ",";
        //     }
        //     std::cout << operator[](i);
        // }
        // std::cout << ",&_"<<Executor::predicateIds[predicateName]<<");" <<std::endl;
    }
    bool isInternalLiteral()const{
        // return waspID==0;
        return true;
    }
    int getWaspID()const{
        return id;
    }
    void setWaspID(int waspID){}
    bool isTrue()const{
        return status == True;
    }
    bool isFalse()const{
        return status == False;
    }
    bool isUndef()const{
        return status == Undef;
    }
    TruthStatus getTruthValue()const {return status;}
    std::pair<const TupleLight *, bool>  setStatus(TruthStatus t){
        if(status==t){
            return std::make_pair(this, false);
        }
        status=t;
        // removeFromCollisionsLists(factory);
        return std::make_pair(this, true);
    }
    Glucose::vec<Glucose::Lit>& getReasonLits(){
        #ifndef PURE_PROP
            return TupleLight::EMPTY_REASON_LITS;
        #else
            return reason;
        #endif
    }
    void clearReasonClause(){
        #ifdef PURE_PROP
        this->reason.clear();
        #endif
    }
    void addLiteralToReason(int var, bool negated){
        #ifdef PURE_PROP
        assert(var > 0);
        reason.push(Glucose::mkLit(var,negated));
        #endif 
    }

    const Glucose::vec<Glucose::Lit>& getReason()const{
        #ifndef PURE_PROP
            return TupleLight::EMPTY_REASON_LITS;
        #else
            return reason;
        #endif
    }
    void cleanUpCollisionsList(){
        if(collisionsLists!=nullptr) delete collisionsLists;
        collisionsLists=nullptr;
    }
private:
    int predicateName;
    TruthStatus status;
    mutable int id;

    int* content;
    int size_;
    mutable unsigned collisionsListsSize;
    std::pair< std::variant< std::vector<int>, IndexedSet >*,unsigned>* collisionsLists;

    // mutable std::vector<std::pair< std::variant< std::vector<int>, IndexedSet >*,unsigned>> collisionsLists;
    // mutable std::unordered_map<std::vector<unsigned>*, unsigned> collisionsLists;
    #ifdef PURE_PROP
    Glucose::vec<Glucose::Lit> reason;
    #endif
};

struct TupleLightHash {

    inline std::size_t operator()(const TupleLight & v) const {
        std::size_t seed = 0;
        for (int i=0; i < v.size(); i++) {
            seed ^= v[i] + 0x9e3779b9 + (seed << 6) + (seed >> 2);
        }
        return seed;
    }
};



#endif
