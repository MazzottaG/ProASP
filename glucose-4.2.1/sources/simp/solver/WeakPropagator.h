//
// Created by giuseppe mazzotta on 27/08/24.
//

#ifndef WEAKPROPAGATOR_H
#define WEAKPROPAGATOR_H
#include "AbstractPropagator.h"
#include "AuxMapHandler.h"
#include <unordered_map>


class WeakPropagator: public AbstractPropagator {
    public:
        ~WeakPropagator(){}
        WeakPropagator():actualSum(0),undefSum(0),upperBound(-1){}
        void printName()const {std::cout << "Weak Propagator"<<std::endl;}
        void propagateLevelZero(Glucose::Solver*,Glucose::vec<Glucose::Lit>&);
        Glucose::CRef propagate(Glucose::Solver*,Glucose::vec<Glucose::Lit>&,int) ;
        void attachWatched();
        void init()const{}
        void notifyTrue(int lit){
            int var = lit >= 0 ? lit : -lit;
            int internalId = tupleMapping[var];
            int weight = weightForLiteral[internalId];
            if(lit >=0 ) actualSum+=weight;
            undefSum-=weight;
        }
        void notifyUndef(int lit){
            int var = lit >= 0 ? lit : -lit;
            int internalId = tupleMapping[var];
            int weight = weightForLiteral[internalId];
            if(lit >=0 ) actualSum-=weight;
            undefSum+=weight;
        }
        void setUpperBound(int bound){this->upperBound=bound;}
        int getUpperBound()const{return upperBound;}

        Glucose::CRef propagateTuple(Glucose::Solver*,Glucose::vec<Glucose::Lit>&,std::vector<bool>&,TupleLight*);
        void printStoredLiterals(){}
        void remapStoredLiteral(){
            tupleMapping.clear();
            for(unsigned litId = 0; litId < literals.size(); litId++){
                tupleMapping[literals[litId]->getId()]=litId;
            }
        }
        void printStats(){}
        void printCurrentStatus(){
            std::cout << "Actual sum: " << actualSum<<std::endl;
            std::cout << "Undef sum: " << undefSum<<std::endl;
            std::cout << "WatchedLiterals {"<<std::endl;
            for(auto pair : tupleMapping){
                std::cout << "   Lit "<<pair.second<< " {"<<std::endl;
                TupleLight* tuple = literals[pair.second];
                int weight = weightForLiteral[pair.second];
                std::cout << "          Id "<< pair.first<<std::endl;
                std::cout << "      Weight "<< weight<<std::endl;
                std::cout << "       Truth "<< (tuple->isTrue() ? "True" : (tuple->isFalse() ? "False" : "Undef"))<<std::endl;
                std::cout << "        Atom "; AuxMapHandler::getInstance().printTuple(tuple);
                std::cout << "   }"<<std::endl;
            }
            std::cout << "}"<<std::endl;
        }
        void addWeightedLiteral(TupleLight* tuple,int weight){
            assert(tuple!=NULL);
            int id = tuple->getId();
            if(tupleMapping.emplace(id,literals.size()).second){
                if(tuple->isTrue()) actualSum+=weight;
                else if(tuple->isUndef()) undefSum+=weight;

                literals.push_back(tuple);
                weightForLiteral.push_back(weight);
            }else
                assert(weightForLiteral[tupleMapping[id]]==weight);
        }
    private:
        std::vector<int> weightForLiteral;
        std::vector<TupleLight*> literals;
        std::unordered_map<int,int> tupleMapping;

        int actualSum;
        int undefSum;

        int upperBound;

};


#endif //WEAKPROPAGATOR_H
