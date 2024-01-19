#ifndef AGGREGATE_PROPAGATOR_H
#define AGGREGATE_PROPAGATOR_H
#include "../datastructures/IndexedSet.h"
#include "../datastructures/TupleFactory.h"
#include "AuxMapHandler.h"
#include "AbstractPropagator.h"
#include <set>

enum AggState {
    TRUE_AGG, FALSE_AGG, UNDEF_AGG
};

class AggregatePropagator: public AbstractPropagator{

    private:

        vector<TupleLight*> literals;
        vector<unsigned> weights;
        std::set<vector<int>> aggTerms;
        
        vector<TupleLight*> ids;
        vector<int> bounds;
        
        unsigned currentSum;
        unsigned maxPossibleSum;

        std::unordered_map<int,unsigned> aggSetMapping;
        std::unordered_map<int,unsigned> aggIdMapping;

        bool aggSetNegated;

    public:

        AggregatePropagator(): currentSum(0),maxPossibleSum(0),aggSetNegated(false){}
        AggregatePropagator(const AggregatePropagator& other): 
            currentSum(other.currentSum),
            maxPossibleSum(other.maxPossibleSum),
            aggSetMapping(other.aggSetMapping),
            aggIdMapping(other.aggIdMapping),
            bounds(other.bounds),
            aggTerms(other.aggTerms),
            aggSetNegated(other.aggSetNegated),
            weights(other.weights){
                for(Tuple* t : other.literals){
                    literals.push_back(t);
                }
                for(Tuple* t : other.ids){
                    ids.push_back(t);
                }
            }
        AggregatePropagator& operator=(const AggregatePropagator& other){ 
            currentSum = other.currentSum;
            maxPossibleSum = other.maxPossibleSum;
            aggSetMapping = other.aggSetMapping;
            aggIdMapping = other.aggIdMapping;
            bounds = other.bounds;
            aggTerms = other.aggTerms;
            weights = other.weights;
            aggSetNegated = other.aggSetNegated;
            literals.clear();
            ids.clear();
            for(Tuple* t : other.literals){
                literals.push_back(t);
            }
            for(Tuple* t : other.ids){
                ids.push_back(t);
            }
        }
        void setAggSetNagated(bool negated){
            aggSetNegated = negated;
        }
        bool isAggSetNegated()const {
            return aggSetNegated;
        }
        std::pair<int,bool> isAggIdStarter(int literal);
        std::pair<int,bool> isAggSetStarter(int literal);
        void addWeightedLiteral(TupleLight* tuple,std::vector<int> terms, unsigned weight, bool negated){
            assert(tuple != NULL || negated);
            if(aggTerms.emplace(terms).second){
                if(negated)
                    setAggSetNagated(true);
                if(tuple == NULL){
                    currentSum += weight;
                }else{
                    auto it = aggSetMapping.emplace(tuple->getId(),literals.size());
                    if(it.second){
                        literals.push_back(tuple);
                        weights.push_back(weight);
                        maxPossibleSum+=weight;
                    }else{
                        weights[it.first->second]+=weight;
                        maxPossibleSum+=weight;
                    }
                }
            }
        }
        void computeSSSum(std::vector<int>& sums){
            assert(sums.size() == 0);
            sums.push_back(0);
            std::unordered_set<int> distinctSums({0});
            for(unsigned i = 0; i<literals.size();i++){
                int weight = weights[i];
                unsigned totalSums = sums.size();
                for(unsigned j=0; j< totalSums; j++){
                    int sum = sums[j]+weight;
                    auto it = distinctSums.emplace(sum);
                    if(it.second)
                        sums.push_back(sums[j]+weight);
                }
            }

            std::sort(sums.begin(), sums.end(), std::less<int>());
            return;
        }

        void addBound(TupleLight* tuple, int bound, bool negated=false){
            assert(!negated);
            auto it = aggIdMapping.emplace(tuple->getId(),ids.size());
            if(it.second){
                ids.push_back(tuple);
                bounds.push_back(bound);
            }
        }
        void printCurrentStatus(){
            std::cout << "Actual sum is "<<currentSum<<std::endl;
            std::cout << "Max possible sum is "<<maxPossibleSum<<std::endl;
            
            std::cout << "Bounds: {\n";
            for(unsigned i = 0; i < ids.size(); i++){
                std::cout << "AggId "<< (ids[i]==NULL ? "NULL": ""); if(ids[i] != NULL) AuxMapHandler::getInstance().printTuple(ids[i]);
                std::cout << "Guard "<< bounds[i]<<std::endl;
            }
            std::cout << "}\n";

            std::cout << "AggSet: {\n";
            for(unsigned i = 0; i < literals.size(); i++){
                std::cout << "Literal "; if(aggSetNegated) std::cout << "not "; AuxMapHandler::getInstance().printTuple(literals[i]);
                std::cout << " Weight "<< weights[i]<<std::endl;
            }
            std::cout << "}\n";


            std::cout << "AggTerms: {\n";
            for(const std::vector<int>& terms : aggTerms){
                std::cout << "   ";
                for(int t : terms){
                    std::cout << t << " ";
                }
                std::cout << std::endl;
            }
            std::cout << "}\n";

        }
        void printName()const { std::cout << "Grounded Aggregate"<<std::endl;}
        void propagateLevelZero(Glucose::Solver*,Glucose::vec<Glucose::Lit>&);
        Glucose::CRef propagate(Glucose::Solver*,Glucose::vec<Glucose::Lit>&,int);
        Glucose::CRef propagateAggregateAsFalse(Glucose::Solver*,std::vector<Glucose::Lit>&,int,TupleLight*,bool,bool=true);
        Glucose::CRef propagateAggregateAsTrue(Glucose::Solver*,std::vector<Glucose::Lit>&,int,TupleLight*,bool,bool=true);
        void attachWatched();
        void init()const{}

        void notifyTrue(int literal){

            auto aggSetStarter = isAggSetStarter(literal);
            if(aggSetStarter.second){
                int currentWeight = weights[aggSetStarter.first >= 0 ? aggSetStarter.first : -aggSetStarter.first];
                if((aggSetNegated && literal < 0) || (!aggSetNegated && literal>=0)){
                    currentSum+=currentWeight;
                }
                maxPossibleSum-=currentWeight;
            }
        }
        void notifyUndef(int literal){

            auto aggSetStarter = isAggSetStarter(literal);
            if(aggSetStarter.second){
                int currentWeight = weights[aggSetStarter.first >= 0 ? aggSetStarter.first : -aggSetStarter.first];
                if((aggSetNegated && literal < 0) || (!aggSetNegated && literal>=0)){
                    currentSum-=currentWeight;
                }
                maxPossibleSum+=currentWeight;
            }
        }
        void printStoredLiterals(){
            // std::cout << "Watched literals"<<std::endl;
            // for(const auto& pair : aggSetMapping){
            //     std::cout << "   Stored id:" << pair.first << " Tuple: ";
            //     AuxMapHandler::getInstance().printTuple(literals[pair.second]);
            //     std::cout << " Real Id: " << literals[pair.second]->getId()<<std::endl;
            // }
        }
        void remapStoredLiteral(){
            // std::cout << "Remapping literals"<<std::endl;
            aggSetMapping.clear();
            for(unsigned litId = 0; litId < literals.size(); litId++){
                aggSetMapping[literals[litId]->getId()]=litId;
                // std::cout << "   Stored id:" << literals[litId]->getId() << " Tuple: ";
                // AuxMapHandler::getInstance().printTuple(literals[litId]);
                // std::cout <<std::endl;
            }
        }
};
#endif