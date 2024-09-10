#ifndef POSITIVEPROGRAMFACTORY_H
#define POSITIVEPROGRAMFACTORY_H
#include <unordered_set>
#include "AuxMapHandler.h"
#include "../datastructures/TupleLight.h"

class PositiveProgramFactory{
    private:
        static PositiveProgramFactory instance;
        PositiveProgramFactory(){}
        int lastTupleFromGen;
        std::unordered_set<int> toCheck;
        std::unordered_set<int> trueSolverChoicesForPPTuple;
        std::unordered_map<int, std::unordered_set<int>> supportedTuples;
        
        //used to keep track of which tuples that are undef might propagate a tuple to false
        std::unordered_map<int, std::unordered_set<int>> tupleToPossibleSupport;
        //std::unordered_map<int, int> tupleToPossibleSupport;
        std::unordered_map<int, std::unordered_set<int>> possibleSupportToTuples;
        std::vector<int> toRemovePossibleSupports;
    public:
        static PositiveProgramFactory& getInstance(){
            static PositiveProgramFactory instance;
            return instance;
        }

        void setLastTupleFromGen(int lastTupleID){
            lastTupleFromGen = lastTupleID;
        }

        // checks if tuple is a variable in the SAT solver
        // used as stopping condition for explain procedures
        bool isTupleFromGen(int id){
            return id <= lastTupleFromGen;
        }
        // checks if tuple comes from the input interface of lazy
        // propagator
        bool isTupleFromInputInterface(int id){
            return TupleFactory::getInstance().isTupleFromInputInterface(id);
        }

        //when a conflict is found and a tuple is flipped, there is the possibility
        //that previously founded tuples can now be propagated to false since they 
        //have lost the support that was assigned to them (the rule that updated them in Factory)
        void updateToCheckDueToTuple(unsigned tupleId){
            //std::cout <<"Update to check called\n";
            std::vector<int> toPropagatePossibleUnfoundedness;
            toPropagatePossibleUnfoundedness.push_back(tupleId);
            while(!toPropagatePossibleUnfoundedness.empty()){
                int toPropagate = toPropagatePossibleUnfoundedness.back();
                toPropagatePossibleUnfoundedness.pop_back();
                if(supportedTuples.count(toPropagate)){
                    for(int supportedTuple : supportedTuples[toPropagate]){
                        toCheck.insert(supportedTuple);
                        //std::cout <<"Added to check inside factory " << supportedTuple<< "\n";
                        toPropagatePossibleUnfoundedness.push_back(supportedTuple);
                    }
                }

            }
        }


        void addSupported(int support, int supported){
            //std::cout <<"Added support " << support <<" supported "<< supported <<" \n";
            if(!supportedTuples.count(support))
                supportedTuples.emplace(support, std::unordered_set<int>());
            supportedTuples[support].insert(supported);
            //std::cout <<"After support add \n";
        }
        //remove all supported from tuple plus the supports for tuple
        void removeSupported(int tuple){
            //std::cout <<"Removing support for tuple "<< tuple <<" \n";
            Glucose::vec<Glucose::Lit>& reason = TupleFactory::getInstance().getTupleFromInternalID(tuple)->getReasonLits();
            for(int i = 0; i < reason.size(); ++i){
                supportedTuples[var(reason[i])].erase(tuple);
            }
            //remove all supported from tuple
            if(supportedTuples.count(tuple)){
                supportedTuples[tuple].clear();
                supportedTuples.erase(tuple);
            }
        }


        //if no undef for tuple add, otherwise update
        void addPossibleSupportForTuple(int tupleId, int supportId){
            trueSolverChoicesForPPTuple.erase(tupleId);
            //std::cout <<"Saved possible support for tuple "<< tupleId <<"->support: "<<supportId << "\n";
            if(!tupleToPossibleSupport.count(tupleId)){
                std::pair<int, std::unordered_set<int>> t = std::make_pair(tupleId, std::unordered_set<int>());
                tupleToPossibleSupport.emplace(t);
            }
            tupleToPossibleSupport[tupleId].insert(supportId);
            
            if(!possibleSupportToTuples.count(supportId)){
                std::pair<int, std::unordered_set<int>>t = std::make_pair(supportId, std::unordered_set<int>());
                possibleSupportToTuples.emplace(t);
            }
            possibleSupportToTuples[supportId].insert(tupleId);
            
        }
        //given a possible (undef) support, add its supported tuples as to check
        void removePossibleSupportForTuple(int supportId){
            toRemovePossibleSupports.push_back(supportId);
            if(possibleSupportToTuples.count(supportId)){
                    //std::cout<<"removed\n"; 
                    for(int t : possibleSupportToTuples[supportId]){
                        //std::cout <<"Added to check "<<t<<"\n";
                        toCheck.insert(t);
                    }
            }
        }

        void clearToRemovePossibleSupports(){
            toRemovePossibleSupports.clear();
        }

        //at the end of decision level
        //clear all supports that are not needed anymore
        void removePossibleSupportForTuples(){
            for(int supportId : toRemovePossibleSupports){
                //std::cout <<"Removing possible support for tuple support-> "<<supportId<<"\n";
                if(possibleSupportToTuples.count(supportId)){
                    //std::cout<<"removed\n"; 
                    for(int t : possibleSupportToTuples[supportId]){
                        //std::cout <<"Added to check "<<t<<"\n";
                        //toCheck.insert(t);
                        tupleToPossibleSupport.erase(t);
                    }
                    possibleSupportToTuples[supportId].clear();
                }
            }
        }

        

        //WARNING call only inside undoFixpoint. In that case there is no need
        //to delete supports recursively since each tuple that has been propagated
        // at level x+1 w.r.t. the unrolling level will delete its direct consequences 
        // void removeDirectSupported(int tupleId){
        //     if(supportedTuples.count(tupleId)){
        //         //remove all supported of tuple
        //         supportedTuples[tupleId].clear();
        //     }
        //     //remove tuple from supports
        //     supportedTuples.erase(tupleId);
            
        //     std::cout <<"removed " << tupleId << " from to check\n";
        //     toCheck.erase(tupleId);
        // }

        void addToCheckTuple(int id){
            toCheck.insert(id);
        }

        void addTrueSolverChoice(int id){
            //std::cout <<"ADD TRUE SOLVER CHOICE "<<id<<"\n";

            trueSolverChoicesForPPTuple.insert(id);
        }
        void removeTrueSolverChoice(int id){
            //std::cout <<"REMOVE TRUE SOLVER CHOICE "<<id<<"\n";
            trueSolverChoicesForPPTuple.erase(id);
        }
        
        bool isTupleToCheck(int id){
            return toCheck.count(id);
        }
        void removeToCheckTuple(int id){
            toCheck.erase(id);
        }
        std::unordered_set<int>& getToCheck(){
            //add true solver choices over PP defined 
            for(int choice : trueSolverChoicesForPPTuple){
                //std::cout <<"Adding true solver choice in to check;\n";
                toCheck.insert(choice);
            }
            return toCheck;
        }   
};
#endif /*POSITIVEPROGRAMFACTORY_H*/
