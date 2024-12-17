#ifndef POSITIVEPROGRAMFACTORY_H
#define POSITIVEPROGRAMFACTORY_H
#include <unordered_set>
#include "AuxMapHandler.h"
#include "TupleSignSet.h"
#include "../datastructures/TupleLight.h"
//#define DEBUG_LAZY_PROP
class PositiveProgramFactory{
    private:
        static PositiveProgramFactory instance;
        PositiveProgramFactory(){}
        int lastTupleFromGen;
        std::unordered_set<int> toCheck;
        // a:- b,c.
        //tupleToSupports
        //<a, {b,c}>
        //supportToTuples
        //<b, {a}>
        //<c, {a}>
        std::unordered_map<int, std::unordered_set<int>> tupleToSupports;
        std::unordered_map<int, std::unordered_set<int>> supportToTuples;

        //used to keep track of which tuples that are undef might propagate a tuple to false
        std::unordered_map<int, TupleSignSet> tupleToPossibleSupports;
        //std::unordered_map<int, int> tupleToPossibleSupports;
        std::unordered_map<int, std::unordered_set<int>> possibleSupportToTuples;

        std::unordered_map<int, TupleSignSet> tupleToPossibleSupportsTemp;
        std::unordered_map<int, std::unordered_set<int>> possibleSupportToTuplesTemp;

        //entries of possibleSupportsToTuples that have to be invalidated since key is invalidated/propagated
        std::unordered_set<int> toRemovePossibleSupports;
        //entries of tupleToPossibleSupports that have to be invalidated since key is invalidated/propagated
        std::unordered_set<int> toRemoveTupleToPossibleSupports;

        //keeps track of tuples on which propagateToFalse was already called
        //such tuples can be definetly removed from toCheck if no conflict, restored in toCheck otherwise 
        std::unordered_set<int> removedToCheck;

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

        void addSupported(int support, int supported){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"Added support "; 
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(support));
                std::cout << " supported "; 
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(supported));
                std::cout << " \n";
            #endif

            if(!tupleToSupports.count(supported))
                tupleToSupports.emplace(supported, std::unordered_set<int>());
            tupleToSupports[supported].insert(support);
            if(!supportToTuples.count(support))
                supportToTuples.emplace(support, std::unordered_set<int>());
            supportToTuples[support].insert(supported);
        }

        //setup for new level
        void newDecisionLevel(){
            possibleSupportToTuplesTemp.clear();
            tupleToPossibleSupportsTemp.clear();
        }
        //keep possibleSupports structures as they were before decision level
        void conflict(){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"Closing decision level with conflict\n";
            #endif
            toRemovePossibleSupports.clear();
            toRemoveTupleToPossibleSupports.clear();
            
            std::vector<int> toRemove;
            for(int id : toCheck){
                if(tupleToPossibleSupports.count(id))
                    toRemove.push_back(id);
            }
            for(int id : toRemove){
                toCheck.erase(id);
                // std::cout <<"Removed " << id << " from toCheck\n";
            }

            for(int id : removedToCheck){
                if(!tupleToPossibleSupports.count(id)){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Added to check from conflict " << id << "\n";
                    #endif
                    toCheck.insert(id);
                }
            }
            removedToCheck.clear();
            newDecisionLevel();
        }
        //only supports will be updated from unroll
        void clearDueToRestart(){
            toRemovePossibleSupports.clear();
            toRemoveTupleToPossibleSupports.clear();
            possibleSupportToTuplesTemp.clear();
            tupleToPossibleSupportsTemp.clear();
        }

        void printStats(){
            std::cout<<"---------------------------------------------\n";
            std::cout << "PositiveProgramFactory stats\n";
            std::cout <<"\tSize of toCheck " << getToCheck().size() << "\n";

            std::cout <<"\tSize of tupleToSupports " << tupleToSupports.size() << "\n";
            std::cout <<"\tSize of supportToTuples " << supportToTuples.size() << "\n";

            std::cout <<"\tSize of tupleToPossibleSupports " << tupleToPossibleSupports.size() << "\n";
            std::cout <<"\tSize of possibleSupportToTuples " << possibleSupportToTuples.size() << "\n";

            std::cout <<"\tSize of tupleToPossibleSupportsTemp " << tupleToPossibleSupportsTemp.size() << "\n";
            std::cout <<"\tSize of possibleSupportToTuplesTemp " << possibleSupportToTuplesTemp.size() << "\n";
            std::cout<<"---------------------------------------------\n";
        }
        //persist diff of current level
        void closeDecisionLevelNoConflict(){
            
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"Closing decision level without confl\n";
            #endif
            
            for(int toRemoveSupport : toRemovePossibleSupports){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Removing " << toRemoveSupport << " from possibleSupports\n";
                #endif
                for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                    possibleSupportToTuples[toRemoveSupport].erase(toRemoveTuple);
                    if(possibleSupportToTuples[toRemoveSupport].size() == 0)
                        possibleSupportToTuples.erase(toRemoveSupport);
                }
            }

            for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Removing " << toRemoveTuple << " from tupleToPossibleSupports\n";
                #endif
                tupleToPossibleSupports.erase(toRemoveTuple);
            }

            for(auto it : tupleToPossibleSupportsTemp){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"emplacing new tupleToPossibleSupportsTemp " << it.first << " ";
                    for(auto support : it.second){
                        std::cout << support.value << " ";
                    }
                    std::cout << std::endl;
                #endif
                tupleToPossibleSupports.emplace(it);
            }
            for(auto it : possibleSupportToTuplesTemp){
                if(possibleSupportToTuples.count(it.first) != 0){
                    for(auto t : it.second){
                        possibleSupportToTuples[it.first].insert(t);
                    }
                }else{
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"emplacing new possibleSupportToTuples " << it.first << " ";
                        for(int supported : it.second){
                            std::cout << supported << " ";
                        }
                        std::cout << std::endl;
                    #endif
                    possibleSupportToTuples.emplace(it);
                }
            }
            toRemovePossibleSupports.clear();
            toRemoveTupleToPossibleSupports.clear();
            removedToCheck.clear();
        }

        //if no undef for tuple add, otherwise update
        void addPossibleSupportForTuple(int tupleId, int supportId, bool sign){
            //std::cout <<"Saved possible support for tuple "<< tupleId <<"->support: "<<supportId << "\n";
            if(!tupleToPossibleSupportsTemp.count(tupleId)){
                std::pair<int, TupleSignSet> t = std::make_pair(tupleId, TupleSignSet());
                tupleToPossibleSupportsTemp.emplace(t);
            }
            tupleToPossibleSupportsTemp[tupleId].insert(supportId, sign);
            
            if(!possibleSupportToTuplesTemp.count(supportId)){
                std::pair<int, std::unordered_set<int>> t = std::make_pair(supportId, std::unordered_set<int>());
                possibleSupportToTuplesTemp.emplace(t);
            }
            possibleSupportToTuplesTemp[supportId].insert(tupleId);
            
        }
        //clear supports for deleted tuple
        void onDeleteLazyTuple(int tupleId){
            //lazy tuples propagated at level zero have no supports
            //and are deleted only just before terminating
            if(!tupleToSupports.count(tupleId)){
                return;
            }
            updateToCheckDueToTuple(tupleId);
        }
        //given a possible (undef) support, add its supported tuples as to check
        //called when possible support is propagated
        //sign is true if lit is propagated to false, false otherwise
        void removePossibleSupports(int tupleId, bool sign){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"In removePossibleSupport for " << tupleId << "\n";
            #endif
            //tuple has possible supports saved
            if(tupleToPossibleSupports.count(tupleId)){
                if(!TupleFactory::getInstance().isPropagationFromLazyProp(tupleId) && !TupleFactory::getInstance().isTupleChecked(tupleId)){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Added " << tupleId << " in toCheck from removePossibleSupports\n";
                    #endif  
                    toCheck.insert(tupleId);
                }
                for(auto support : tupleToPossibleSupports[tupleId]){
                    toRemovePossibleSupports.insert(support.value);
                }
                toRemoveTupleToPossibleSupports.insert(tupleId);
            }

            //tuple is a possible support for some other tuple
            if(possibleSupportToTuples.count(tupleId)){
                //remove tuples that could be supported by tupleId
                for(auto supported : possibleSupportToTuples[tupleId]){
                    bool signOfSupport = tupleToPossibleSupports[supported].signOf(tupleId);
                    if(!TupleFactory::getInstance().isPropagationFromLazyProp(supported) && !TupleFactory::getInstance().getTupleFromInternalID(supported)->isFalse()
                        &&  signOfSupport != sign){//tupleToPossibleSupports[supported].signOf(tupleId) != sign
                        toCheck.insert(supported);
                        #ifdef DEBUG_LAZY_PROP
                            std::cout <<"Added "<< supported << "in toCheck from removePossibleSupports\n";
                        #endif
                    }
                    if(signOfSupport != sign){
                        for(auto support : tupleToPossibleSupports[supported]){
                            toRemovePossibleSupports.insert(support.value);
                        }
                        
                        toRemoveTupleToPossibleSupports.insert(supported);
                    }
                }
                //remove tupleId from all possibleSupports 
                toRemovePossibleSupports.insert(tupleId);
            }

            //tuple has a fresh possible support that has to be invalidated
            // a key of tupleToPossibleSupportTemp becomes false
            if(tupleToPossibleSupportsTemp.count(tupleId)){
                for(auto support : tupleToPossibleSupportsTemp.at(tupleId)){
                    possibleSupportToTuplesTemp[support.value].erase(tupleId);
                    //std::cout <<"Removing "<< support <<" from tupleToPossibleSupportsTemp\n";
                    if(possibleSupportToTuplesTemp[support.value].size() == 0){
                        possibleSupportToTuplesTemp.erase(support.value);
                    }
                }
                tupleToPossibleSupportsTemp.erase(tupleId);
                //std::cout <<"Removing " << tupleId << " from possibleSupportToTuplesTemp\n";
            }
            
            if(possibleSupportToTuplesTemp.count(tupleId)){
                std::unordered_set<int> toRemovePossibleSupportsTemp;
                std::unordered_set<int> toRemoveTupleToPossibleSupportsTemp;
                for(int supported : possibleSupportToTuplesTemp[tupleId]){
                    bool signOfSupport = tupleToPossibleSupportsTemp[supported].signOf(tupleId);
                    if(!TupleFactory::getInstance().isPropagationFromLazyProp(supported) && !TupleFactory::getInstance().getTupleFromInternalID(supported)->isFalse()
                        && signOfSupport != sign){//tupleToPossibleSupportsTemp[supported].signOf(tupleId) != sign
                        toCheck.insert(supported);
                        #ifdef DEBUG_LAZY_PROP
                            std::cout <<"Added "<< supported << "in toCheck\n";
                        #endif
                    }
                    if(signOfSupport != sign){
                        for(auto support : tupleToPossibleSupportsTemp[supported]){
                            toRemovePossibleSupportsTemp.insert(support.value);
                        }
                        toRemoveTupleToPossibleSupportsTemp.insert(supported);
                    }
                }
                toRemovePossibleSupportsTemp.insert(tupleId);

                for(int toRemoveSupport : toRemovePossibleSupportsTemp){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Removing " << toRemoveSupport << " from possibleSupportsTemp\n";
                    #endif
                    for(int toRemoveTuple : toRemoveTupleToPossibleSupportsTemp){
                        possibleSupportToTuplesTemp[toRemoveSupport].erase(toRemoveTuple);
                        if(possibleSupportToTuplesTemp[toRemoveSupport].size() == 0)
                            possibleSupportToTuplesTemp.erase(toRemoveSupport);
                    }
                }

                for(int toRemoveTuple : toRemoveTupleToPossibleSupportsTemp){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Removing " << toRemoveTuple << " from tupleToPossibleSupportsTemp\n";
                    #endif
                    tupleToPossibleSupportsTemp.erase(toRemoveTuple);
                }
            
            }
            
        }

        void removePossibleSupportsFromUndo(int tupleId, bool sign){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"In removePossibleSupportsFromUndo for " << tupleId << "\n";
            #endif
            //tuple has possible supports saved
            if(tupleToPossibleSupports.count(tupleId)){
                if(!TupleFactory::getInstance().isPropagationFromLazyProp(tupleId) && !TupleFactory::getInstance().isTupleChecked(tupleId)){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Added " << tupleId << " in toCheck from removePossibleSupportsFromUndo\n";
                    #endif  
                    toCheck.insert(tupleId);
                }
                for(auto support : tupleToPossibleSupports[tupleId]){
                    toRemovePossibleSupports.insert(support.value);
                }
                toRemoveTupleToPossibleSupports.insert(tupleId);
            }

            //tuple is a possible support for some other tuple
            if(possibleSupportToTuples.count(tupleId)){
                //remove tuples that could be supported by tupleId
                for(auto supported : possibleSupportToTuples[tupleId]){
                    bool signOfSupport = tupleToPossibleSupports[supported].signOf(tupleId);
                    if(!TupleFactory::getInstance().isPropagationFromLazyProp(supported) && !TupleFactory::getInstance().getTupleFromInternalID(supported)->isFalse()
                        &&  signOfSupport != sign){//tupleToPossibleSupports[supported].signOf(tupleId) != sign
                        toCheck.insert(supported);
                        #ifdef DEBUG_LAZY_PROP
                            std::cout <<"Added "<< supported << "in toCheck from removePossibleSupportsFromUndo\n";
                        #endif
                    }
                    if(signOfSupport != sign){
                        for(auto support : tupleToPossibleSupports[supported]){
                            toRemovePossibleSupports.insert(support.value);
                        }
                        
                        toRemoveTupleToPossibleSupports.insert(supported);
                    }
                }
                //remove tupleId from all possibleSupports 
                toRemovePossibleSupports.insert(tupleId);
            }
            for(int toRemoveSupport : toRemovePossibleSupports){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Removing " << toRemoveSupport << " from possibleSupports\n";
                #endif
                for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                    possibleSupportToTuples[toRemoveSupport].erase(toRemoveTuple);
                    if(possibleSupportToTuples[toRemoveSupport].size() == 0)
                        possibleSupportToTuples.erase(toRemoveSupport);
                }
            }

            for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Removing " << toRemoveTuple << " from tupleToPossibleSupports\n";
                #endif
                tupleToPossibleSupports.erase(toRemoveTuple);
            }
            toRemovePossibleSupports.clear();
            toRemoveTupleToPossibleSupports.clear();    
        }

        bool hasPossibleSupport(int tupleId){
            return tupleToPossibleSupports.count(tupleId) > 0 && !toRemovePossibleSupports.count(tupleId) ;
        }

        //called for clearing support just before adding a new support
        //clears SP for tupleId and its reverse repr
        void clearTupleSupport(int tupleId){
            //std::cout <<"Inside ClearTupleSupport\n";
            assert(tupleToSupports.count(tupleId));
            tupleToSupports.at(tupleId).clear();
            tupleToSupports.erase(tupleId);
        }

        //debug print of possible support data structures with check that the 
        // two maps are consistent
        void printPossibleSupportsStructures(){
            
            std::cout <<"TupleToPossibleSupports: \n";
            for(auto it : tupleToPossibleSupports){
                //std::cout << it.first;
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(it.first));
                std::cout  << " -> ";
                
                for(auto it1 : it.second){
                    if(!possibleSupportToTuples.count(it1.value)){
                        std::cout <<"Was expecting to find " << it1.value << " in possibleSupportToTuples\n";
                        exit(1);
                    }
                    //assert(possibleSupportToTuples.count(it1));
                    // if(TupleFactory::getInstance().getTupleFromInternalID(it1.value)->isFalse()){
                    //     std::cout << "Found " << it1.value << " in tupleToPossibleSupports but is false\n";
                    //     exit(1);
                    // }
                    //assert(!TupleFactory::getInstance().getTupleFromInternalID(it1)->isFalse());
                    std::cout << "<";
                    std::cout << it1.value;
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(it1.value));
                    std::cout <<", " << it1.sign << "> ";
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
            std::cout <<"possibleSupportToTuples: \n";
            for(auto it : possibleSupportToTuples){
                //assert(TupleFactory::getInstance().getTupleFromInternalID(it.first)->isUndef());
                std::cout << it.first << " -> ";
                for(int it1 : it.second){
                    if(!tupleToPossibleSupports.count(it1)){
                        std::cout << "Was expecting to find " << it1 << " in tupleToPossibleSupports\n";
                        exit(1);
                    }
                    // if(TupleFactory::getInstance().getTupleFromInternalID(it1)->isFalse()){
                    //     std::cout << "Found " << it1 << " in possibleSupportsToTuple but is false\n";
                    //     exit(1);
                    // }
                    //assert(!TupleFactory::getInstance().getTupleFromInternalID(it1)->isFalse());
                    //assert(tupleToPossibleSupports.count(it1));
                    std::cout << it1 << " ";
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
        }
        void printPossibleSupportsTempStructures(){
            std::cout <<"TupleToPossibleSupportsTemp: \n";
            for(auto it : tupleToPossibleSupportsTemp){
                std::cout << it.first << " -> ";
                for(auto it1 : it.second){
                    if(!possibleSupportToTuplesTemp.count(it1.value)){
                        std::cout <<"Was expecting to find " << it1.value << " in possibleSupportToTuplesTemp\n";
                        exit(1);
                    }
                    //assert(possibleSupportToTuples.count(it1));
                    std::cout << it1.value << " ";
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
            std::cout <<"possibleSupportToTuplesTemp: \n";
            for(auto it : possibleSupportToTuplesTemp){
                std::cout << it.first << " -> ";
                for(int it1 : it.second){
                    if(!tupleToPossibleSupportsTemp.count(it1)){
                        std::cout << "Was expecting to find " << it1 << " in tupleToPossibleSupportsTemp\n";
                        exit(1);
                    }
                    //assert(tupleToPossibleSupports.count(it1));
                    std::cout << it1 << " ";
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
        } 

        //debug print of supported structures
        void printSupported(){
            std::cout <<"Printing supports\n";
            for(auto support : tupleToSupports){
                if(!TupleFactory::getInstance().getTupleFromInternalID(support.first)->isTrue()){
                    std::cout <<"Was expecting " << support.first << " to be true but it is not\n";
                    //exit(1);
                }
                //assert(TupleFactory::getInstance().getTupleFromInternalID(support.first)->isTrue());
                if(support.second.size() > 0){
                    std::cout << "Tuple ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(support.first));
                    std::cout << " is supported by: ";
                    for(int supported : support.second){
                        std::cout <<" ";
                        AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(supported));
                        if(!supportToTuples.count(supported)){
                            std::cout << "Was expecting to find " << supported << " in supportToTuples which is not present\n";
                            exit(1);
                        }
                    }
                    std::cout << std::endl;
                }
            }
            for(auto supported : supportToTuples) {
                if(TupleFactory::getInstance().getTupleFromInternalID(supported.first)->isUndef()){
                    std::cout << "Was expecting "<< supported.first << " not to be Undef but it is\n";
                    //exit(1);
                }
                //assert(!TupleFactory::getInstance().getTupleFromInternalID(supported.first)->isUndef());
                std::cout <<"supported: ";
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(supported.first)); 
                std::cout << " supports ";
                for(int t : supported.second){
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(t));
                    std::cout << " ";
                    if(!tupleToSupports.count(t)){
                        std::cout << "Was expecting to find " << t << " in tupleToSupports which is not present\n";
                        exit(1);
                    }
                }
                std::cout << std::endl;
            }
        }
        
        void updateToCheckDueToTuple(int tupleId){
            
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"In updateToCheckDueToTuple for ";
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(tupleId));  
                std::cout << "\n";
            #endif
            
            std::vector<int> toPropagate;
            toPropagate.push_back(tupleId);
            int numProp = 0;
            //from tuple make and undo of all consequences of tuple (supported from tupleId have lost their support)
            while(!toPropagate.empty()){
                numProp++;
                #ifdef DEBUG_LAZY_PROP
                    std::cout<< "Found ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(toPropagate.back()));  
                    std::cout << " in toPropagate of updateToCheck\n";
                #endif
                int currentTuple = toPropagate.back();
                toPropagate.pop_back();
                //do not add as to check if either tuple is not from the lazy program or there is still
                //a valid possible support to it
                if(!tupleToPossibleSupports.count(currentTuple) && !TupleFactory::getInstance().getTupleFromInternalID(currentTuple)->isFalse() && TupleFactory::getInstance().isTupleFromGen(currentTuple)){
                    toCheck.insert(currentTuple);
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Added toCheck from updateToCheck-tupleId ";
                        AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID((currentTuple)));
                        std::cout << " size now is -> " << toCheck.size() << "\n";
                    #endif
                }
                //clear supports for unrolling tuple and tuples that have lost their support
                if(tupleToSupports.count(currentTuple)){
                    for(int support : tupleToSupports[currentTuple]){
                        supportToTuples[support].erase(currentTuple);
                        #ifdef DEBUG_LAZY_PROP
                            std::cout << "Removed ";
                            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(support));
                            std::cout << " as support for ";
                            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(currentTuple));
                            std::cout << std::endl;
                        #endif
                        if(supportToTuples[support].size() == 0)
                            supportToTuples.erase(support);
                    }
                    tupleToSupports.at(currentTuple).clear();
                    tupleToSupports.erase(currentTuple);
                }
                //add supported from current tuple as toPropagate
                if(supportToTuples.count(currentTuple)){
                    for(int supported: supportToTuples[currentTuple]){
                       toPropagate.push_back(supported);
                    }
                    
                    supportToTuples[currentTuple].clear();
                    supportToTuples.erase(currentTuple);
                }
            }
        }

        
        void addToCheckTuple(int id){
            if(!tupleToPossibleSupports.count(id)){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Added to check " << id << "\n";
                #endif
                toCheck.insert(id);
            }
        }

        void addTrueSolverChoice(int id){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"Added true solver choice " << id << "\n";
            #endif
            toCheck.insert(id);
        }
        bool isTupleToCheck(int id){
            return toCheck.count(id) > 0;
        }
        void removeToCheckTuple(int id){
            if(toCheck.count(id)){
                toCheck.erase(id);
                removedToCheck.insert(id);
            }
        }
        void clearToCheck(){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"Cleared to check\n";
            #endif
            toCheck.clear();
        }
        std::unordered_set<int> getToCheck(){
            return toCheck;
        }   
};
#endif /*POSITIVEPROGRAMFACTORY_H*/
