#ifndef POSITIVEPROGRAMFACTORY_H
#define POSITIVEPROGRAMFACTORY_H
#include <unordered_set>
#include "AuxMapHandler.h"
#include "TupleSignSetWithHead.h"
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
        std::unordered_map<int, TupleSignSetWithHead> tupleToPossibleSupports;
        //std::unordered_map<int, int> tupleToPossibleSupports;
        std::unordered_map<int, std::unordered_set<int>> possibleSupportToTuples;

        std::unordered_map<int, TupleSignSetWithHead> tupleToPossibleSupportsTemp;
        std::unordered_map<int, std::unordered_set<int>> possibleSupportToTuplesTemp;

        //entries of possibleSupportsToTuples that have to be invalidated since key is invalidated/propagated
        std::vector<std::pair<int, int>> toRemovePossibleSupports;
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

            if(tupleToSupports.find(supported) == tupleToSupports.end())
                tupleToSupports.emplace(supported, std::unordered_set<int>());
            tupleToSupports[supported].insert(support);
            if(supportToTuples.find(support) == supportToTuples.end())
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
                if(tupleToPossibleSupports.find(id) != tupleToPossibleSupports.end())
                    toRemove.push_back(id);
            }
            for(int id : toRemove){
                toCheck.erase(id);
                // std::cout <<"Removed " << id << " from toCheck\n";
            }

            for(int id : removedToCheck){
                if(tupleToPossibleSupports.find(id) == tupleToPossibleSupports.end()){
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
            for(auto& toRemove : toRemovePossibleSupports){
                possibleSupportToTuples[toRemove.first].erase(toRemove.second);
                if(possibleSupportToTuples[toRemove.first].size() == 0)
                    possibleSupportToTuples.erase(toRemove.first);
            }
            for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                tupleToPossibleSupports.erase(toRemoveTuple);
            }
            for(auto& it : tupleToPossibleSupportsTemp){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"emplacing new tupleToPossibleSupportsTemp ";
                    AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first) : TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
                    std::cout << " ";
                    for(auto support : it.second){
                        AuxMapHandler::getInstance().printTuple(support.value >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(support.value) : TupleFactory::getInstance().getDummyTupleFromInternalID(support.value));
                        std::cout << " ";
                    }
                    std::cout << std::endl;
                #endif
                tupleToPossibleSupports.emplace(it);
            }
            for(auto& it : possibleSupportToTuplesTemp){
                if(possibleSupportToTuples.count(it.first) != 0){
                    for(auto t : it.second){
                        possibleSupportToTuples[it.first].insert(t);
                    }
                }else{
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"emplacing new possibleSupportToTuples ";
                        AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first) : TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
                        std::cout << " ";
                        for(int supported : it.second){
                            AuxMapHandler::getInstance().printTuple(supported >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(supported) : TupleFactory::getInstance().getDummyTupleFromInternalID(supported));
                            std::cout << " ";
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
            // std::cout <<"Saved possible support for tuple "<< tupleId <<"->support: "<<supportId << "\n";
            if(tupleToPossibleSupportsTemp.find(tupleId) == tupleToPossibleSupportsTemp.end()){
                std::pair<int, TupleSignSetWithHead> t = std::make_pair(tupleId, TupleSignSetWithHead());
                tupleToPossibleSupportsTemp.emplace(t);
            }
            tupleToPossibleSupportsTemp[tupleId].insert(supportId, sign);
            
            if(possibleSupportToTuplesTemp.find(supportId) == possibleSupportToTuplesTemp.end()){
                std::pair<int, std::unordered_set<int>> t = std::make_pair(supportId, std::unordered_set<int>());
                possibleSupportToTuplesTemp.emplace(t);
            }
            possibleSupportToTuplesTemp[supportId].insert(tupleId);
        }
        //clear supports for deleted tuple
        void onDeleteLazyTuple(int tupleId){
            //lazy tuples propagated at level zero have no supports
            //and are deleted only just before terminating
            if(tupleToSupports.find(tupleId) == tupleToSupports.end()){
                return;
            }
            updateToCheckDueToTuple(tupleId);
        }
        //given a possible (undef) support, add its supported tuples as to check
        //called when possible support is propagated
        //sign is true if lit is propagated to false, false otherwise
        void removePossibleSupports(int originalTupleId, bool sign, bool fromUndo=false){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<"In removePossibleSupport for " << originalTupleId << "\n";
            #endif
            std::vector<std::pair<int,int>> toRemovePossibleSupportsTemp;
            std::unordered_set<int> toRemoveTupleToPossibleSupportsTemp;
            std::vector<int> toPropagate;
            int tupleId;
            toPropagate.push_back(originalTupleId);
            while(!toPropagate.empty()){
                tupleId = toPropagate.back();
                #ifdef DEBUG_LAZY_PROP
                    std::cout << "Found ";
                    AuxMapHandler::getInstance().printTuple(tupleId >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(tupleId) : TupleFactory::getInstance().getDummyTupleFromInternalID(tupleId) ); 
                    std::cout << " in toPropagate of removePossibleSuppot\n";
                #endif
                sign = tupleId == originalTupleId ? sign : true;
                toPropagate.pop_back();
                //tuple has possible supports saved
                if(tupleToPossibleSupports.find(tupleId) != tupleToPossibleSupports.end()){
                    if(TupleFactory::getInstance().isTupleFromInputInterface(tupleId) && !TupleFactory::getInstance().isPropagationFromLazyProp(tupleId) && !TupleFactory::getInstance().isTupleChecked(tupleId)){
                        #ifdef DEBUG_LAZY_PROP
                            std::cout <<"Added " << tupleId << " in toCheck from removePossibleSupports\n";
                        #endif  
                        toCheck.insert(tupleId);
                    }
                    for(auto support : tupleToPossibleSupports[tupleId]){
                        toRemovePossibleSupports.push_back(std::make_pair(support.value, tupleId));
                    }
                    toRemoveTupleToPossibleSupports.insert(tupleId);
                }

                //tuple is a possible support for some other tuple
                if(possibleSupportToTuples.find(tupleId) != possibleSupportToTuples.end()){
                    //remove tuples that could be supported by tupleId
                    for(auto supported : possibleSupportToTuples[tupleId]){
                        bool signOfSupport = tupleToPossibleSupports[supported].signOf(tupleId);
                        if(TupleFactory::getInstance().isTupleFromInputInterface(supported) && !TupleFactory::getInstance().isPropagationFromLazyProp(supported) && !TupleFactory::getInstance().getTupleFromInternalID(supported)->isFalse()
                            &&  signOfSupport != sign){//tupleToPossibleSupports[supported].signOf(tupleId) != sign
                            toCheck.insert(supported);
                            #ifdef DEBUG_LAZY_PROP
                                std::cout <<"Added "<< supported << "in toCheck from removePossibleSupports\n";
                            #endif
                        }
                        if(signOfSupport != sign){
                            for(auto support : tupleToPossibleSupports[supported]){
                                toRemovePossibleSupports.push_back(std::make_pair(support.value, supported));
                            }
                            if(toRemoveTupleToPossibleSupports.insert(supported).second)
                                toPropagate.push_back(supported);
                        }
                    }
                }
                if(!fromUndo){
                    //tuple has a fresh possible support that has to be invalidated
                    // a key of tupleToPossibleSupportTemp becomes false
                    if(tupleToPossibleSupportsTemp.find(tupleId) != tupleToPossibleSupportsTemp.end()){
                        for(auto support : tupleToPossibleSupportsTemp.at(tupleId)){
                            toRemovePossibleSupportsTemp.push_back(std::make_pair(support.value, tupleId));
                        }
                        toRemoveTupleToPossibleSupportsTemp.insert(tupleId);
                    }
                    
                    if(possibleSupportToTuplesTemp.find(tupleId) != possibleSupportToTuplesTemp.end()){
                        for(int supported : possibleSupportToTuplesTemp[tupleId]){
                            bool signOfSupport = tupleToPossibleSupportsTemp[supported].signOf(tupleId);
                            if(TupleFactory::getInstance().isTupleFromInputInterface(supported) && !TupleFactory::getInstance().isPropagationFromLazyProp(supported) && !TupleFactory::getInstance().getTupleFromInternalID(supported)->isFalse()
                                && signOfSupport != sign){
                                toCheck.insert(supported);
                                #ifdef DEBUG_LAZY_PROP
                                    std::cout <<"Added "<< supported << "in toCheck\n";
                                #endif
                            }
                            if(signOfSupport != sign){
                                for(auto support : tupleToPossibleSupportsTemp[supported]){
                                    toRemovePossibleSupportsTemp.push_back(std::make_pair(support.value, supported));
                                }
                                if(toRemoveTupleToPossibleSupportsTemp.insert(supported).second)
                                    toPropagate.push_back(supported);
                            }
                        }
                    }
                }
            }
            if(!fromUndo){

                for(auto& toRemove : toRemovePossibleSupportsTemp){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Removing " << toRemove.first << " from possibleSupportsTemp\n";
                    #endif
                    possibleSupportToTuplesTemp[toRemove.first].erase(toRemove.second);
                    if(possibleSupportToTuplesTemp[toRemove.first].size() == 0)
                        possibleSupportToTuplesTemp.erase(toRemove.first);
                }
                for(int toRemoveTuple : toRemoveTupleToPossibleSupportsTemp){
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Removing ";
                        AuxMapHandler::getInstance().printTuple(toRemoveTuple >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(toRemoveTuple) : TupleFactory::getInstance().getDummyTupleFromInternalID(toRemoveTuple));
                        std::cout << " from tupleToPossibleSupportsTemp\n";
                    #endif
                    tupleToPossibleSupportsTemp.erase(toRemoveTuple);
                }
            }else{
              for(auto& toRemove : toRemovePossibleSupports){
                possibleSupportToTuples[toRemove.first].erase(toRemove.second);
                if(possibleSupportToTuples[toRemove.first].size() == 0)
                    possibleSupportToTuples.erase(toRemove.first);
                }
                for(int toRemoveTuple : toRemoveTupleToPossibleSupports){
                    tupleToPossibleSupports.erase(toRemoveTuple);
                }

                toRemovePossibleSupports.clear();
                toRemoveTupleToPossibleSupports.clear();  
            }
        }



        bool hasPossibleSupport(int tupleId){
            return tupleToPossibleSupports.find(tupleId) != tupleToPossibleSupports.end() && toRemoveTupleToPossibleSupports.find(tupleId) == toRemoveTupleToPossibleSupports.end();
        }

        //called for clearing support just before adding a new support
        //clears SP for tupleId and its reverse repr
        void clearTupleSupport(int tupleId){
            //std::cout <<"Inside ClearTupleSupport\n";
            assert(tupleToSupports.find(tupleId)!= tupleToSupports.end());
            tupleToSupports.at(tupleId).clear();
            tupleToSupports.erase(tupleId);
        }

        //debug print of possible support data structures with check that the 
        // two maps are consistent
        void printPossibleSupportsStructures(){
            
            std::cout <<"TupleToPossibleSupports: \n";
            for(auto it : tupleToPossibleSupports){
                //std::cout << it.first;
                AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first) : TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
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
                    //std::cout << it1.value;
                    AuxMapHandler::getInstance().printTuple(it1.value >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it1.value): TupleFactory::getInstance().getDummyTupleFromInternalID(it1.value));
                    std::cout <<", " << it1.sign << "> ";
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
            std::cout <<"possibleSupportToTuples: \n";
            for(auto it : possibleSupportToTuples){
                //assert(TupleFactory::getInstance().getTupleFromInternalID(it.first)->isUndef());
                //std::cout << it.first << " -> ";
                AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first): TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
                std::cout << " -> ";
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
                    //std::cout << it1 << " ";
                    AuxMapHandler::getInstance().printTuple(it1 >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it1): TupleFactory::getInstance().getDummyTupleFromInternalID(it1));
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
        }
        void printPossibleSupportsTempStructures(){
            std::cout <<"TupleToPossibleSupportsTemp: \n";
            for(auto it : tupleToPossibleSupportsTemp){
                AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first): TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
                std::cout << " -> ";
                for(auto it1 : it.second){
                    if(!possibleSupportToTuplesTemp.count(it1.value)){
                        std::cout <<"Was expecting to find " << it1.value << " in possibleSupportToTuplesTemp\n";
                        exit(1);
                    }
                    //assert(possibleSupportToTuples.count(it1));
                    AuxMapHandler::getInstance().printTuple(it1.value >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it1.value): TupleFactory::getInstance().getDummyTupleFromInternalID(it1.value));
                }
                std::cout<<std::endl;
            }
            std::cout<<std::endl;
            std::cout <<"possibleSupportToTuplesTemp: \n";
            for(auto it : possibleSupportToTuplesTemp){
                AuxMapHandler::getInstance().printTuple(it.first >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it.first): TupleFactory::getInstance().getDummyTupleFromInternalID(it.first));
                std::cout << " -> ";
                for(int it1 : it.second){
                    if(!tupleToPossibleSupportsTemp.count(it1)){
                        std::cout << "Was expecting to find " << it1 << " in tupleToPossibleSupportsTemp\n";
                        exit(1);
                    }
                    //assert(tupleToPossibleSupports.count(it1));
                    AuxMapHandler::getInstance().printTuple(it1 >= 0 ? TupleFactory::getInstance().getTupleFromInternalID(it1): TupleFactory::getInstance().getDummyTupleFromInternalID(it1));
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
                if(tupleToPossibleSupports.find(currentTuple) == tupleToPossibleSupports.end() && !TupleFactory::getInstance().getTupleFromInternalID(currentTuple)->isFalse() && TupleFactory::getInstance().isTupleFromGen(currentTuple)){
                    toCheck.insert(currentTuple);
                    #ifdef DEBUG_LAZY_PROP
                        std::cout <<"Added toCheck from updateToCheck-tupleId ";
                        AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID((currentTuple)));
                        std::cout << " size now is -> " << toCheck.size() << "\n";
                    #endif
                }
                //clear supports for unrolling tuple and tuples that have lost their support
                if(tupleToSupports.find(currentTuple) != tupleToSupports.end()){
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
                if(supportToTuples.find(currentTuple) != supportToTuples.end()){
                    for(int supported: supportToTuples[currentTuple]){
                       toPropagate.push_back(supported);
                    }
                    
                    supportToTuples[currentTuple].clear();
                    supportToTuples.erase(currentTuple);
                }
            }
        }

        
        void addToCheckTuple(int id){
            if(tupleToPossibleSupports.find(id) == tupleToPossibleSupports.end()){
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
            return toCheck.find(id) != toCheck.end();
        }
        void removeToCheckTuple(int id){
            if(toCheck.find(id) != toCheck.end()){
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
