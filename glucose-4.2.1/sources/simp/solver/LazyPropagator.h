#ifndef LAZYPROPAGATOR_H
#define LAZYPROPAGATOR_H
#include <vector>
#include "AbstractLazyPropagator.h"
//#define DEBUG_PROP
//#define DEBUG_LAZY_PROP
class LazyPropagator{
private:
    std::vector<AbstractLazyPropagator *> propagators;
    std::vector<std::vector<int>> tuplesByPropagator;
    // keeps track of which predicate is watched by which component
    std::unordered_map<int, std::vector<int>> watchedPredicateToPropagators;
    // keeps track of which predicate is defined by which component
    std::unordered_map<int,int> predicateToPropagator;
    std::unordered_set<int> predicatedDefinedByPositiveProgram;

    //undefs found in propagateToFalse call
    std::unordered_set<int> undefsSet;
    //undefs added during propagateToFalse
    std::vector<int> undefsVec;
    //tuple to index in undefsVec up to which undefs must be removed
    std::unordered_map<int, int> tupleToUndefRemoveIndex;

    LazyPropagator();

public:
    static LazyPropagator &getInstance(){
        static LazyPropagator prop;
        return prop;
    }

    ~LazyPropagator(){
        for (AbstractLazyPropagator *p : propagators){
            delete p;
            p = nullptr;
        }
    }
    void clearWatchersAfterConflict(){
        for(int i = 0; i < propagators.size(); ++i){
            bool generatedProp;
            #ifdef DEBUG_LAZY_PROP
                    std::cout << "Clearing watchers for propagator " << propagators[i]->getId() << "\n";
            #endif
            tuplesByPropagator[propagators[i]->getId()].clear();
        }
    }
   
    bool computeFixpointLevelZero(Glucose::Solver *s, Glucose::vec<Glucose::Lit> &lits){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Fixpoint level zero of lazy propagator\n";
        #endif
        bool generated = false;
        for (int i = 0; i < propagators.size(); ++i){
            //std::cout <<"Before propagator "<< i <<"\n"; 
            bool generatedProp;
            generatedProp = propagators[i]->computeFixpointLevelZero(s, lits);
            generated = generated || generatedProp;
            //std::cout <<"propagator "<< i << " generated: "<< generatedProp<<"\n";
        }
        return generated;
    }
    bool computeFixpoint(Glucose::Solver *s, Glucose::CRef &confl, Glucose::vec<Glucose::Lit> &lits){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Fixpoint of lazy propagator\n";
            for(unsigned i = 0; i < tuplesByPropagator.size(); ++i){
                std::cout << "Tuples for propagator " << propagators[i]->getId() <<"\n"; 
                for(unsigned j = 0; j < tuplesByPropagator[i].size(); ++j){
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(tuplesByPropagator[i][j]));
                    std::cout << " ";
                }
                std::cout << "\n";
            }
        #endif
        //TupleFactory::getInstance().addDecisionLevel(s->currentLevel());
        bool generated = false;
        for(int i = 0; i < propagators.size(); ++i){
            bool generatedProp = true;
            // #ifdef DEBUG_LAZY_PROP
            //         std::cout << "Calling propagator " << propagators[i]->getId() << "\n";
            // #endif
            if(confl == Glucose::CRef_Undef)
                generatedProp = propagators[i]->computeFixpoint(s, tuplesByPropagator[propagators[i]->getId()], confl, lits);
            //clear tuples by propagator after fixpoint is completed
            tuplesByPropagator[propagators[i]->getId()].clear();
            // this is actually a return true since a conflict comes only from a tuple generation
            
            // if (confl != Glucose::CRef_Undef){
            //     #ifdef DEBUG_LAZY_PROP
            //         std::cout << "Propagator " << propagators[i]->getId() << " fixpoint generated a conflict\n";
            //     #endif
            //     return generated;
            // }
            // #ifdef DEBUG_LAZY_PROP
            //     if(generatedProp)
            //         std::cout << "Propagator " << propagators[i]->getId() << " fixpoint generated\n";
            //     else
            //         std::cout << "Propagator " << propagators[i]->getId() << " fixpoint did not generate\n";
            // #endif
            generated = generated || generatedProp;
            
        }
        return generated;
    }

    
    virtual void explainTrueLiteral(unsigned int var, Glucose::vec<Glucose::Lit> &propagationReason){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"ExplainTrue of lazy propagator\n";
        #endif
        std::vector<Glucose::Lit> toExplain;
        Glucose::Lit lit = Glucose::mkLit(var, false);
        Glucose::vec<Glucose::Lit> &litReason = TupleFactory::getInstance().getTupleFromInternalID(var)->getReasonLits();
        assert(litReason.size() >= 2);
        toExplain.push_back(lit);
       
        int tupleId;
        Tuple *t;
        while (!toExplain.empty()){
            Glucose::Lit lit = toExplain.back();
            Tuple *tuple = TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(lit));
            toExplain.pop_back();
            Glucose::vec<Glucose::Lit> &tupleReason = tuple->getReasonLits();
            if (tupleReason.size() > 0){
                // ignore tuple and current level lit
                for (unsigned i = 1; i < tupleReason.size(); ++i){
                    bool sign = Glucose::sign(tupleReason[i]);
                    tupleId = Glucose::var(tupleReason[i]);
                    if (TupleFactory::getInstance().isFact(tupleId))
                        propagationReason.push(Glucose::mkLit(tupleId, sign));
                    else
                        toExplain.push_back(tupleReason[i]);
                }
            }
            else
            { // level zero tuples have empty reasons but are not facts(see main)
                propagationReason.push(Glucose::mkLit(tupleId, sign(lit)));
            }
        }

        //DEBUG PRINT
        #ifdef DEBUG_LAZY_PROP
        std::cout <<"Reason in explain true of lazy prop: " ;
        for(unsigned i = 0; i < propagationReason.size(); ++i){
            //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));
            std::cout << Glucose::var(propagationReason[i]) << " ";
        }
        std::cout<< std::endl;
        #endif
    }

    virtual void explainConflictualTrueLiteral(Glucose::Solver *s, unsigned int var, Glucose::vec<Glucose::Lit> &propagationReason){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Explain conflictual True of lazy propagator\n";
        #endif
        std::vector<Glucose::Lit> toExplain;
        std::vector<int> toExplainPosition;
        Glucose::Lit lit = Glucose::mkLit(var, false);

        for(unsigned i = 1; i < propagationReason.size(); ++i){
            toExplain.push_back(propagationReason[i]);
            toExplainPosition.push_back(i);
        }
       
        int tupleId;
        Tuple *t;
        int currentLevelTupleIndex = -1;
        while (!toExplain.empty()){
            Glucose::Lit lit = toExplain.back();
            int currentPos = toExplainPosition.back();
            Tuple *tuple = TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(lit));
            tupleId = tuple->getId();
            toExplain.pop_back();
            toExplainPosition.pop_back();
            Glucose::vec<Glucose::Lit> &tupleReason = tuple->getReasonLits();
            if(tupleReason.size() > 0){
                for (unsigned i = 1; i < tupleReason.size(); ++i){
                    bool sign = Glucose::sign(tupleReason[i]);
                    tupleId = Glucose::var(tupleReason[i]);
                    if(TupleFactory::getInstance().isTupleFromInputInterface(tupleId)){
                        if(i == 1){
                            propagationReason[currentPos] = Glucose::mkLit(tupleId, sign);
                            if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(tupleId)  && s->levelFromPropagator(tupleId) == s->currentLevel())
                                currentLevelTupleIndex = currentPos;
                        }else{
                            //the first tuple goes where the toExplain was
                            propagationReason.push(Glucose::mkLit(tupleId, sign));
                            if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(Glucose::var(lit))  && s->levelFromPropagator(Glucose::var(lit)) == s->currentLevel())
                                currentLevelTupleIndex = tupleReason.size();
                        }
                    }
                    else{
                        toExplain.push_back(tupleReason[i]);
                        toExplainPosition.push_back(propagationReason.size()-1);
                    }
                }
            }
            else{ // level zero tuples have empty reasons but are not facts(see main)
                propagationReason[currentPos] = Glucose::mkLit(tupleId, sign(lit));
                if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(tupleId)  && s->levelFromPropagator(tupleId) == s->currentLevel())
                    currentLevelTupleIndex = currentPos;
            }
        }
        assert(currentLevelTupleIndex != -1);
        //DEBUG 
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Found current level tuple at position "<< currentLevelTupleIndex <<" : "<< Glucose::var(propagationReason[currentLevelTupleIndex])<<"\n";
            std::cout <<"Reason in explain true of lazy prop from conflict: " ;
            for(unsigned i = 0; i < propagationReason.size(); ++i){
                //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));
                std::cout << Glucose::var(propagationReason[i]) << " ";
            }
            std::cout<< std::endl;
        #endif
    }

    bool propagateToFalse(Glucose::Solver *s, Tuple* tuple, Glucose::CRef &clause){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Propagate to false of lazy propagator for tuple: ";
            AuxMapHandler::getInstance().printTuple(tuple);
            std::cout <<"\n";
        #endif
        int predicateId = tuple->getPredicateName();
        if(predicateToPropagator.count(predicateId)){
            Glucose::vec<Glucose::Lit>& tupleReasons =  TupleFactory::getInstance().isTupleFromInputInterface(tuple->getId()) && !s->isAssigned(tuple->getId()) ? tuple->getReasonLits() : s->getReasonClause();
            tupleReasons.clear();
            std::unordered_set<int> reasonSet;
            int lastTupleBeforePropagateToFalse = TupleFactory::getInstance().getLastId();
            tupleReasons.push(Glucose::mkLit(tuple->getId(), true));
            reasonSet.insert(tuple->getId());
            bool propagated =  propagators[predicateToPropagator[predicateId]]->propagateToFalse(s, tuple, tuple, tupleReasons, reasonSet, clause, true);
            //not propagated due to undef in some body or propagation failed due to a conflict
            if(!propagated || clause == Glucose::CRef_Undef){
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Removed from true solver choice";
                #endif
                PositiveProgramFactory::getInstance().removeTrueSolverChoice(tuple->getId());
            }
            //conflict propagation No unroll and no propagateLiteral, but the tuple will be set to
            //true and has to be checked in the next level
            if(propagated && clause != Glucose::CRef_Undef){
                PositiveProgramFactory::getInstance().addTrueSolverChoice(tuple->getId());
                #ifdef DEBUG_LAZY_PROP
                    std::cout <<"Propagated " << tuple->getId() << "to false";
                #endif
            }
            //delete all dummy tuples created during propagateToFalse
            for(int t = TupleFactory::getInstance().getLastId(); t > lastTupleBeforePropagateToFalse; --t){
                TupleFactory::getInstance().deleteLastTuple(t);
            }
            removeUndefsAddedByTuple(tuple->getId(), false);
            tupleToUndefRemoveIndex.clear();

            assert(undefsSet.size() == 0);
            assert(undefsVec.size() == 0);
            return propagated;
        }
        return false;
    }
    
    void addExplainingTuple(int id){
        tupleToUndefRemoveIndex.emplace(std::make_pair(id, undefsVec.size()));
    }

    void addUndefTuple(int id){
        if(!undefsSet.count(id)){
            undefsSet.insert(id);
            undefsVec.push_back(id);
        }
    }

    void addPossibleSupportsForTuple(int id){
        #ifdef DEBUG_LAZY_PROP
            std::cout<<"Saving possible support for tuple: "<<id<<"\n";
        #endif
        for(int i = 0; i < undefsVec.size(); ++i){
            #ifdef DEBUG_LAZY_PROP
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(undefsVec[i]));
                std::cout << " ";
            #endif
            PositiveProgramFactory::getInstance().addPossibleSupportForTuple(id, undefsVec[i]);
        }
        #ifdef DEBUG_LAZY_PROP
            std::cout<<"\n";
        #endif
    }

    void storeUndefsFromTuple(int tuple, std::unordered_set<int>& undefs){
        assert(tupleToUndefRemoveIndex.count(tuple) != 0);
        for(unsigned i = tupleToUndefRemoveIndex.at(tuple); i < undefsVec.size(); ++i){
            undefs.insert(undefsVec.at(i));
        }
    }

    std::vector<int>& getUndefsVec(){
        return undefsVec;
    }

    //remove undefs added from tuple id
    void removeUndefsAddedByTuple(int id, bool noErase = true){
        if(tupleToUndefRemoveIndex.count(id)){
            for(int i = undefsVec.size() -1; i >= tupleToUndefRemoveIndex.at(id); --i){
                undefsSet.erase(undefsVec.at(i));
                undefsVec.pop_back();
            }
            if(!noErase)
                tupleToUndefRemoveIndex.erase(id);
        }
    }
    
    AbstractLazyPropagator *getPropagatorFromPredicateId(int predId){
        assert(predicateToPropagator.count(predId));
        return propagators[predicateToPropagator[predId]];
    }

    void attachWatched(int tupleId){
        int tuplePred = TupleFactory::getInstance().getTupleFromInternalID(tupleId)->getPredicateName();
        for(int propagatorId : watchedPredicateToPropagators[tuplePred]){
            tuplesByPropagator[propagatorId].push_back(tupleId);
        }
    }
    bool isPredicateDefinedInPositiveProgram(int predicateName){
        return predicatedDefinedByPositiveProgram.count(predicateName) > 0;
    }
};
#endif /*LAZYPROPAGATOR_H*/
