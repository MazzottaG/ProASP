#ifndef LAZYPROPAGATOR_H
#define LAZYPROPAGATOR_H
#include <vector>
#include "AbstractLazyPropagator.h"
#define DEBUG_PROP true
class LazyPropagator{
private:
    std::vector<AbstractLazyPropagator *> propagators;
    std::vector<std::vector<int>> tuplesByPropagator;
    // keeps track of which predicate is watched by which component
    std::unordered_map<int, std::vector<int>> watchedPredicateToPropagators;
    // keeps track of which predicate is defined by which component
    std::unordered_map<int,int> predicateToPropagator;
    std::unordered_set<int> predicatedDefinedByPositiveProgram;
    int conflictualLit;
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
            #ifdef DEBUG_PROP
                    std::cout << "Clearing watchers for propagator " << propagators[i]->getId() << "\n";
            #endif
            tuplesByPropagator[propagators[i]->getId()].clear();
        }
    }
    void storeConflictualLiteral(int conf){
        conflictualLit = conf;
    }
    int getConflictualLiteral(){
        return conflictualLit;
    }
   
    bool computeFixpointLevelZero(Glucose::Solver *s, Glucose::vec<Glucose::Lit> &lits){
        #ifdef DEBUG_PROP
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
        #ifdef DEBUG_PROP
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
            bool generatedProp;
            // #ifdef DEBUG_PROP
            //         std::cout << "Calling propagator " << propagators[i]->getId() << "\n";
            // #endif
            generatedProp = propagators[i]->computeFixpoint(s, tuplesByPropagator[propagators[i]->getId()], confl, lits);
            //clear tuples by propagator after fixpoint is completed
            tuplesByPropagator[propagators[i]->getId()].clear();
            // this is actually a return true since a conflict comes only from a tuple generation
            
            // if (confl != Glucose::CRef_Undef){
            //     #ifdef DEBUG_PROP
            //         std::cout << "Propagator " << propagators[i]->getId() << " fixpoint generated a conflict\n";
            //     #endif
            //     return generated;
            // }
            // #ifdef DEBUG_PROP
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
        #ifdef DEBUG_PROP
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

        // std::cout <<"Reason in explain true of lazy prop: " ;
        // for(unsigned i = 0; i < propagationReason.size(); ++i){
        //     //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));
        //     std::cout << Glucose::var(propagationReason[i]) << " ";
        // }
        // std::cout<< std::endl;
    }

    virtual void explainConflictualTrueLiteral(Glucose::Solver *s, unsigned int var, Glucose::vec<Glucose::Lit> &propagationReason){
        #ifdef DEBUG_PROP
            std::cout <<"Explain conflictual True of lazy propagator\n";
        #endif
        //std::cout <<"ExplainTrue of lazy propagator\n";
        std::vector<Glucose::Lit> toExplain;
        std::vector<int> toExplainPosition;
        Glucose::Lit lit = Glucose::mkLit(var, false);

        for(unsigned i = 1; i < propagationReason.size(); ++i){
            //std::cout <<"Inside for\n";
            //if(!TupleFactory::getInstance().isTupleFromInputInterface(Glucose::var(propagationReason[i]))){
                //std::cout <<"pushed to explain\n";
                toExplain.push_back(propagationReason[i]);
                toExplainPosition.push_back(i);
            //}

        }
       
        int tupleId;
        Tuple *t;
        int currentLevelTupleIndex = -1;
        while (!toExplain.empty()){
            Glucose::Lit lit = toExplain.back();
            //std:cout <<"Explaining "<< Glucose::var(lit) <<"\n";
            int currentPos = toExplainPosition.back();
            //std::cout <<"Current pos " << currentPos<<"\n";
            //std::cout <<"Tuple index: " << Glucose::var(lit)<<"\n";
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
                            //std::cout <<"switch"<<tupleId<<"\n";
                            propagationReason[currentPos] = Glucose::mkLit(tupleId, sign);
                            if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(tupleId)  && s->levelFromPropagator(tupleId) == s->currentLevel())
                                currentLevelTupleIndex = currentPos;
                        }else{
                            //std::cout <<"add\n";
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
            else
            { // level zero tuples have empty reasons but are not facts(see main)
                //std::cout <<"EMPTY REASON\n";
                propagationReason[currentPos] = Glucose::mkLit(tupleId, sign(lit));
                if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(tupleId)  && s->levelFromPropagator(tupleId) == s->currentLevel())
                    currentLevelTupleIndex = currentPos;
            }
        }
        assert(currentLevelTupleIndex != -1);
        // std::cout <<"Found current level tuple at position "<< currentLevelTupleIndex <<" : "<< Glucose::var(propagationReason[currentLevelTupleIndex])<<"\n";
        // std::cout <<"Reason in explain true of lazy prop from conflict: " ;
        // for(unsigned i = 0; i < propagationReason.size(); ++i){
        //     //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));
        //     std::cout << Glucose::var(propagationReason[i]) << " ";
        // }
        // std::cout<< std::endl;
    }

    bool propagateToFalse(Glucose::Solver *s, Tuple* tuple, Glucose::CRef &clause){
        #ifdef DEBUG_PROP
            std::cout <<"Propagate to false of lazy propagator for tuple: ";
            AuxMapHandler::getInstance().printTuple(tuple);
            std::cout <<"\n";
        #endif
        // tupleReasons.clear();
        int predicateId = tuple->getPredicateName();
        if(predicateToPropagator.count(predicateId)){
            Glucose::vec<Glucose::Lit>& tupleReasons =  TupleFactory::getInstance().isTupleFromInputInterface(tuple->getId()) && !s->isAssigned(tuple->getId()) ? tuple->getReasonLits() : s->getReasonClause();
            tupleReasons.clear();
            std::unordered_set<int> reasonSet;
            bool propagated =  propagators[predicateToPropagator[predicateId]]->propagateToFalse(s, tuple, tuple, true, tupleReasons, reasonSet, clause, true);
            //not propagated due to undef in some body or propagation failed due to a conflict
            if(!propagated || clause == Glucose::CRef_Undef){
                std::cout <<"Removed from true solver choice";
                PositiveProgramFactory::getInstance().removeTrueSolverChoice(tuple->getId());
            }
            //conflict propagation No unroll and no propagateLiteral, but the tuple will be set to
            //true and has to be checked in the next level
            if(propagated && clause != Glucose::CRef_Undef){
                PositiveProgramFactory::getInstance().addTrueSolverChoice(tuple->getId());
                std::cout <<"Propagated " << tuple->getId() << "to false";
            }
            return propagated;
        }
        return false;
    }

    AbstractLazyPropagator *getPropagatorFromPredicateId(int predId){
        //std::cout <<"Requiring predicate "<< predId<<"\n";
        assert(predicateToPropagator.count(predId));
        return propagators[predicateToPropagator[predId]];
    }

    // void checkLiteralStatus(Glucose::Solver *s, std::vector<std::pair<int, bool>> lits)
    // {
    //     // TODO ADD THIS WHERE EXPLAINFALSE WILL BE CALLED
    //     // Glucose::vec<Glucose::Lit>& tupleReasons = s->getReasonClause();
    //     for (int i = 0; i < propagators.size(); ++i){
    //         std::cout << "Calling checkLiteral status for prop " << i << "\n";
    //         propagators[i]->checkLiteralStatus(s, lits);
    //     }
    // }
    void attachWatched(int tupleId){
        //std::cout <<"Attach watched " << tupleId <<" to: ";
        int tuplePred = TupleFactory::getInstance().getTupleFromInternalID(tupleId)->getPredicateName();
        for(int propagatorId : watchedPredicateToPropagators[tuplePred]){
            //std::cout << propagatorId << " ";
            tuplesByPropagator[propagatorId].push_back(tupleId);
        }
        //std::cout <<"\n";
    }
    bool isPredicateDefinedInPositiveProgram(int predicateName){
        return predicatedDefinedByPositiveProgram.count(predicateName) > 0;
    }
    static int INSERT_AS_UNDEF;
    static int INSERT_AS_TRUE;
    static int UPDATE_TO_TRUE;
};
#endif /*LAZYPROPAGATOR_H*/
