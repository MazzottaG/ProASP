#ifndef EXTERNALPROPAGATOR_H
#define EXTERNALPROPAGATOR_H
#include "AggregatePropagator.h"
#include <iostream>
#include <vector>
#include "AuxMapHandler.h"
#include "ModelExpansion.h"
#include "PositiveProgramFactory.h"
#include "LazyPropagator.h"
class Propagator{
    public:

        static Propagator& getInstance(){
            static Propagator prop;
            return prop;
        }
        
        ~Propagator(){
            for(AbstractPropagator* prop : propagators){
                if(prop != NULL){
                    delete prop;
                    prop = NULL;
                }
            }
        }
        void attachWatchers(){
            for(AbstractPropagator* prop : propagators){
                prop->attachWatched();
            }
        }
        void printStoredLiterals(){
            for(AbstractPropagator* prop : propagators){
                // std::cout << "Propagator ";
                prop->printName();
                prop->printStoredLiterals();
                // std::cout << "--------------------------";
            }
        }
        void propagateAtLevel0(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits){
            for(AbstractPropagator* prop : propagators){
                // std::cout << "Calling ";prop->printName();
                prop->propagateLevelZero(s,lits);
                // std::cout << "Completed ";prop->printName();
                // std::cout << std::endl;
            }
        }
        void expandModel(){
            ModelExpansion::getInstance().generate(NULL);
        }
        void updateSumForTrueLit(Tuple*);
        void updateSumForTrueLitGroundAggregate(int literal){
            // for(AbstractPropagator* prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
            for(unsigned prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
                // prop->notifyTrue(literal);
                propagators[prop]->notifyTrue(literal);
            }
        }
        void updateSumForUndefLit(Tuple*,TruthStatus);
        void updateSumForUndefLitGroundAggregate(int literal){
            // for(AbstractPropagator* prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
            //     prop->notifyUndef(literal);
            // }
            for(unsigned prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
                propagators[prop]->notifyUndef(literal);
            }
        }

        Glucose::CRef propagateLiteral(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits,int literal){
            // nested_calls++;
            // assert(nested_calls>0);
            // for(int i = 0 ; i< nested_calls;i++) std::cout << "   ";
            // std::cout << "------------"<<std::endl;
            Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID( literal > 0 ? literal : -literal);;
            if(starter == NULL){
                if(literal != 0){
                    std::cout << "Error: unable to find starting literal" <<std::endl; 
                    exit(180);
                }
            }
            if(starter->isUndef()){
                const auto& insertResult = starter->setStatus(literal > 0 ? True : False);
                if(insertResult.second){
                    bool starterIsFromLazyPred = LazyPropagator::getInstance().isPredicateDefinedInPositiveProgram(starter->getPredicateName());
                    TupleFactory::getInstance().removeFromCollisionsList(starter->getId());
                    //IsChecked is true for tuples propagated via externalPropagation
                    PositiveProgramFactory::getInstance().removePossibleSupports(starter->getId(), literal <= 0);
                    if(literal > 0){
                        AuxMapHandler::getInstance().insertTrue(insertResult);
                        if(starterIsFromLazyPred){
                            if(!TupleFactory::getInstance().isPropagationFromLazyProp(starter->getId())){
                                PositiveProgramFactory::getInstance().addToCheckTuple(starter->getId());
                            }
                            else{
                                PositiveProgramFactory::getInstance().removeToCheckTuple(starter->getId());
                            }
                        }
                    }
                    else{
                        PositiveProgramFactory::getInstance().removeToCheckTuple(starter->getId());
                        AuxMapHandler::getInstance().insertFalse(insertResult);
                    }
                    updateSumForTrueLit(starter);
                    updateSumForTrueLitGroundAggregate(literal);
                    LazyPropagator::getInstance().attachWatched(starter->getId());
                }
            }
            else{
                if((literal > 0 && starter->isFalse()) || (literal < 0 && starter->isTrue())) {
                    std::cout << "Error: literal already assigned with different value" <<std::endl;
                    exit(180);
                }
            }     
            if(!active) {

                // for(int i = 0 ; i< nested_calls;i++) std::cout << "   ";
                // std::cout << "------------"<<std::endl;
                // nested_calls--;
                return Glucose::CRef_Undef;
            }
            // for(AbstractPropagator* prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
                // std::cout << "Calling ";prop->printName();
                // Glucose::CRef clause = prop->propagate(s,lits,literal);
            for(unsigned prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
                // std::cout << "Calling ";propagators[prop]->printName();std::cout << std::endl;
                Glucose::CRef clause = propagators[prop]->propagate(s,lits,literal);
                if(clause != Glucose::CRef_Undef){
                    // std::cout << "Found Conflict in propagator"<<std::endl;

                    // for(int i = 0 ; i< nested_calls;i++) std::cout << "   ";
                    // std::cout << "------------"<<std::endl;
                    // nested_calls--;
                    return clause;
                }
            }

            // for(int i = 0 ; i< nested_calls;i++) std::cout << "   ";
            // std::cout << "------------"<<std::endl;
            // nested_calls--;
            if(literal < 0 ){
                PositiveProgramFactory::getInstance().removeToCheckTuple(starter->getId());
            }
            return Glucose::CRef_Undef;
        }
        void init(){
            for(AbstractPropagator* prop : propagators){
                prop->init();
            }
            return;
        }

        void unrollLiteral(unsigned x){
            TupleLight* starter = TupleFactory::getInstance().getTupleFromInternalID( x );
            if(starter == NULL){if(x != 0){std::cout << "Error: unable to find unrolling literal" <<std::endl; exit(180);}}
            bool starterIsFromLazyPred = LazyPropagator::getInstance().isPredicateDefinedInPositiveProgram(starter->getPredicateName());
            if(!starter->isUndef()){
                int sign = starter->isFalse() ? -1 : 1;
                //if(sign == 1){
                starter->getReasonLits().clear();
                //}
                TruthStatus val = starter->getTruthValue();
                const auto& insertResult = starter->setStatus(Undef);
                if(insertResult.second){
                    //TupleFactory::getInstance().removeCheckedTuple(starter->getId());
                    updateSumForUndefLit(starter,val);
                    updateSumForUndefLitGroundAggregate(sign*x);
                    #ifdef DEBUG_PROP
                    std::cout << "Unrolling ";AuxMapHandler::getInstance().printTuple(starter);
                    #endif
                    
                    //if(TupleFactory::getInstance().isPropagationFromLazyProp(starter->getId())){
                        //std::cout <<"Unrolling lazy\n";
                        //PositiveProgramFactory::getInstance().removeSupported(starter->getId());
                    //}
                    
                    TupleFactory::getInstance().removeFromCollisionsList(starter->getId());
                    AuxMapHandler::getInstance().insertUndef(insertResult);
                }
            }
            else{
                #ifdef DEBUG_PROP
                    std::cout << "Warning: Unrolling literal not assigned yet" <<std::endl;
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(starter->getId()));
                    std::cout << std::endl;
                #endif
            }

            //set all tuples supported by starter as toCheck 
            //(possibly only starter itself if it was propagated by eager prop)
            if(starterIsFromLazyPred){
                LazyPropagator::getInstance().addAlwaysToCheckTuple(starter->getId(), starter->getPredicateName());
                TupleFactory::getInstance().removePropagationFromLazyProp(starter->getId());
                PositiveProgramFactory::getInstance().updateToCheckDueToTuple(starter->getId());
            }
            //if tuple was a true solver choice, remove such that it will not be checked anymore
            //at the end of each decision level
            //PositiveProgramFactory::getInstance().removeToCheckTuple(starter->getId());
        }
        void activate(){active=true;}
        void addPropagator(AbstractPropagator* prop){ prop->setId(propagators.size()); propagators.push_back(prop); }
        AbstractPropagator* getPropagator(int propId){
            assert(propId>0 && propId < propagators.size());
            return propagators[propId];
        }
    private:
        int nested_calls = 0;
        Propagator();
        bool active;
        bool fullGrounding;
        std::vector<AbstractPropagator*> propagators;
};

#endif