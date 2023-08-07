#ifndef EXTERNALPROPAGATOR_H
#define EXTERNALPROPAGATOR_H
#include "AbstractPropagator.h"
#include <iostream>
#include <vector>
#include "AuxMapHandler.h"
#include "ModelExpansion.h"

class Propagator{
    public:

        static Propagator& getInstance(){
            static Propagator prop;
            return prop;
        }
        
        ~Propagator(){
            std::cout << "Destroying propagators"<<std::endl;
            for(AbstractPropagator* prop : propagators){
                delete prop;
            }
        }
        void attachWatchers(){
            for(AbstractPropagator* prop : propagators){
                prop->attachWatched();
            }
        }
        void propagateAtLevel0(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits){
            for(AbstractPropagator* prop : propagators){
                std::cout << "Calling extenral progragator ";
                prop->printName();
                prop->propagateLevelZero(s,lits);
            }
        }
        void expandModel(){
            ModelExpansion::getInstance().generate(NULL);
        }
        void updateSumForTrueLit(Tuple*);
        void updateSumForUndefLit(Tuple*);

        Glucose::CRef propagateLiteral(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits,int literal){
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
                    TupleFactory::getInstance().removeFromCollisionsList(starter->getId());
                    if(literal > 0) AuxMapHandler::getInstance().insertTrue(insertResult);
                    else AuxMapHandler::getInstance().insertFalse(insertResult);
                }
                updateSumForTrueLit(starter);
            }
            else{
                if((literal > 0 && starter->isFalse()) || (literal < 0 && starter->isTrue())) {
                    std::cout << "Error: literal already assigned with different value" <<std::endl; 
                    exit(180);
                }
            }     
            if(!active) return Glucose::CRef_Undef;
            for(AbstractPropagator* prop : TupleFactory::getInstance().getWatcher(literal<0 ? -literal : literal,literal<0)){
                Glucose::CRef clause = prop->propagate(s,lits,literal);
                if(clause != Glucose::CRef_Undef){
                    return clause;
                }
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
            if(!starter->isUndef()){
                updateSumForUndefLit(starter);
                const auto& insertResult = starter->setStatus(Undef);
                if(insertResult.second){
                    #ifdef DEBUG_PROP
                    std::cout << "Unrolling ";AuxMapHandler::getInstance().printTuple(starter);
                    #endif
                    TupleFactory::getInstance().removeFromCollisionsList(starter->getId());
                    AuxMapHandler::getInstance().insertUndef(insertResult);
                }
            }
            else{
                #ifdef DEBUG_PROP
                std::cout << "Warning: Unrolling literal not assigned yet" <<std::endl;
                #endif
            }
        }
        void activate(){active=true;}
    private:    
        Propagator();
        bool active;
        std::vector<AbstractPropagator*> propagators;
};

#endif