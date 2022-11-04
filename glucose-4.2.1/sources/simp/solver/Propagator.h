#ifndef EXTERNALPROPAGATOR_H
#define EXTERNALPROPAGATOR_H
#include "AbstractPropagator.h"
#include <iostream>
#include <vector>
#include "AuxMapHandler.h"

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
        void propagateAtLevel0(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits){
            for(AbstractPropagator* prop : propagators){
                prop->propagateLevelZero(s,lits);
            }
        }

        Glucose::CRef propagateLiteral(Glucose::Solver* s,Glucose::vec<Glucose::Lit>& lits,int literal){
            for(AbstractPropagator* prop : propagators){
                Glucose::CRef clause = prop->propagate(s,lits,literal);
                if(clause != Glucose::CRef_Undef)
                    return clause;
            }
            return Glucose::CRef_Undef;
        }

        void unrollLiteral(unsigned x){
            TupleLight* starter = TupleFactory::getInstance().getTupleFromInternalID( x );
            if(starter == NULL){if(x != 0){std::cout << "Error: unable to find unrolling literal" <<std::endl; exit(180);}}
            if(!starter->isUndef()){
                const auto& insertResult = starter->setStatus(Undef);
                if(insertResult.second){
                    std::cout << "Unrolling ";AuxMapHandler::getInstance().printTuple(starter);
                    TupleFactory::getInstance().removeFromCollisionsList(starter->getId());
                    AuxMapHandler::getInstance().insertUndef(insertResult);
                }
            }
            else{
                std::cout << "Warning: Unrolling literal not assigned yet" <<std::endl;
            }
        }
    private:
        Propagator();
        std::vector<AbstractPropagator*> propagators;
};

#endif