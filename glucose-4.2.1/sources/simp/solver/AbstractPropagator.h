#ifndef ABSTRACT_PROPAGATOR_H
#define ABSTRACT_PROPAGATOR_H
#include "../../core/Solver.h"

class AbstractPropagator{
    public:
        virtual ~AbstractPropagator(){}
        virtual void printName()const {}
        virtual void propagateLevelZero(Glucose::Solver*,Glucose::vec<Glucose::Lit>&) = 0;
        virtual Glucose::CRef propagate(Glucose::Solver*,Glucose::vec<Glucose::Lit>&,int) = 0;
        virtual void attachWatched() = 0;
        virtual void init()const{}
        virtual void notifyTrue(int){}
        virtual void notifyUndef(int){}
        virtual void printStoredLiterals(){}
        virtual void remapStoredLiteral(){}

        unsigned getId()const {return id;}
        void setId(unsigned prop){
            this->id = prop;
        }
    private:
        unsigned id;
    
};
#endif