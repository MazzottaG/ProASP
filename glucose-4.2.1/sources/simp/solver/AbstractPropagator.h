#ifndef ABSTRACT_PROPAGATOR_H
#define ABSTRACT_PROPAGATOR_H
#include "../../core/Solver.h"

class AbstractPropagator{
    public:
        virtual void propagateLevelZero(Glucose::Solver*,Glucose::vec<Glucose::Lit>&) = 0;
        virtual Glucose::CRef propagate(Glucose::Solver*,Glucose::vec<Glucose::Lit>&,int) = 0;

};
#endif