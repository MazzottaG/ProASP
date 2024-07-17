#ifndef ABSTRACTLAZYPROPAGATOR_H
#define ABSTRACTLAZYPROPAGATOR_H

#include "../../core/Solver.h"
#include "../datastructures/TupleFactory.h"
#include "PositiveProgramFactory.h"

typedef TupleLight Tuple;
class AbstractLazyPropagator{
    public:
        virtual bool computeFixpointLevelZero(Glucose::Solver* s, Glucose::vec<Glucose::Lit>& lits) = 0;
        virtual bool computeFixpoint(Glucose::Solver* s, std::vector<int>&, Glucose::CRef&, Glucose::vec<Glucose::Lit>& lits) = 0;
        virtual bool propagateToFalse(Glucose::Solver* s, Tuple* tuple, Tuple* original, bool sign, Glucose::vec<Glucose::Lit>& tupleReasons, Glucose::vec<Glucose::Lit>& lits, Glucose::CRef& clause, bool makePropagation) = 0;
        //virtual void checkLiteralStatus(Glucose::Solver* s, std::vector<std::pair<int, bool>>) = 0;
        unsigned getId(){
            return id;
        }
        void setId(unsigned id){
            this->id = id;
        }
        std::vector<int> getWatchedPredicates(){
            return watchedPredicates;
        }
        std::vector<int> getHeadPredicates(){
            return headPredicates;
        }
        
    protected:
        unsigned id;
        //predicates in the head or the body of some rule handled by the component prop.
        std::vector<int> watchedPredicates;
        //predicates in the head of some rule handled by the component propagator (a subset of watchedPredicates)
        std::vector<int> headPredicates;
};

#endif /*ABSTRACTLAZYPROPAGATOR_H*/