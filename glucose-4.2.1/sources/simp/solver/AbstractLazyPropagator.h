#ifndef ABSTRACTLAZYPROPAGATOR_H
#define ABSTRACTLAZYPROPAGATOR_H

#include "../../core/Solver.h"
#include "../datastructures/TupleFactory.h"
#include "PositiveProgramFactory.h"

typedef TupleLight Tuple;
class AbstractLazyPropagator{
    public:
        virtual void computeFixpoint(Glucose::Solver* s) = 0;
        virtual void explainTrueLiteral(Glucose::Solver* s, Glucose::Lit& lit){
            int tupleId = Glucose::toInt(lit);
            Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tupleId);
            Glucose::vec<Glucose::Lit>& propagationReason =  !s->isAssigned(tupleId) ? tuple->getReasonLits() : s->getReasonClause();
            propagationReason.clear();
            propagationReason.push(Glucose::mkLit(tupleId, true));
            std::vector<int> toExplain;
            do{
                Glucose::vec<Glucose::Lit>&  tupleReason = tuple->getReasonLits();
                for(unsigned i = 0 ; i < tupleReason.size(); ++i){
                    int var = Glucose::toInt(tupleReason[i]);
                    tupleId = std::abs(var);
                    propagationReason.push(Glucose::mkLit(tupleId,  var > 0));
                    toExplain.push_back(tupleId);
                }
            }while(!toExplain.empty());
        }
        virtual void checkLiteralStatus(std::vector<std::pair<int, bool>>) = 0;
};

#endif /*ABSTRACTLAZYPROPAGATOR_H*/