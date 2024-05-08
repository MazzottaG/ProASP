#ifndef ABSTRACTLAZYPROPAGATOR_H
#define ABSTRACTLAZYPROPAGATOR_H

#include "../../core/Solver.h"
#include "../datastructures/TupleFactory.h"
#include "PositiveProgramFactory.h"

typedef TupleLight Tuple;
class AbstractLazyPropagator{
    public:
        virtual void computeFixpoint(Glucose::Solver* s, std::vector<int>&) = 0;
        virtual void explainTrueLiteral(Glucose::Solver* s, Glucose::Lit& lit){
            int tupleId = TupleFactory::getInstance().glucoseReasonToTupleId(lit);
            Tuple* t = TupleFactory::getInstance().getTupleFromInternalID(tupleId);
            Glucose::vec<Glucose::Lit> propagationReason;
            std::vector<int> toExplain;
            toExplain.push_back(tupleId);
            while(!toExplain.empty()){
                Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(toExplain.back());
                toExplain.pop_back();
                Glucose::vec<Glucose::Lit>&  tupleReason = tuple->getReasonLits();
                for(unsigned i = 0; i < tupleReason.size(); ++i){
                    bool sign = Glucose::sign(tupleReason[i]);
                    //use var - change method
                    tupleId = TupleFactory::getInstance().glucoseReasonToTupleId(tupleReason[i]);
                    if(PositiveProgramFactory::getInstance().isTupleFromGen(tupleId))
                        propagationReason.push(Glucose::mkLit(tupleId,  sign));
                    else
                        toExplain.push_back(tupleId);
                }
            }

            std::cout <<"Reason: " ;
            for(unsigned i = 0; i < propagationReason.size(); ++i){
                //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(TupleFactory::getInstance().glucoseReasonToTupleId(propagationReason[i])));
                std::cout << propagationReason[i].x << " ";
            }
            std::cout<< std::endl;
        }
        virtual void explainFalseLiteral(int, std::unordered_set<int>&) = 0;
        virtual void checkLiteralStatus(std::vector<std::pair<int, bool>>) = 0;
};

#endif /*ABSTRACTLAZYPROPAGATOR_H*/