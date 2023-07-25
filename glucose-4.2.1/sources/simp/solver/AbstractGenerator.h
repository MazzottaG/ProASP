#ifndef ABSTRACTGENERATOR_H
#define ABSTRACTGENERATOR_H
#include "../SimpSolver.h"
#include "AuxMapHandler.h"

class AbstractGenerator{
    public:
        virtual void generate(Glucose::SimpSolver*)=0;
        void propagateTrackedLiteral(Glucose::SimpSolver* solver,std::vector<int>& falseAtoms){
            std::pair<bool,int> trackedLit = TupleFactory::getInstance().popTracked();
            while (trackedLit.first){
                TupleLight* tuple = TupleFactory::getInstance().getTupleFromInternalID(trackedLit.second);
                const auto& insertResult = tuple->setStatus(False);
                if(insertResult.second){
                    falseAtoms.push_back(trackedLit.second);
                    TupleFactory::getInstance().removeFromCollisionsList(tuple->getId());
                    AuxMapHandler::getInstance().insertFalse(insertResult);
                }
                trackedLit = TupleFactory::getInstance().popTracked();
            }
            
        }
};
#endif