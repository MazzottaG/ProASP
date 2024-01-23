#ifndef ABSTRACTGENERATOR_H
#define ABSTRACTGENERATOR_H
#include "../SimpSolver.h"
#include "AuxMapHandler.h"
#include "AggregatePropagator.h"
#include <map>

class AbstractGenerator{
    public:
        virtual ~AbstractGenerator(){}
        virtual void generate(Glucose::SimpSolver*)=0;
        virtual void printName()const {}
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
        void collectPropagators(std::vector<AggregatePropagator*>& props){
            for(auto pair: propagators){
                props.push_back(new AggregatePropagator(pair.second));
            }
        }
        void printAggrPropagator() const{

            for(auto pair: propagators){
                std::cout << "Vars:";
                for(int t: pair.first) std::cout << " "<<t;
                std::cout << std::endl;
                pair.second.printCurrentStatus();
            }
        }
        // std::map<std::vector<int>,AggregatePropagator>& getPropagators(){return propagators;}
        // std::map<std::vector<int>,AggregatePropagator>& getPropagatorsClone(){return propagatorsClone;}
        void remapLiterals(){
            for(auto& pair : propagators) pair.second.remapStoredLiteral();
            for(auto& pair : propagatorsClone) pair.second.remapStoredLiteral();
        }
        void printStoredLiterals(){
            for(auto& pair : propagators) pair.second.printStoredLiterals();
            for(auto& pair : propagatorsClone) pair.second.printStoredLiterals();
        }
    protected:
        std::map<std::vector<int>,AggregatePropagator> propagators;
        std::map<std::vector<int>,AggregatePropagator> propagatorsClone;

};
#endif