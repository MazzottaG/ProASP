#ifndef INSTANCEEXPANSIONPOSCYCLE_H
#define INSTANCEEXPANSIONPOSCYCLE_H
#include "AbstractGenerator.h"
#include <vector>

class InstanceExpansionPosCycle{
    public:
        static InstanceExpansionPosCycle& getInstance(){
            static InstanceExpansionPosCycle instance;
            return instance;
        }
        ~InstanceExpansionPosCycle(){
            for(AbstractGenerator* gen : generators){
                if(gen != NULL){
                    delete gen;
                    gen=NULL;
                }
            }
        }
        void generate(Glucose::SimpSolver* s){
            for(AbstractGenerator* gen : generators) {
                gen->generate(s);
            }
        }
    private:
        InstanceExpansionPosCycle();
        std::vector<AbstractGenerator*> generators;
        bool solvedByGenerator;
};

#endif /*INSTANCEEXPANSIONPOSCYCLE*/