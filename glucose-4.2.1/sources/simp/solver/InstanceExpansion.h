#ifndef INSTANCEEXPANSION_H
#define INSTANCEEXPANSION_H
#include "AbstractGenerator.h"
#include <vector>

class InstanceExpansion{
    public:
        static InstanceExpansion& getInstance(){
            static InstanceExpansion instance;
            return instance;
        }
        ~InstanceExpansion(){
            for(AbstractGenerator* gen : generators){
                if(gen != NULL){
                    delete gen;
                    gen=NULL;
                }
            }
        }
        bool isSolvedByGenerator()const {return solvedByGenerator;}
        void generate(Glucose::SimpSolver* s){
            for(AbstractGenerator* gen : generators) {
                gen->generate(s);
            }
        }
    private:
        InstanceExpansion();
        std::vector<AbstractGenerator*> generators;
        bool solvedByGenerator;
};

#endif