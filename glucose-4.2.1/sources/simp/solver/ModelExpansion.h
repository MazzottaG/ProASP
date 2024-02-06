#ifndef MODELEXPANSION_H
#define MODELEXPANSION_H
#include "AbstractGenerator.h"
#include <vector>

class ModelExpansion{
    public:
        static ModelExpansion& getInstance(){
            static ModelExpansion instance;
            return instance;
        }
        ~ModelExpansion(){
            for(AbstractGenerator* gen : generators){
                if(gen != NULL)
                delete gen;
            }

        }
        bool isSolvedByGenerator()const {return solvedByGenerator;}
        void generate(Glucose::SimpSolver* s){
            for(AbstractGenerator* gen : generators) {
                gen->generate(s);
            }
        }
    private:
        ModelExpansion();
        std::vector<AbstractGenerator*> generators;
        bool solvedByGenerator;
};

#endif