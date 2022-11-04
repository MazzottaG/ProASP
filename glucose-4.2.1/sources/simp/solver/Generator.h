#ifndef GENERATOR_H
#define GENERATOR_H
#include "AbstractGenerator.h"
#include <vector>

class Generator{
    public:
        static Generator& getInstance(){
            static Generator instance;
            return instance;
        }
        ~Generator(){
            for(AbstractGenerator* gen : generators){
                delete gen;
            }

        }
        bool isSolvedByGenerator()const {return solvedByGenerator;}
        void generate(Glucose::Solver* s){
            for(AbstractGenerator* gen : generators) 
                gen->generate(s);
        }
    private:
        Generator();
        std::vector<AbstractGenerator*> generators;
        bool solvedByGenerator;
};

#endif