#ifndef GENERATOR_H
#define GENERATOR_H
#include "AbstractGenerator.h"
#include <vector>

class Generator{
    public:
        Generator();
        ~Generator(){
            for(AbstractGenerator* gen : generators){
                delete gen;
            }

        }
        void generate(){
            for(AbstractGenerator* gen : generators) 
                gen->generate();
        }
    private:
        std::vector<AbstractGenerator*> generators;
};

#endif