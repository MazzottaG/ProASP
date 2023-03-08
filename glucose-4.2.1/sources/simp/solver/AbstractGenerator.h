#ifndef ABSTRACTGENERATOR_H
#define ABSTRACTGENERATOR_H
#include "../SimpSolver.h"
class AbstractGenerator{
    public:
        virtual void generate(Glucose::SimpSolver*)=0;
};
#endif