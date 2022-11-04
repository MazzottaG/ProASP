#ifndef ABSTRACTGENERATOR_H
#define ABSTRACTGENERATOR_H
#include "../../core/Solver.h"
class AbstractGenerator{
    public:
        virtual void generate(Glucose::Solver*)=0;
};
#endif