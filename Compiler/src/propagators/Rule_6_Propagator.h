#ifndef Rule_6_Propagator_H
#define Rule_6_Propagator_H
#include <vector>
#include "../datastructures/TupleFactory.h"
#include "../datastructures/AuxiliaryMapSmart.h"
#include "../solver/AuxMapHandler.h"
#include "../utils/ConstantsManager.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
class Rule_6_Propagator: public AbstractGenerator{
    public:
        void propagateLevelZero()override {
        }
};
#endif
