#ifndef Rule_1_Propagator_H
#define Rule_1_Propagator_H
#include <vector>
#include "../datastructures/TupleFactory.h"
#include "../datastructures/AuxiliaryMapSmart.h"
#include "../solver/AuxMapHandler.h"
#include "../utils/ConstantsManager.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
class Rule_1_Propagator: public AbstractGenerator{
    public:
        void propagateLevelZero()override {
            const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_usup_0_()->getValuesVec();
            const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_fsup_0_()->getValuesVec();
            const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_psup_0_()->getValuesVec();
            for(int i = 0; i < tuplesP->size(); i++){
                Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesP->at(i));
                if(tuple != NULL){
                    int X = tuple->at(0);
                    int Y = tuple->at(1);
                    Tuple* boundBody=TupleFactory::getInstance().find({X,Y}, AuxMapHandler::getInstance().get_e());
                    if(boundBody != NULL && boundBody->isFalse()){
                        std::cout << "Conflict detected at level 0" <<std::endl;
                    }
                    else if(boundBody != NULL && boundBody->isUndef()){
                        std::cout << "Propagate body atom as true"; <<std::endl;
                    }
                }
            }
        }
};
#endif
