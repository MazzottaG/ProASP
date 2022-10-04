#ifndef Rule_3_Propagator_H
#define Rule_3_Propagator_H
#include <vector>
#include "../datastructures/TupleFactory.h"
#include "../datastructures/AuxiliaryMapSmart.h"
#include "../solver/AuxMapHandler.h"
#include "../utils/ConstantsManager.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
class Rule_3_Propagator: public AbstractGenerator{
    public:
        void propagateLevelZero()override {
            const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_usup_1_()->getValuesVec();
            const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_fsup_1_()->getValuesVec();
            const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_psup_1_()->getValuesVec();
            for(int i = 0; i < tuplesP->size(); i++){
                Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesP->at(i));
                if(tuple != NULL){
                    int X = tuple->at(0);
                    int Z = tuple->at(1);
                    const std::vector<int>* bodyTuplesU = &AuxMapHandler::getInstance().get_uaux_0_0_2_()->getValuesVec({X,Z});
                    const std::vector<int>* bodyTuplesP = &AuxMapHandler::getInstance().get_paux_0_0_2_()->getValuesVec({X,Z});
                    if(bodyTuplesU->size()+bodyTuplesP->size() == 0){
                        std::cout << "Conflict detected at level 0" <<std::endl;
                    }
                    else if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){
                        std::cout << "Propagating last undefined as true" <<std::endl;
                    }
                }
            }
        }
};
#endif
