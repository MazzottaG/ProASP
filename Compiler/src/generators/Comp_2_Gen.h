#ifndef Comp_2_Gen_H
#define Comp_2_Gen_H
#include <vector>
#include "../datastructures/TupleFactory.h"
#include "../datastructures/AuxiliaryMapSmart.h"
#include "../solver/AuxMapHandler.h"
#include "../solver/AbstractGenerator.h"
#include "../utils/ConstantsManager.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
void insertUndefComp_2_Gen(const std::pair<const Tuple *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_e()){
        AuxMapHandler::getInstance().get_ue_()->insert2Vec(*insertResult.first);
        AuxMapHandler::getInstance().get_ue_0_()->insert2Vec(*insertResult.first);
    }
}
void printTuple_Comp_2_Gen(const Tuple* t){
    if(t->isFalse()) std::cout << "not ";
    if(t->isUndef()) std::cout << "undef ";
    std::cout << AuxMapHandler::getInstance().unmapPredicate(t->getPredicateName()) << "(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ",";
        std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));
    }
    std::cout << ")"<<std::endl;
}
class Comp_2_Gen: public AbstractGenerator{
    public:
        void generate()override {
            std::cout << "Generator Comp_2_Gen"<<std::endl;
        }
};
#endif
