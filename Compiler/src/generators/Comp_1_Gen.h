#ifndef Comp_1_Gen_H
#define Comp_1_Gen_H
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
void insertUndefComp_1_Gen(const std::pair<const Tuple *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_sup_0()){
        AuxMapHandler::getInstance().get_usup_0_()->insert2Vec(*insertResult.first);
    }
}
void printTuple_Comp_1_Gen(const Tuple* t){
    if(t->isFalse()) std::cout << "not ";
    if(t->isUndef()) std::cout << "undef ";
    std::cout << AuxMapHandler::getInstance().unmapPredicate(t->getPredicateName()) << "(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ",";
        std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));
    }
    std::cout << ")"<<std::endl;
}
class Comp_1_Gen: public AbstractGenerator{
    public:
        void generate()override {
            {
                const std::vector<int>* tuplesU_0 = &AuxMapHandler::getInstance().get_ue_()->getValuesVec({});
                for(unsigned i=0; i<tuplesU_0->size(); i++){
                    Tuple* tuple_0=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_0->at(i));
                    if(tuple_0!= NULL){
                        int X = tuple_0->at(0);
                        int Y = tuple_0->at(1);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X,Y}, AuxMapHandler::getInstance().get_sup_0());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_1_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_1_Gen(insertResult);
                        }
                    }// closing
                }// closing
            }// closing
            std::cout << "Generator Comp_1_Gen"<<std::endl;
        }
};
#endif
