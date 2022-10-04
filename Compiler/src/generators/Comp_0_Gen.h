#ifndef Comp_0_Gen_H
#define Comp_0_Gen_H
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
void insertUndefComp_0_Gen(const std::pair<const Tuple *, bool>& insertResult){
    if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_aux_0()){
        AuxMapHandler::getInstance().get_uaux_0_()->insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_r()){
        AuxMapHandler::getInstance().get_ur_()->insert2Vec(*insertResult.first);
    }
    else if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_sup_1()){
        AuxMapHandler::getInstance().get_usup_1_()->insert2Vec(*insertResult.first);
    }
}
void printTuple_Comp_0_Gen(const Tuple* t){
    if(t->isFalse()) std::cout << "not ";
    if(t->isUndef()) std::cout << "undef ";
    std::cout << AuxMapHandler::getInstance().unmapPredicate(t->getPredicateName()) << "(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ",";
        std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));
    }
    std::cout << ")"<<std::endl;
}
class Comp_0_Gen: public AbstractGenerator{
    public:
        void generate()override {
            std::vector<int> stack;
            {
                const std::vector<int>* tuplesU_0 = &AuxMapHandler::getInstance().get_ur_()->getValuesVec({});
                for(unsigned i=0; i<tuplesU_0->size(); i++){
                    Tuple* tuple_0=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_0->at(i));
                    if(tuple_0!= NULL){
                        int X = tuple_0->at(0);
                        int Y = tuple_0->at(1);
                        const std::vector<int>* tuplesU_1 = &AuxMapHandler::getInstance().get_ue_0_()->getValuesVec({Y});
                        for(unsigned i=0; i<tuplesU_1->size(); i++){
                            Tuple* tuple_1=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_1->at(i));
                            if(tuple_1!= NULL){
                                int Z = tuple_1->at(1);
                                Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X,Y,Z}, AuxMapHandler::getInstance().get_aux_0());
                                const auto& insertResult = head_0->setStatus(Undef);
                                if(insertResult.second){
                                    std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                                    TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                                    insertUndefComp_0_Gen(insertResult);
                                    stack.push_back(head_0->getId());
                                }
                            }// closing
                        }// closing
                    }// closing
                }// closing
            }// closing
            {
                const std::vector<int>* tuplesU_0 = &AuxMapHandler::getInstance().get_usup_0_()->getValuesVec({});
                for(unsigned i=0; i<tuplesU_0->size(); i++){
                    Tuple* tuple_0=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_0->at(i));
                    if(tuple_0!= NULL){
                        int X_0 = tuple_0->at(0);
                        int X_1 = tuple_0->at(1);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X_0,X_1}, AuxMapHandler::getInstance().get_r());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_0_Gen(insertResult);
                            stack.push_back(head_0->getId());
                        }
                    }// closing
                }// closing
            }// closing
            {
                const std::vector<int>* tuplesU_0 = &AuxMapHandler::getInstance().get_usup_1_()->getValuesVec({});
                for(unsigned i=0; i<tuplesU_0->size(); i++){
                    Tuple* tuple_0=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_0->at(i));
                    if(tuple_0!= NULL){
                        int X_0 = tuple_0->at(0);
                        int X_1 = tuple_0->at(1);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X_0,X_1}, AuxMapHandler::getInstance().get_r());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_0_Gen(insertResult);
                            stack.push_back(head_0->getId());
                        }
                    }// closing
                }// closing
            }// closing
            {
                const std::vector<int>* tuplesU_0 = &AuxMapHandler::getInstance().get_uaux_0_()->getValuesVec({});
                for(unsigned i=0; i<tuplesU_0->size(); i++){
                    Tuple* tuple_0=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_0->at(i));
                    if(tuple_0!= NULL){
                        int X = tuple_0->at(0);
                        int Y = tuple_0->at(1);
                        int Z = tuple_0->at(2);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X,Z}, AuxMapHandler::getInstance().get_sup_1());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_0_Gen(insertResult);
                            stack.push_back(head_0->getId());
                        }
                    }// closing
                }// closing
            }// closing
            while(!stack.empty()){
                Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID(stack.back());
                stack.pop_back();
                if(starter != NULL){
                    if(starter->getPredicateName() == AuxMapHandler::getInstance().get_r()){
                        int X = starter->at(0);
                        int Y = starter->at(1);
                        const std::vector<int>* tuplesU_1 = &AuxMapHandler::getInstance().get_ue_0_()->getValuesVec({Y});
                        for(unsigned i=0; i<tuplesU_1->size(); i++){
                            Tuple* tuple_1=TupleFactory::getInstance().getTupleFromInternalID(tuplesU_1->at(i));
                            if(tuple_1!= NULL){
                                int Z = tuple_1->at(1);
                                Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X,Y,Z}, AuxMapHandler::getInstance().get_aux_0());
                                const auto& insertResult = head_0->setStatus(Undef);
                                if(insertResult.second){
                                    std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                                    TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                                    insertUndefComp_0_Gen(insertResult);
                                    stack.push_back(head_0->getId());
                                }
                            }// closing
                        }// closing
                    }// closing
                    if(starter->getPredicateName() == AuxMapHandler::getInstance().get_sup_1()){
                        int X_0 = starter->at(0);
                        int X_1 = starter->at(1);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X_0,X_1}, AuxMapHandler::getInstance().get_r());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_0_Gen(insertResult);
                            stack.push_back(head_0->getId());
                        }
                    }// closing
                    if(starter->getPredicateName() == AuxMapHandler::getInstance().get_aux_0()){
                        int X = starter->at(0);
                        int Y = starter->at(1);
                        int Z = starter->at(2);
                        Tuple* head_0=TupleFactory::getInstance().addNewInternalTuple({X,Z}, AuxMapHandler::getInstance().get_sup_1());
                        const auto& insertResult = head_0->setStatus(Undef);
                        if(insertResult.second){
                            std::cout << "Added tuple ";printTuple_Comp_0_Gen(head_0);
                            TupleFactory::getInstance().removeFromCollisionsList(head_0->getId());
                            insertUndefComp_0_Gen(insertResult);
                            stack.push_back(head_0->getId());
                        }
                    }// closing
                } else std::cout << "Warning null tuple in generation stack"<<std::endl;
            }
            std::cout << "Generator Comp_0_Gen"<<std::endl;
        }
};
#endif
