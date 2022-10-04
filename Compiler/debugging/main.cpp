#ifndef AUXMAPHANDLER_H
#define AUXMAPHANDLER_H
#include <vector>
#include "../src/datastructures/TupleLight.h"
#include "../src/datastructures/AuxiliaryMapSmart.h"
#include "../src/datastructures/TupleFactory.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
class AuxMapHandler{
    public:
        static AuxMap<0> uaux_0_;
        static AuxMap<0> usup_0_;
        static AuxMap<0> usup_1_;
        static AuxMap<0> ur_;
        static AuxMap<0> uarc_;
        static AuxMap<32> uarc_0_;
};
AuxMap<0> AuxMapHandler::uaux_0_=AuxMap<0>({});
AuxMap<0> AuxMapHandler::usup_0_=AuxMap<0>({});
AuxMap<0> AuxMapHandler::usup_1_=AuxMap<0>({});
AuxMap<0> AuxMapHandler::ur_=AuxMap<0>({});
AuxMap<0> AuxMapHandler::uarc_=AuxMap<0>({});
AuxMap<32> AuxMapHandler::uarc_0_=AuxMap<32>({0});
#endif
void printTuple(Tuple* t){

    if(t->isFalse()) std::cout << "not ";
    if(t->isUndef()) std::cout << "undef ";
    std::cout << "arc(";
    for(int i=0;i<t->size();i++){
        if(i>0) std::cout << ",";
        std::cout << t->at(i);
    }
    std::cout << ")"<<std::endl;

}
int main(){
    TupleFactory factory;
    factory.addPredicate();
    Tuple* t = factory.addNewInternalTuple({1,1},0);
    AuxMapHandler::uarc_.insert2Set(*t);
    AuxMapHandler::uarc_0_.insert2Set(*t);
    std::vector<int> tuples = AuxMapHandler::uarc_.getValuesVec({});
    for(int id :tuples){
        printTuple(factory.getTupleFromInternalID(id));
    }   
}