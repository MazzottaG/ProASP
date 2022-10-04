#ifndef AUXMAPHANDLER_H
#define AUXMAPHANDLER_H
#include <vector>
#include "../datastructures/TupleLight.h"
#include "../datastructures/AuxiliaryMapSmart.h"
typedef TupleLight Tuple;
template<size_t S>
using AuxMap = AuxiliaryMapSmart<S> ;
typedef std::vector<const Tuple* > Tuples;
class AuxMapHandler{
    public:
        static AuxMapHandler& getInstance(){
            static AuxMapHandler instance;
            return instance;
        }
        AuxMap<0>* get_usup_0_(){return &usup_0_;}
        AuxMap<0>* get_usup_1_(){return &usup_1_;}
        AuxMap<0>* get_ur_(){return &ur_;}
        AuxMap<32>* get_ur_1_(){return &ur_1_;}
        AuxMap<0>* get_uaux_0_(){return &uaux_0_;}
        AuxMap<64>* get_uaux_0_0_1_(){return &uaux_0_0_1_;}
        AuxMap<64>* get_uaux_0_0_2_(){return &uaux_0_0_2_;}
        AuxMap<64>* get_uaux_0_1_2_(){return &uaux_0_1_2_;}
        AuxMap<0>* get_ue_(){return &ue_;}
        AuxMap<32>* get_ue_0_(){return &ue_0_;}
        int get_r()const { return _r;}
        int get_e()const { return _e;}
        int get_sup_0()const { return _sup_0;}
        int get_sup_1()const { return _sup_1;}
        int get_aux_0()const { return _aux_0;}
        std::string unmapPredicate(int predicateId)const {return predicateNames[predicateId];}
        unsigned predicateCount()const {return predicateNames.size();}
    private:
        AuxMapHandler(): usup_0_({}), usup_1_({}), ur_({}), ur_1_({1}), uaux_0_({}), uaux_0_0_1_({0,1}), uaux_0_0_2_({0,2}), uaux_0_1_2_({1,2}), ue_({}), ue_0_({0}), predicateNames({"r","e","sup_0","sup_1","aux_0"}){}
        AuxMap<0> usup_0_;
        AuxMap<0> usup_1_;
        AuxMap<0> ur_;
        AuxMap<32> ur_1_;
        AuxMap<0> uaux_0_;
        AuxMap<64> uaux_0_0_1_;
        AuxMap<64> uaux_0_0_2_;
        AuxMap<64> uaux_0_1_2_;
        AuxMap<0> ue_;
        AuxMap<32> ue_0_;
        int _r = 0;
        int _e = 1;
        int _sup_0 = 2;
        int _sup_1 = 3;
        int _aux_0 = 4;
        std::vector<std::string> predicateNames;
};
#endif
