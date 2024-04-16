#ifndef POSITIVEPROGRAMFACTORY_H
#define POSITIVEPROGRAMFACTORY_H
#include <unordered_set>

class PositiveProgramFactory{
    private:
        static PositiveProgramFactory instance;
        PositiveProgramFactory(){}
        int lastTupleFromGen;
        std::unordered_set<int> checkedTuples;

    public:
        static PositiveProgramFactory& getInstance(){
            static PositiveProgramFactory instance;
            return instance;
        }

        void setLastTupleFromGen(int lastTupleID){
            lastTupleFromGen = lastTupleID;
        }

        bool isTupleFromGen(int id){
            return id <= lastTupleFromGen;
        }
        void updateChecedLiteralStatus(){
            for(int tupleID : checkedTuples){
                //check if reason is still all true in factory
                //if not, remove literal from checked
                //then call lazyProp.computeFixpoint with the bunch of literals whose
                //truth value has been changed since last call of lazyProp
            }
        }

};
#endif /*POSITIVEPROGRAMFACTORY_H*/
