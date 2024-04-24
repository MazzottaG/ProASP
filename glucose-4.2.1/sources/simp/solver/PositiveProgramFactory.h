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
        void updateCheckedLiteralStatus(){
            for(int tupleID : checkedTuples){
                //check if reason is still all true in factory
                //if not, remove literal from checked
                //Expected usage is: LazyPropagator.computeFixpoint(litsChanged),
                //updateCheckedLiteralStatus()
                //
                bool spFailed = false;
                const Glucose::vec<Glucose::Lit>& reason = TupleFactory::getInstance().getTupleFromInternalID(tupleID)->getReason();
                for(unsigned i = 0; i < reason.size(); ++i){
                    int id = TupleFactory::getInstance().glucoseReasonToTupleId(reason[i]);
                    if(!Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isTrue()) spFailed = true;
                    else if(Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isFalse()) spFailed = true;
                    if(spFailed){
                        checkedTuples.erase(tupleID);
                        break;
                    }
                }
            }
        }

        void addCheckedTuple(int id){
            checkedTuples.insert(id);
        }
};
#endif /*POSITIVEPROGRAMFACTORY_H*/
