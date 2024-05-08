#ifndef POSITIVEPROGRAMFACTORY_H
#define POSITIVEPROGRAMFACTORY_H
#include <unordered_set>

class PositiveProgramFactory{
    private:
        static PositiveProgramFactory instance;
        PositiveProgramFactory(){}
        int lastTupleFromGen;
        int assignedLiterals;
        std::unordered_set<int> checkedTuples;
        std::unordered_map<int, std::unordered_set<int>> supportedTuples;

    public:
        static PositiveProgramFactory& getInstance(){
            static PositiveProgramFactory instance;
            return instance;
        }

        void setLastTupleFromGen(int lastTupleID){
            lastTupleFromGen = lastTupleID;
        }

        void setAssignedTuplesFromGen(int n){
            assignedLiterals = n;
        }
        
        bool isTupleFromGen(int id){
            return id <= lastTupleFromGen;
        }

        //does a complete iteration over checked
        // void updateCheckedLiteralStatus(){
        //     for(int tupleID : checkedTuples){
        //         //check if reason is still all true in factory
        //         //if not, remove literal from checked
        //         //Expected usage is: LazyPropagator.computeFixpoint(litsChanged),
        //         //updateCheckedLiteralStatus()
        //         //
        //         bool spFailed = false;
        //         const Glucose::vec<Glucose::Lit>& reason = TupleFactory::getInstance().getTupleFromInternalID(tupleID)->getReason();
        //         for(unsigned i = 0; i < reason.size(); ++i){
        //             int id = TupleFactory::getInstance().glucoseReasonToTupleId(reason[i]);
        //             if(!Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isTrue()) spFailed = true;
        //             else if(Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isFalse()) spFailed = true;
        //             if(spFailed){
        //                 checkedTuples.erase(tupleID);
        //                 break;
        //             }
        //         }
        //     }
        // }

        void addSupported(int support, int supported){
            if(!supportedTuples.count(support))
                supportedTuples.emplace(support, std::unordered_set<int>());
            supportedTuples[support].insert(supported);
        }

        // tuples is a vector of interface tuples that has been reset to undef
        // from the solver due to a conflict and a subsequent rollback
        void resetCheckedStatusDueToUndef(std::vector<int>& tuples){
            //TODO check if list is really needed, maybe  a vector is still ok?
            std::list<int> toCheckTuples;
            for(unsigned i = 0; i < tuples.size(); ++i){
                toCheckTuples.push_back(tuples[i]);
                assert(isTupleFromGen(tuples[i]));
            }
            //set all tuples supported by tuple as non checked
            while(!toCheckTuples.empty()){
                int tuple = toCheckTuples.back();
                toCheckTuples.pop_back();
                if(supportedTuples.count(tuple)){
                    for(auto t : supportedTuples[tuple]){
                        checkedTuples.erase(t);
                        toCheckTuples.push_front(t);
                    }
                    //clear supported for undef(or potentially undef)
                    supportedTuples[tuple].clear();
                    //clear tuple reason
                    TupleFactory::getInstance().getTupleFromInternalID(tuple)->getReasonLits().clear();
                }

            }
        }

        void addCheckedTuple(int id){
            checkedTuples.insert(id);
        }
        
        bool isTupleChecked(int id){
            return checkedTuples.count(id);
        }

        void unrollLiteral(){
            assignedLiterals--;
        }
        void assignLiteral(){
            assignedLiterals++;
        }

        bool isInterfaceAllAssinged(){
            return assignedLiterals == lastTupleFromGen;
        }
        
};
#endif /*POSITIVEPROGRAMFACTORY_H*/
