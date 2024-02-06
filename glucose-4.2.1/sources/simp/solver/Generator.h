#ifndef GENERATOR_H
#define GENERATOR_H
#include "AbstractGenerator.h"
#include <vector>

class Generator{
    public:
        static Generator& getInstance(){
            static Generator instance;
            return instance;
        }
        ~Generator(){
            for(AbstractGenerator* gen : generators){
                if(gen != NULL){
                    delete gen;
                    gen=NULL;
                }
            }
        }
        bool isSolvedByGenerator()const {return solvedByGenerator;}
        std::vector<AggregatePropagator*> collectAggregatePropagators(){
            std::vector<AggregatePropagator*> props;    
            for(AbstractGenerator* gen : generators){
                gen->collectPropagators(props);
            }
            return props;
        }
        void printAggregatePropagators(){

            for(AbstractGenerator* gen : generators){
                gen->printAggrPropagator();
            }

        }
        void generate(Glucose::SimpSolver* s,std::vector<int>& falseAtoms);
        // void generate(Glucose::SimpSolver* s,std::vector<int>& falseAtoms){
        //     std::cout << "Generating ... "<<std::endl;
        //     unsigned size=generators.size()-1;
        //     for(AbstractGenerator* gen : generators) {
        //         //std::cout << "Generator "<<size--<<std::endl;
        //         gen->printName();
        //         gen->generate(s);
        //         std::cout << "Generator consumed"<<std::endl;
        //         gen->propagateTrackedLiteral(s,falseAtoms);
        //     }
        //     std::cout << "Generated --------------"<<std::endl;
        //     reorderAggregateSets();
        //     for(AbstractGenerator* gen : generators) {
        //         gen->remapLiterals();
        //     }
        //     computePossibleSums();
        //     auto& sums = TupleFactory::getInstance().possibleSums();
        //     for(auto pair : sums){
        //         std::cout << "Possible sum for ";
        //         AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));
        //         std::cout << pair.second << std::endl;
        //     }
        //     // debug_botttle_filling();
        // }
        void reorderAggregateSets();
        void computePossibleSums();
        static bool compTuple(const int& l1,const int& l2){
            Tuple* first = TupleFactory::getInstance().getTupleFromInternalID(l1);
            unsigned firstAggrVarIndex = TupleFactory::getInstance().getIndexForAggrSet(first->getPredicateName());
            int w = first->at(firstAggrVarIndex)-TupleFactory::getInstance().getTupleFromInternalID(l2)->at(firstAggrVarIndex);
            return w==0 ? l1 > l2 : w > 0;
        }
        int getRealVar(int var){
            if(remappedId == NULL || !remappedId->count(var)) return var;
            return remappedId->find(var)->second;
        }
        void destroyRemapping(){
            if(remappedId != NULL) delete remappedId;
        }
    private:
        Generator();
        std::vector<AbstractGenerator*> generators;
        std::unordered_map<int,int>* remappedId;
        bool solvedByGenerator;

        void debug_botttle_filling(){
            // std::unordered_set<std::string>
            // for(std::string predicate : {"unfilled","aux_0","bottle","filled","aux_1","aggr_id0","xvalue","aggr_id1","aggr_set0","aggr_id2","yvalue","aggr_set1","aggr_id3","join6","join7"}){
            //     std::cout << "Predicate: "<<predicate<< "     Size: "<<TupleFactory::getInstance().predicateSize(AuxMapHandler::getInstance().getPredicateId(predicate))<<std::endl;
            // }
        }
};

#endif