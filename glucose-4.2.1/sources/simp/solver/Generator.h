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
                delete gen;
            }

        }
        bool isSolvedByGenerator()const {return solvedByGenerator;}
        void generate(Glucose::SimpSolver* s,std::vector<int>& falseAtoms){
            std::cout << "Generating ... "<<std::endl;
            unsigned size=generators.size()-1;
            for(AbstractGenerator* gen : generators) {
                std::cout << "Generator "<<size--<<std::endl;

                gen->generate(s);
                gen->propagateTrackedLiteral(s,falseAtoms);
            }
            std::cout << "Reordering aggregate sets ... "<<std::endl;
            reorderAggregateSets();
            computePossibleSums();
            auto& sums = TupleFactory::getInstance().possibleSums();
            for(auto pair : sums){
                std::cout << "Possible sum for ";
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));
                std::cout << pair.second << std::endl;
            }
        }
        void reorderAggregateSets();
        void computePossibleSums();
        static bool compTuple(const int& l1,const int& l2){
            Tuple* first = TupleFactory::getInstance().getTupleFromInternalID(l1);
            unsigned firstAggrVarIndex = TupleFactory::getInstance().getIndexForAggrSet(first->getPredicateName());
            int w = first->at(firstAggrVarIndex)-TupleFactory::getInstance().getTupleFromInternalID(l2)->at(firstAggrVarIndex);
            return w==0 ? l1 > l2 : w > 0;
        }
    private:
        Generator();
        std::vector<AbstractGenerator*> generators;
        bool solvedByGenerator;
};

#endif