#ifndef LAZYPROPAGATOR_H
#define LAZYPROPAGATOR_H
#include <vector>
#include "AbstractLazyPropagator.h"

class LazyPropagator{
    private:
        std::vector<AbstractLazyPropagator*> propagators;

    public:
        LazyPropagator();
        void computeFixpoint(Glucose::Solver* s, std::vector<int>& propagated){
            for(int i = 0; i < propagators.size(); ++i){
                propagators[i]->computeFixpoint(s, propagated);
            }
        }
        void explainTrueLiteral(Glucose::Solver* s, Glucose::Lit& lit ){
            for(int i = 0; i < propagators.size(); ++i){
                propagators[i]->explainTrueLiteral(s, lit);
            }
        }
        void explainFalseLiteral(int id, std::unordered_set<int>& tupleReasons){
            for(int i = 0; i < propagators.size(); ++i){
                propagators[i]->explainFalseLiteral(id, tupleReasons);
            }
        }

        void checkLiteralStatus(std::vector<std::pair<int, bool>> lits){
            for(int i = 0; i < propagators.size(); ++i){
                std::cout <<"Calling checkLiteral status for prop " << i <<"\n"; 
                propagators[i]->checkLiteralStatus(lits);
            }
        }
    static int INSERT_AS_UNDEF;
    static int INSERT_AS_TRUE;
    static int REMOVE_FROM_UNDEF;
};
#endif/*LAZYPROPAGATOR_H*/
