#ifndef LAZYPROPAGATOR_H
#define LAZYPROPAGATOR_H
#include <vector>
#include "AbstractLazyPropagator.h"

class LazyPropagator{
    private:
        std::vector<AbstractLazyPropagator*> propagators;

    public:
        LazyPropagator();
        void computeFixpoint(Glucose::Solver* s){
            for(int i = 0; i < propagators.size(); ++i){
                propagators[i]->computeFixpoint(s);
            }
        }
        void explainTrueLiteral(Glucose::Solver* s, Glucose::Lit& lit ){
            for(int i = 0; i < propagators.size(); ++i){
                propagators[i]->explainTrueLiteral(s, lit);
            }
        }
    static int INSERT_AS_UNDEF;
    static int INSERT_AS_TRUE;
    static int REMOVE_FROM_UNDEF;
};
#endif/*LAZYPROPAGATOR_H*/
