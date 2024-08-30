//
// Created by giuseppe mazzotta on 27/08/24.
//

#include "WeakPropagator.h"

Glucose::CRef WeakPropagator::propagateTuple(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& propagations,std::vector<bool>& polarity,TupleLight* starter){
    if(upperBound < 0) return Glucose::CRef_Undef;
    assert(actualSum<upperBound);
    if(actualSum + undefSum >= upperBound){
        for(unsigned i=0; i<literals.size(); i++){
            if(literals[i]->isUndef()){
                if(actualSum + weightForLiteral[i] >= upperBound){

                    int varL = literals[i]->getId();
                    bool negated = true;

                    bool foundConflict = solver->isConflictPropagation(varL, negated);
                    bool assigned = solver->isAssigned(varL);
                    if(!assigned || foundConflict){

                        if(solver->currentLevel() > 0 && starter!=NULL){
                            Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? literals[i]->getReasonLits() : solver->getReasonClause();
                            propagationReason.clear();
                            propagationReason.push(Glucose::mkLit(varL,negated));
                            assert(starter->isTrue());
                            propagationReason.push(Glucose::mkLit(starter->getId(), true));
                            for(unsigned j = 0; j<literals.size(); j++){
                                int varR = literals[j]->getId();
                                if(varR == starter->getId() || starter->isUndef()) continue;
                                if(literals[j]->isTrue()){
                                    propagationReason.push(Glucose::mkLit(literals[j]->getId(),true));
                                }
                            }
                            // std::cout << "      Propagating "<< (negated ? "not ": "");AuxMapHandler::getInstance().printTuple(literals[i]);std::cout << std::endl;
                            // std::cout << "         Reason: ";
                            // for(int index = 0; index < propagationReason.size(); index++){
                            //     Glucose::Lit lit = propagationReason[index];
                            //     std::cout << (sign(lit) ? "not " : "");
                            //     AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(lit)));
                            // }
                            // std::cout << std::endl;
                            Glucose::CRef clause = solver->externalPropagation(varL,negated,this);
                            if(clause != Glucose::CRef_Undef)
                                return clause;
                        }else{
                            if(!assigned){
                                propagations.push(Glucose::mkLit(varL, negated));
                                polarity.push_back(negated);
                            }
                            else if(foundConflict) {
                                Glucose::vec<Glucose::Lit> lits;
                                solver->addClause_(lits);
                                return Glucose::CRef_PropConf;
                            }
                        }
                    }
                }
            }
        }
    }
    return Glucose::CRef_Undef;

}
void WeakPropagator::propagateLevelZero(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits){
    std::cout << "WeakPropagator: Propagating at level 0"<<std::endl;
    Glucose::vec<Glucose::Lit> propagations;
    std::vector<bool> polarity;

    if(actualSum >= upperBound){
        lits.clear();
        solver->addClause_(lits);
        return;
    }

    propagateTuple(solver,propagations,polarity,NULL);
    for(unsigned i = 0; i< propagations.size(); i++){
        bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);
        bool assigned = solver->isAssigned(var(propagations[i]));
        if(!assigned)
            solver->assignFromPropagators(propagations[i]);
        else if(foundConflict){
            lits.clear();
            solver->addClause_(lits);
            return;
        }
    }
    return;
}
Glucose::CRef WeakPropagator::propagate(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits, int literal){
    if(literal < 0) return Glucose::CRef_Undef;

    if(actualSum >= upperBound){
        if(solver->currentLevel()<=0){
            lits.clear();
            solver->addClause_(lits);
            return Glucose::CRef_PropConf;
        }
        assert(false);
    }
    TupleLight* starter = TupleFactory::getInstance().getTupleFromInternalID(literal);
    std::cout << "WeakPropagator: Propagating "<< (literal < 0 ? "not " : "");
    AuxMapHandler::getInstance().printTuple(starter);
    Glucose::vec<Glucose::Lit> propagations;
    std::vector<bool> polarity;
    Glucose::CRef clause = propagateTuple(solver,propagations,polarity,starter);
    if(clause != Glucose::CRef_Undef) return clause;

    for(unsigned i = 0; i< propagations.size(); i++){
        bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);
        bool assigned = solver->isAssigned(var(propagations[i]));
        if(!assigned)
            solver->assignFromPropagators(propagations[i]);
        else if(foundConflict){
            lits.clear();
            solver->addClause_(lits);
            return Glucose::CRef_PropConf;
        }
    }
    return Glucose::CRef_Undef;
}
void WeakPropagator::attachWatched(){
    std::cout << "Weak propagator: My ID is "<<getId()<<std::endl;
    for(auto pair : tupleMapping){
        int id = pair.first >= 0 ? pair.first : -pair.first;
        TupleFactory::getInstance().addWatcher(this->getId(),id,true);
        TupleFactory::getInstance().addWatcher(this->getId(),id,false);
        std::cout << "WeakPropagator: Watching +- ";AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(id));
    }
}

