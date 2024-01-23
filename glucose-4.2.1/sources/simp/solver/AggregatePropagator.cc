#include "AggregatePropagator.h"

std::pair<int,bool> AggregatePropagator::isAggIdStarter(int literal){
    
    auto aggIdPos = aggIdMapping.find(literal >= 0 ? literal : -literal);
    if(aggIdPos != aggIdMapping.end()){
        return std::make_pair(literal >= 0 ? aggIdPos->second : -aggIdPos->second, true);
    }
    return std::make_pair(0,false);
}
std::pair<int,bool> AggregatePropagator::isAggSetStarter(int literal){
    
    auto aggSetPos = aggSetMapping.find(literal >= 0 ? literal : -literal);
    if(aggSetPos != aggSetMapping.end()){
        return std::make_pair(literal >= 0 ? aggSetPos->second : -aggSetPos->second, true);
    }
    return std::make_pair(0,false);
}
Glucose::CRef AggregatePropagator::propagateAggregateAsFalse(Glucose::Solver* solver,std::vector<Glucose::Lit>&,int boundIndex,TupleLight* starter,bool startedFromAggId,bool computeReason){

    assert(ids[boundIndex]->isFalse());
    
    for(unsigned i=0; i<literals.size(); i++){
        if(literals[i]->isUndef()){
            if(currentSum + weights[i] >= bounds[boundIndex]){

                int varL = literals[i]->getId();
                bool negated = aggSetNegated ? false : true;

                bool foundConflict = solver->isConflictPropagation(varL, negated);
                bool assigned = solver->isAssigned(varL);
                if(!assigned || foundConflict){

                    if(solver->currentLevel() > 0 && computeReason){
                        Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? literals[i]->getReasonLits() : solver->getReasonClause();
                        propagationReason.clear();
                        propagationReason.push(Glucose::mkLit(varL,negated));
                        if(startedFromAggId){
                            propagationReason.push(Glucose::mkLit(ids[boundIndex]->getId(),false));
                        }else{
                            assert((aggSetNegated && starter->isFalse()) || ((!aggSetNegated && starter->isTrue())));
                            propagationReason.push(Glucose::mkLit(starter->getId(), aggSetNegated ? false : true));
                            propagationReason.push(Glucose::mkLit(ids[boundIndex]->getId(),false));
                        }
                        for(unsigned j = 0; j<literals.size(); j++){
                            int varR = literals[j]->getId();
                            if(varR == starter->getId() || starter->isUndef()) continue;
                            
                            if(aggSetNegated){
                                if(literals[j]->isFalse()){
                                    propagationReason.push(Glucose::mkLit(literals[j]->getId(),false));
                                }    
                            }else{
                                if(literals[j]->isTrue()){
                                    propagationReason.push(Glucose::mkLit(literals[j]->getId(),true));
                                }
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
                        if(!assigned) solver->assignFromPropagators(Glucose::mkLit(varL, negated));
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
    return Glucose::CRef_Undef;
}
Glucose::CRef AggregatePropagator::propagateAggregateAsTrue(Glucose::Solver* solver,std::vector<Glucose::Lit>&,int boundIndex,TupleLight* starter,bool startedFromAggId,bool computeReason){

    assert(ids[boundIndex]->isTrue());
    for(unsigned i=0; i<literals.size(); i++){
        if(literals[i]->isUndef()){
            if(currentSum + maxPossibleSum - weights[i] < bounds[boundIndex]){
                int varL = literals[i]->getId();
                bool negated = aggSetNegated;

                bool foundConflict = solver->isConflictPropagation(varL, negated);
                bool assigned = solver->isAssigned(varL);
                
                if(!assigned || foundConflict){
                    
                    if(solver->currentLevel() > 0 && computeReason){
                        Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? literals[i]->getReasonLits() : solver->getReasonClause();
                        propagationReason.clear();
                        propagationReason.push(Glucose::mkLit(varL,negated));
                        if(startedFromAggId){
                            propagationReason.push(Glucose::mkLit(ids[boundIndex]->getId(),true));
                        }else{
                            assert((aggSetNegated && starter->isTrue()) || ((!aggSetNegated && starter->isFalse())));
                            propagationReason.push(Glucose::mkLit(starter->getId(),aggSetNegated ? true : false));
                            propagationReason.push(Glucose::mkLit(ids[boundIndex]->getId(),true));
                        }
                        for(unsigned j = 0; j<literals.size(); j++){
                            int varR = literals[j]->getId();
                            if(varR == starter->getId() || starter->isUndef()) continue;
                            
                            if(aggSetNegated){
                                if(literals[j]->isTrue()){
                                    propagationReason.push(Glucose::mkLit(literals[j]->getId(),true));
                                }    
                            }else{
                                if(literals[j]->isFalse()){
                                    propagationReason.push(Glucose::mkLit(literals[j]->getId(),false));
                                }
                            }
                        }
                        // if(foundConflict) std::cout << "conflictual literal in aggregates"<<std::endl;
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
                        if(!assigned) solver->assignFromPropagators(Glucose::mkLit(varL, negated));
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
    return Glucose::CRef_Undef;

}

void AggregatePropagator::propagateLevelZero(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits){
    std::vector<Glucose::Lit> propagations;
    std::vector<bool> polarity;
    for(int i=0; i<bounds.size(); i++){
        // std::cout << "Considering bound ";
        // AuxMapHandler::getInstance().printTuple(ids[i]);
        // std::cout << std::endl;
        if((ids[i]->isTrue() && currentSum+maxPossibleSum < bounds[i]) || (ids[i]->isFalse() && currentSum >= bounds[i])){
            Glucose::vec<Glucose::Lit> lits;
            solver->addClause_(lits);
            return;
        } else if(ids[i]->isTrue() && currentSum<bounds[i]){
            // std::cout << "   GroundAggregatePropagator: Evaluating True Bound ";AuxMapHandler::getInstance().printTuple(ids[i]);std::cout<< " with guard "<<bounds[i]<<std::endl;
            // std::cout << "   True Bound"<<std::endl;
            propagateAggregateAsTrue(solver,propagations,i,NULL,false,false);
        }else if(ids[i]->isFalse() && currentSum+maxPossibleSum >= bounds[i]){
            // std::cout << "   GroundAggregatePropagator: Evaluating False Bound ";AuxMapHandler::getInstance().printTuple(ids[i]);std::cout<< " with guard "<<bounds[i]<<std::endl;
            // std::cout << "   False Bound"<<std::endl;
            propagateAggregateAsFalse(solver,propagations,i,NULL,false,false);
        }else if(ids[i]->isUndef()){
            // std::cout << "   GroundAggregatePropagator: Evaluating Undef Bound ";AuxMapHandler::getInstance().printTuple(ids[i]);std::cout<< " with guard "<<bounds[i]<<std::endl;
            // std::cout << "   Undef Bound"<<std::endl;
            if(currentSum>=bounds[i]){
                propagations.push_back(Glucose::mkLit(ids[i]->getId(),false));
                polarity.push_back(false);
            }else if(currentSum + maxPossibleSum < bounds[i]){
                propagations.push_back(Glucose::mkLit(ids[i]->getId(),true));
                polarity.push_back(true);
            }
        }
    }
    for(unsigned i = 0; i< propagations.size(); i++){
        
        // std::cout << "      Propagating Level 0 " << sign(propagations[i]) ? "not " : "";
        // AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagations[i])));
        // std::cout << std::endl;

        bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);
        bool assigned = solver->isAssigned(var(propagations[i]));
        if(!assigned) solver->assignFromPropagators(Glucose::mkLit(var(propagations[i]), polarity[i]));
        else if(foundConflict) {
            Glucose::vec<Glucose::Lit> lits;
            solver->addClause_(lits);
            return;
        }
    }
}
Glucose::CRef AggregatePropagator::propagate(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits,int literal){
    // std::cout << "Propagating ..."<<std::endl;
    TupleLight* starter = TupleFactory::getInstance().getTupleFromInternalID(literal >= 0 ? literal : -literal);
    std::vector<Glucose::Lit> propagations;
    std::vector<bool> polarity;
    auto aggIdStarter = isAggIdStarter(literal);
    if(aggIdStarter.second){
        
        // std::cout << "Propagation starting from aggId"<<std::endl;
        // std::cout << "    Received literal: ";AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(literal >= 0 ? literal : -literal));
        // std::cout << "    Remapped literal: ";AuxMapHandler::getInstance().printTuple(ids[aggIdStarter.first >=0 ? aggIdStarter.first : -aggIdStarter.first]);
        // std::cout << "    Associated bound: "<<bounds[aggIdStarter.first >=0 ? aggIdStarter.first : -aggIdStarter.first]<<std::endl;
        
        if(literal < 0){
            Glucose::CRef c = propagateAggregateAsFalse(solver,propagations,aggIdStarter.first >=0 ? aggIdStarter.first : -aggIdStarter.first,starter,true);
            if(c != Glucose::CRef_Undef) return c;
        }else{
            Glucose::CRef c = propagateAggregateAsTrue(solver,propagations,aggIdStarter.first >=0 ? aggIdStarter.first : -aggIdStarter.first,starter,true);
            if(c != Glucose::CRef_Undef) return c;
        }
         
    }else{
        auto aggSetStarter = isAggSetStarter(literal);
        if(aggSetStarter.second){

            // std::cout << "Propagation starting from aggSet"<<std::endl;
            // std::cout << "    Received literal: ";AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(literal >= 0 ? literal : -literal));
            // std::cout << "    Remapped literal: ";AuxMapHandler::getInstance().printTuple(literals[aggSetStarter.first >=0 ? aggSetStarter.first : -aggSetStarter.first]);
            // std::cout << "   Associated weight: "<<weights[aggSetStarter.first >=0 ? aggSetStarter.first : -aggSetStarter.first]<<std::endl;
            for(int i=0; i<bounds.size(); i++){
                if(ids[i]->isTrue() && currentSum<bounds[i]){
                    Glucose::CRef c = propagateAggregateAsTrue(solver,propagations,i,starter,false);
                    if(c != Glucose::CRef_Undef) return c;

                }else if(ids[i]->isFalse() && currentSum+maxPossibleSum >= bounds[i]){
                    Glucose::CRef c = propagateAggregateAsFalse(solver,propagations,i,starter,false);
                    if(c != Glucose::CRef_Undef) return c;

                }else if(ids[i]->isUndef()){
                    if(currentSum>=bounds[i]){
                        int varL = ids[i]->getId();
                        bool negated = false;

                        bool foundConflict = solver->isConflictPropagation(varL, negated);
                        bool assigned = solver->isAssigned(varL);
                        if(!assigned || foundConflict){

                            if(solver->currentLevel() > 0){
                                assert((aggSetNegated && starter->isFalse()) || (!aggSetNegated && starter->isTrue()));
                                Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? ids[i]->getReasonLits() : solver->getReasonClause();
                                propagationReason.clear();
                                propagationReason.push(Glucose::mkLit(varL,negated));
                                // starter is aggset 
                                propagationReason.push(Glucose::mkLit(starter->getId(), aggSetNegated ? false : true));
                                for(unsigned j = 0; j<literals.size(); j++){
                                    int varR = literals[j]->getId();
                                    if(varR == starter->getId() || starter->isUndef()) continue;
                                    
                                    if(aggSetNegated){
                                        if(literals[j]->isFalse()){
                                            propagationReason.push(Glucose::mkLit(literals[j]->getId(),false));
                                        }    
                                    }else{
                                        if(literals[j]->isTrue()){
                                            propagationReason.push(Glucose::mkLit(literals[j]->getId(),true));
                                        }
                                    }
                                }
                                // DEBUG PRINTING
                                // std::cout << "      Propagating ";AuxMapHandler::getInstance().printTuple(ids[i]);std::cout << std::endl;
                                // std::cout << "         Reason: ";
                                // for(int index = 0; index < propagationReason.size(); index++){
                                //     Glucose::Lit lit = propagationReason[index];
                                //     std::cout << (sign(lit) ? "not " : "");
                                //     AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(lit)));
                                // }
                                // std::cout << std::endl;
                                // -------------
                                Glucose::CRef clause = solver->externalPropagation(varL,negated,this);
                                if(clause != Glucose::CRef_Undef)
                                    return clause;
                            }else{
                                propagations.push_back(Glucose::mkLit(varL, negated));
                                polarity.push_back(negated);
                            }
                        }
                    }else if(currentSum + maxPossibleSum < bounds[i]){
                        int varL = ids[i]->getId();
                        bool negated = true;

                        bool foundConflict = solver->isConflictPropagation(varL, negated);
                        bool assigned = solver->isAssigned(varL);
                        if(!assigned || foundConflict){

                            if(solver->currentLevel() > 0){

                                assert((aggSetNegated && starter->isTrue()) || (!aggSetNegated && starter->isFalse()));
                                Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? ids[i]->getReasonLits() : solver->getReasonClause();
                                propagationReason.clear();
                                propagationReason.push(Glucose::mkLit(varL,negated));
                                // starter is aggset 
                                propagationReason.push(Glucose::mkLit(starter->getId(), aggSetNegated ? true : false));
                                for(unsigned j = 0; j<literals.size(); j++){
                                    int varR = literals[j]->getId();
                                    if(varR == starter->getId() || starter->isUndef()) continue;
                                    
                                    if(aggSetNegated){
                                        if(literals[j]->isTrue()){
                                            propagationReason.push(Glucose::mkLit(literals[j]->getId(),true));
                                        }    
                                    }else{
                                        if(literals[j]->isFalse()){
                                            propagationReason.push(Glucose::mkLit(literals[j]->getId(),false));
                                        }
                                    }
                                }
                                // DEBUG PRINTING
                                // std::cout << "      Propagating not ";AuxMapHandler::getInstance().printTuple(ids[i]);std::cout << std::endl;
                                // std::cout << "         Reason: ";
                                // for(int index = 0; index < propagationReason.size(); index++){
                                //     Glucose::Lit lit = propagationReason[index];
                                //     std::cout << (sign(lit) ? "not " : "");
                                //     AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(lit)));
                                // }
                                // std::cout << std::endl;
                                // --------------

                                Glucose::CRef clause = solver->externalPropagation(varL,negated,this);
                                if(clause != Glucose::CRef_Undef)
                                    return clause;
                            }else{
                                propagations.push_back(Glucose::mkLit(varL,negated));
                                polarity.push_back(negated);
                            }
                        }
                    }
                }
            }
        }
    }
    for(unsigned i = 0; i< propagations.size(); i++){
        bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);
        bool assigned = solver->isAssigned(var(propagations[i]));
        if(!assigned) solver->assignFromPropagators(Glucose::mkLit(var(propagations[i]), polarity[i]));
        else if(foundConflict) {
            solver->addClause_(lits);
            return Glucose::CRef_PropConf;
        }
    }
    return Glucose::CRef_Undef;
}
void AggregatePropagator::attachWatched(){

    for(auto pair : aggIdMapping){
        int id = pair.first > 0 ? pair.first : -pair.first;
        TupleFactory::getInstance().addWatcher(this->getId(),id,true);
        TupleFactory::getInstance().addWatcher(this->getId(),id,false);
    }
    for(auto pair : aggSetMapping){
        int id = pair.first > 0 ? pair.first : -pair.first;
        TupleFactory::getInstance().addWatcher(this->getId(),id,true);
        TupleFactory::getInstance().addWatcher(this->getId(),id,false);
    }
}