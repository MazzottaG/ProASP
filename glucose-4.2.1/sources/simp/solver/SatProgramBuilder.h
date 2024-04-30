#ifndef SATPROGRAMBUILDER_H
#define SATPROGRAMBUILDER_H

#include "../datastructures/TupleFactory.h"
#include "../SimpSolver.h"
#include "AuxMapHandler.h"
#include "Generator.h"

class SatProgramBuilder{

    public:
        static SatProgramBuilder& getInstance(){
            static SatProgramBuilder instance;
            return instance;
        }

        bool computeCompletion(Glucose::SimpSolver* solver){
            std::unordered_map<unsigned,unsigned> auxRemapping;
            if(!auxCompletion(auxRemapping,solver) || !headAtomCompletion(auxRemapping,solver) || !addConstraints(solver)) {
                cleanup();
                return false;
            }
            return true;
        }
        
    private:
        void cleanup(){
            TupleFactory::getInstance().cleanupCompletionStruct();
        }
        void printClause(Glucose::vec<Glucose::Lit>& clause){
            for(unsigned j = 0; j<clause.size(); j++){
                bool negated = Glucose::sign(clause[j]);
                int var = Glucose::var(clause[j]);
                std::cout << (negated ? "-" : "") << var << " ";
                // std::cout << (negated ? "-" : ""); AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var)); std::cout<< " ";
            }
            std::cout << "0"<<endl;
        }
        SatProgramBuilder(){}
        bool addConstraints(Glucose::SimpSolver* solver){
            auto constraint = TupleFactory::getInstance().popConstraint();
            Glucose::vec<Glucose::Lit> clause;
            bool ok = true;
            while(constraint.first != NULL){
                if(ok){
                    int * content = constraint.first->getContent();
                    for(int i=0; i<constraint.second; i++){
                        bool negated = content[i] < 0;
                        int var = negated ? -content[i]: content[i];
                        int realVar = Generator::getInstance().getRealVar(var);
                        clause.push(Glucose::mkLit(realVar, negated));                  
                    }
                    // printClause(clause);
                    
                    if(!solver->addClause_(clause))
                        ok=false;
                    clause.clear();
                }
                delete constraint.first;
                constraint = TupleFactory::getInstance().popConstraint();
            }
            return ok;
        }
        bool auxCompletion(std::unordered_map<unsigned,unsigned>& auxRemapping,Glucose::SimpSolver* solver){
            //std::cout << "%%%%%%%%%%%%%%%%%%%%%%% Aux Completion %%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;

            Glucose::vec<Glucose::Lit> binClause;
            Glucose::vec<Glucose::Lit> clause;
            auto clauseData = TupleFactory::getInstance().popClause();
            while(clauseData.first !=NULL){
                int bodyId = clauseData.first->getId();
                unsigned bodyLength = clauseData.second;
                TupleLight* body = clauseData.first;
                int * content = body->getContent();
                if(bodyLength == 1 && content[0] > 0){
                    int var = content[0];
                    int realVar = Generator::getInstance().getRealVar(var);
                    auxRemapping[bodyId]=realVar;
                }else{
                    int auxLiteral = TupleFactory::getInstance().addExtraSymbol();
                    while (auxLiteral >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}
                    auxRemapping[bodyId]=auxLiteral;
                    clause.clear();
                    clause.push(Glucose::mkLit(auxLiteral,false));
                    for(int i=0; i<bodyLength; i++){
                        bool negated = content[i] < 0;
                        int var = negated ? -content[i]: content[i];
                        int realVar = Generator::getInstance().getRealVar(var);
                        binClause.clear();
                        binClause.push(Glucose::mkLit(auxLiteral,true));
                        binClause.push(Glucose::mkLit(realVar, negated));
                        clause.push(Glucose::mkLit(realVar, !negated));
                        // printClause(binClause);
                        if(!solver->addClause_(binClause))
                            return false;  
                    }
                    // printClause(clause);
                    if(!solver->addClause_(clause))
                        return false;
                }
                delete clauseData.first;
                clauseData = TupleFactory::getInstance().popClause();
            }
            //std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;
            return true;
        }
        bool headAtomCompletion(std::unordered_map<unsigned,unsigned>& auxRemapping,Glucose::SimpSolver* solver){
            //std::cout << "%%%%%%%%%%%%%%%%%%%%%%% Head Completion %%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;
            Glucose::vec<Glucose::Lit> binClause;
            Glucose::vec<Glucose::Lit> clause;
            
            auto& auxsForLit = TupleFactory::getInstance().getAuxsForLiteral();
            auto& atomsForLit = TupleFactory::getInstance().getAtomsForLiteral();
            for(auto pair:auxsForLit){
                //pair contains <head_atom, set<clauseId>>
                clause.clear();
                int realPairFirst = Generator::getInstance().getRealVar(pair.first);
                clause.push(Glucose::mkLit(realPairFirst,true));
                std::vector<std::string> debugAux;
                for(auto aux : pair.second){
                    int freshSymbol = auxRemapping[aux];
                    binClause.clear();
                    binClause.push(Glucose::mkLit(realPairFirst,false));
                    binClause.push(Glucose::mkLit(freshSymbol, true));
                    // printClause(binClause);
                    if(!solver->addClause_(binClause))
                        return false;
                    clause.push(Glucose::mkLit(freshSymbol, false));
                }
                for(auto supAtom : atomsForLit[pair.first]){
                    binClause.clear();
                    int realSupAtom = Generator::getInstance().getRealVar(supAtom);
                    binClause.push(Glucose::mkLit(realPairFirst,false));
                    
                    binClause.push(Glucose::mkLit(realSupAtom, true));
                    //printClause(binClause);
                    if(!solver->addClause_(binClause))
                        return false;

                    clause.push(Glucose::mkLit(realSupAtom, false));
                }
                // printClause(clause);
                if(!solver->addClause_(clause))
                    return false;
            }
            for(auto pair:atomsForLit){
                //pair contains <head_atom, set<atom>>

                if(auxsForLit.count(pair.first)!=0) continue;
                
                int realPairFirst = Generator::getInstance().getRealVar(pair.first);

                clause.clear();
                clause.push(Glucose::mkLit(realPairFirst,true));

                for(auto supAtom : pair.second){
                    int realSupAtom = Generator::getInstance().getRealVar(supAtom);
                    binClause.clear();
                    binClause.push(Glucose::mkLit(realPairFirst,false));
                    binClause.push(Glucose::mkLit(realSupAtom, true));
                    // printClause(binClause);
                    if(!solver->addClause_(binClause))
                       return false;  
                    clause.push(Glucose::mkLit(realSupAtom, false));
                }
                // printClause(clause);
                if(!solver->addClause_(clause)) return false;
            }
            //std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;

            return true;
        }
};
#endif