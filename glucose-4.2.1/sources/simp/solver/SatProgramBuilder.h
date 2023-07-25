#ifndef SATPROGRAMBUILDER_H
#define SATPROGRAMBUILDER_H

#include "../datastructures/TupleFactory.h"
#include "../SimpSolver.h"
#include "AuxMapHandler.h"

class SatProgramBuilder{

    public:
        static SatProgramBuilder& getInstance(){
            static SatProgramBuilder instance;
            return instance;
        }
        bool computeCompletion(Glucose::SimpSolver* solver){
            bool ok=true;
            std::unordered_map<unsigned,unsigned> auxRemapping;
            if(!auxCompletion(auxRemapping,solver) || !headAtomCompletion(auxRemapping,solver) || !addConstraints(solver))
                return false;
            return true;
        }
    private:
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
                        clause.push(Glucose::mkLit(negated ? -content[i]: content[i], negated));                  
                    }
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
            std::cout << "%%%%%%%%%%%%%%%%%%%%%%% Aux Completion %%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;

            Glucose::vec<Glucose::Lit> binClause;
            Glucose::vec<Glucose::Lit> clause;
            auto clauseData = TupleFactory::getInstance().popClause();
            while(clauseData.first !=NULL){
                int bodyId = clauseData.first->getId();
                int auxLiteral = TupleFactory::getInstance().addExtraSymbol();
                while (auxLiteral >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}
                auxRemapping[bodyId]=auxLiteral;
                TupleLight* body = clauseData.first;
                unsigned bodyLength = clauseData.second;
                int * content = body->getContent();
                
                clause.clear();
                clause.push(Glucose::mkLit(auxLiteral,false));

                std::vector<int> debugClause;
                for(int i=0; i<bodyLength; i++){
                    bool negated = content[i] < 0;
                    std::cout << "not aux"<<bodyId<<" v "<< (negated ? "not " : "");AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(negated ? -content[i]: content[i]));std::cout << std::endl;
                    binClause.clear();
                    binClause.push(Glucose::mkLit(auxLiteral,true));
                    binClause.push(Glucose::mkLit(negated ? -content[i]: content[i], negated));

                    clause.push(Glucose::mkLit(negated ? -content[i]: content[i], !negated));
                    debugClause.push_back(-content[i]);
                    if(!solver->addClause_(binClause))
                       return false;                   
                }
                std::cout << "aux"<<bodyId;
                for(int i=0;i<debugClause.size();i++){
                    std::cout <<" v "<< (debugClause[i] < 0 ? "not ":"");
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(debugClause[i] < 0 ? -debugClause[i]: debugClause[i]));
                }
                std::cout << std::endl;

                if(!solver->addClause_(clause))
                    return false;
                delete clauseData.first;
                clauseData = TupleFactory::getInstance().popClause();
            }
            std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;

            return true;
        }
        bool headAtomCompletion(std::unordered_map<unsigned,unsigned>& auxRemapping,Glucose::SimpSolver* solver){
            std::cout << "%%%%%%%%%%%%%%%%%%%%%%% Head Completion %%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;
            Glucose::vec<Glucose::Lit> binClause;
            Glucose::vec<Glucose::Lit> clause;
            
            auto& auxsForLit = TupleFactory::getInstance().getAuxsForLiteral();
            auto& atomsForLit = TupleFactory::getInstance().getAtomsForLiteral();
            for(auto pair:auxsForLit){
                //pair contains <head_atom, set<clauseId>>
                clause.clear();
                clause.push(Glucose::mkLit(pair.first,true));

                std::vector<std::string> debugAux;
                for(auto aux : pair.second){
                    int freshSymbol = auxRemapping[aux];
                    
                    binClause.clear();
                    binClause.push(Glucose::mkLit(pair.first,false));
                    binClause.push(Glucose::mkLit(freshSymbol, true));
                    std::cout << "not aux"<<aux<<" v ";AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));std::cout << std::endl;
                    
                    if(!solver->addClause_(binClause))
                       return false;                    
                    clause.push(Glucose::mkLit(freshSymbol, false));
                    debugAux.push_back("aux"+std::to_string(aux));
                }
                std::vector<int> debugAtom;
                for(auto supAtom : atomsForLit[pair.first]){
                    binClause.clear();
                    binClause.push(Glucose::mkLit(pair.first,false));
                    binClause.push(Glucose::mkLit(supAtom, true));
                    if(!solver->addClause_(binClause))
                       return false;                    
                    
                    std::cout << "not ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(supAtom));
                    std::cout << " v ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));std::cout << std::endl;
                    
                    clause.push(Glucose::mkLit(supAtom, false));
                    debugAtom.push_back(supAtom);
                }
                std::cout << "not ";
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));
                for(int i=0;i<debugAtom.size();i++){
                    std::cout <<" v ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(debugAtom[i]));
                }
                for(int i=0;i<debugAux.size();i++){
                    std::cout <<" v " << debugAux[i];
                }
                std::cout << std::endl;
                if(!solver->addClause_(clause)) return false;
            }
            for(auto pair:atomsForLit){
                //pair contains <head_atom, set<atom>>

                if(auxsForLit.count(pair.first)) continue;

                clause.clear();
                clause.push(Glucose::mkLit(pair.first,true));

                std::vector<int> debugAtom;
                for(auto supAtom : pair.second){
                    binClause.clear();
                    binClause.push(Glucose::mkLit(pair.first,false));
                    binClause.push(Glucose::mkLit(supAtom, true));
                    if(!solver->addClause_(binClause))
                       return false;                    
                    std::cout << "not ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(supAtom));
                    std::cout << " v ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));std::cout << std::endl;
                    clause.push(Glucose::mkLit(supAtom, false));
                    debugAtom.push_back(supAtom);
                }
                std::cout << "not ";
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(pair.first));
                for(int i=0;i<debugAtom.size();i++){
                    std::cout <<" v ";
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(debugAtom[i]));
                }
                std::cout << std::endl;
                if(!solver->addClause_(clause)) return false;
            }
            std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"<<std::endl;

            return true;
        }
        
    

};
#endif