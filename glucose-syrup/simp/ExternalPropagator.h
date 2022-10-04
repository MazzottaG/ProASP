#ifndef EXTERNALPROPAGATOR_H
#define EXTERNALPROPAGATOR_H
#include <iostream>
#include <map>
#include "../core/Solver.h"

class ExternalPropagator{
    private:
        std::map<int,std::string> varNames;
        bool aFalse;
    public:
        ExternalPropagator(){
            this->varNames[1]="a";
            this->varNames[2]="b";
            this->varNames[3]="c";
            this->varNames[4]="d";
            this->varNames[5]="e";
            aFalse=true;
        }
        void onLiteralUndef(int lit){
            std::cout << "Unrolling " << this->varNames[lit > 0 ? lit : -lit]<<std::endl;
            if(this->varNames[lit > 0 ? lit : -lit] == "a"){
                aFalse=false;
            }
        }
        Glucose::CRef onLiteralTrue(int lit,Glucose::Solver* s){
             
            std::string name = lit > 0 ? this->varNames[lit] : "not "+this->varNames[-lit];
            std::cout << "Received "<<name<<std::endl;
            if(name == "not a"){
                aFalse=true;
                // c:-not a. 

                // propagate c as true with clause  a,c
                s->clearReasonClause();
                s->addLiteralToReason(0,false);
                s->addLiteralToReason(2,false);
                Glucose::CRef clause = s->externalPropagation(2,false);
                if(clause != Glucose::CRef_Undef)
                    return clause;

                // propagate b as true with clause  a,b
                // s->clearReasonClause();
                // s->addLiteralToReason(0,false);
                // s->addLiteralToReason(1,false);
                // s->externalPropagation(1,false);
            }
            if(name == "c"){
                // :-c,not b.
                // propagate c as true with clause  not c,b
                s->clearReasonClause();
                s->addLiteralToReason(2,true);
                s->addLiteralToReason(1,false);
                Glucose::CRef clause = s->externalPropagation(1,false);
                if(clause != Glucose::CRef_Undef)
                    return clause;
                
                // :-c, b.
                // propagate c as true with clause  not c,not b
                s->clearReasonClause();
                s->addLiteralToReason(2,true);
                s->addLiteralToReason(1,true);
                Glucose::CRef clause1 = s->externalPropagation(1,true);
                if(clause1 != Glucose::CRef_Undef)
                    return clause1;
                
            }
           
            return Glucose::CRef_Undef;
        }
};
#endif

