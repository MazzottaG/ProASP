#include "GrounderGenCompiler.h"

void GrounderGenCompiler::printAddConstraintClause(std::vector<unsigned> order,bool starter){

    for(int index : order){
        if(rule->getFormulas()[index]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)rule->getFormulas()[index];
            std::string sign = lit->isNegated() ? "":"-";
            if(lit->isNegated()){
                outfile << ind++ << "if(tuple_"<<index<<" != NULL){\n";
                    outfile << ind << "clause.push_back(tuple_"<<index<<"->getId());\n";                        
                outfile << --ind << "}\n";
            }else{
                outfile << ind << "clause.push_back(-tuple_"<<index<<"->getId());\n";                        
            }
        }
    }
    outfile << ind << "TupleFactory::getInstance().addNewInternalConstraint(clause);\n";
    outfile << ind << "clause.clear();\n";
}
void GrounderGenCompiler::printAddClause(std::vector<unsigned> order,bool starter){
    std::string terms= !starter ? "" : "starter->getId()";
    for(int index : order){
        if(rule->getFormulas()[index]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)rule->getFormulas()[index];
            if(terms != "")
                terms+=",";
            std::string sign = lit->isNegated() ? "-":"";
            terms+=sign+"tuple_"+std::to_string(index)+"->getId()";

            if(lit->isNegated()){
                outfile << ind++ << "if(tuple_"<<index<<" == NULL){\n";
                //found false literal not generated yet
                    outfile << ind << "tuple_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";
                    for(unsigned k=0; k<lit->getAriety(); k++){
                        if(k>0) outfile << ",";
                        outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                    }
                    outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"(),"<<(predicateIds.count(lit->getPredicateName()) ? "false" : "true")<<");\n";
                    #ifdef DEBUG_GEN
                    outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";
                    #endif
                    outfile << ind << "const auto& insertResult = tuple_"<<index<<"->setStatus(Undef);\n";
                    outfile << ind++ << "if(insertResult.second){\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(tuple_"<<index<<"->getId());\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                        outfile << ind << "while (tuple_"<<index<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                        outfile << ind << "TupleFactory::getInstance().trackLiteral(tuple_"<<index<<"->getId());\n";
                    outfile << --ind << "}\n";                        
                outfile << --ind << "}\n";
                
            }
            // outfile << ind << "std::cout << -"<<auxliteral<<"<<\" \" <<"<<(lit->isNegated() ? "\" -\"" : "\" \"")<<"; AuxMapHandler::getInstance().printTuple(tuple_"<<index<<"); std::cout << std::endl;\n";
            // outfile << ind << "std::cout << -"<<auxliteral<<"<<\" \"<< "<<(rule->getFormulas()[index]->isPositiveLiteral() ? "" : "-")<<"tuple_"<<index<<"->getId() << \" 0\"<<std::endl;\n";
        }
    }

    if(starter){
        int bodysize = rule->getFormulas().size();
        if(bodysize == 1){
            assert(order.size()==0);
            outfile << ind << "Tuple* clauseTuple = starter;\n";
        }else{
            outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
        }
    }else{
        int bodysize = rule->getFormulas().size();
        if(bodysize == 1){
            assert(rule->getFormulas()[order[0]]->isPositiveLiteral());
            outfile << ind << "Tuple* clauseTuple = tuple_"<<order[0]<<";\n";
        }else{
            outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
        }
    }
    // for(int index : order){
    //     if(rule->getFormulas()[index]->isLiteral()){
    //         outfile << ind << "std::cout <<"<<(rule->getFormulas()[index]->isPositiveLiteral() ? "\" -\"" : "\" \"")<<"; AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";
    //     }
    // }
    // outfile << ind << "std::cout << "<<auxliteral<<" << \" 0\"<<std::endl;\n";
}

void GrounderGenCompiler::printAddSP(int index){
    outfile << ind << "TupleFactory::getInstance()."<<(rule->getFormulas().size() != 1 ? "addAuxForLiteral" : "addAtomForLiteral")<<"(head_"<<index<<"->getId(),clauseTuple->getId());\n";
}

int GrounderGenCompiler::printTrackedCheck(std::string tuplename){
    outfile << ind++ << "if(!TupleFactory::getInstance().isTracked("<<tuplename<<"->getId())){\n";
    return 1;
}