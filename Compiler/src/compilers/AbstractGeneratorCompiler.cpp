#include "AbstractGeneratorCompiler.h"

void AbstractGeneratorCompiler::compileSingleStarter(bool recursive,std::vector<unsigned> order,unsigned starter){
    // if(order.empty() && starter >= rule->getFormulas().size()) return;
    std::unordered_set<std::string> boundVars;
    unsigned closingPars = 1;
    if(starter < rule->getFormulas().size()){
        const aspc::Literal* startingLit = (const aspc::Literal*) rule->getFormulas()[starter];
        outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<startingLit->getPredicateName()<<"()){\n";
        for(unsigned k=0; k<startingLit->getAriety(); k++){
            if(!startingLit->isVariableTermAt(k) || boundVars.count(startingLit->getTermAt(k))){
                std::string term = isInteger(startingLit->getTermAt(k)) || startingLit->isVariableTermAt(k) ? startingLit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant("+startingLit->getTermAt(k)+")";
                outfile << ind++ << "if(starter->at("<<k<<") == " << term << "){\n";
                closingPars++;
            }else{
                outfile << ind << "int "<<startingLit->getTermAt(k) << " = starter->at(" <<k<< ");\n"; 
                boundVars.insert(startingLit->getTermAt(k));
            }
        }
    }else{
        outfile << ind++ << "{\n";
    }
    for(unsigned index : order){
        const aspc::Formula* f = rule->getFormulas()[index];
        if(f->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)f;
            if(lit->isBoundedLiteral(boundVars)){
                outfile << ind << "Tuple* tuple_"<<index<<"=TupleFactory::getInstance().find({";
                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(k>0) outfile << ",";
                    outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                }
                outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                if(lit->isNegated()){
                    outfile << ind++ << "if(tuple_"<<index<<" == NULL || !tuple_"<<index<<"->isTrue()){\n";
                }else{
                    outfile << ind++ << "if(tuple_"<<index<<" != NULL && !tuple_"<<index<<"->isFalse()){\n";
                }
            
                closingPars++;
            }else{
                std::string prefix = "AuxMapHandler::getInstance().get_";
                std::string mapName = lit->getPredicateName()+"_";
                std::string terms = "";
                std::unordered_set<int> boundIndices;

                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                        std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                        mapName+=std::to_string(k)+"_";
                        terms += (terms != "" ? ","+term : term);
                        boundIndices.insert(k);
                    }
                }
                outfile << ind << "const std::vector<int>* tuplesU_"<<index<<" = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                outfile << ind << "const std::vector<int>* tuples_"<<index<<" = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                outfile << ind++ << "for(unsigned i=0; i<tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size(); i++){\n";
                closingPars++;
                    outfile << ind << "Tuple* tuple_"<<index<<"= i<tuples_"<<index<<"->size() ? TupleFactory::getInstance().getTupleFromInternalID(tuples_"<<index<<"->at(i)) : TupleFactory::getInstance().getTupleFromInternalID(tuplesU_"<<index<<"->at(i-tuples_"<<index<<"->size()));\n";
                    outfile << ind++ << "if(tuple_"<<index<<"!= NULL){\n";
                    closingPars++;
                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(lit->isVariableTermAt(k) && !boundIndices.count(k)){
                        if(!boundVars.count(lit->getTermAt(k))){
                            outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<index<<"->at("<<k<<");\n";
                            boundVars.insert(lit->getTermAt(k));
                        }else{
                            outfile << ind++ << "if("<< lit->getTermAt(k)<< " == tuple_"<<index<<"->at("<<k<<")){\n";
                            closingPars++;
                        }
                    }
                }
            }
        }else{
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) f;
            if(f->isBoundedValueAssignment(boundVars)){
                outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                boundVars.insert(ineq->getAssignedVariable(boundVars));
            }else{
                outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                closingPars++;
            }
        }
    }
    if(!rule->isConstraint()){
        printAddClause(order,starter < rule->getFormulas().size());
        std::vector<aspc::Atom> head = rule->getHead();
        for(int index=0;index<head.size();index++){
            aspc::Atom* atom = &head[index];
            outfile << ind << "Tuple* head_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";
            for(unsigned k=0; k<atom->getAriety(); k++){
                if(k>0) outfile << ",";
                outfile << (atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+atom->getTermAt(k)+"\")");
            }
            outfile << "}, AuxMapHandler::getInstance().get_"<<atom->getPredicateName()<<"(),"<<(predicateIds.count(atom->getPredicateName()) ? "false" : "true")<<");\n";
            
            outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId())){\n";
                printAddSP(index);
                #ifdef DEBUG_GEN
                outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(head_"<<index<<");\n";
                #endif
                if(recursive){
                    outfile << ind << "stack.push_back(head_"<<index<<"->getId());\n";
                }else{
                    outfile << ind << "const auto& insertResult = head_"<<index<<"->setStatus(Undef);\n";
                    outfile << ind++ << "if(insertResult.second){\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(head_"<<index<<"->getId());\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                        outfile << ind << "while (head_"<<index<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                    outfile << --ind << "}\n";                        
                }  
            outfile << --ind << "}\n";                              
        }
    }else{
        printAddConstraintClause(order,starter < rule->getFormulas().size());
    }
    
    while (closingPars > 0){
        outfile << --ind << "}// closing"<<std::endl;
        closingPars--;
    }
}
void AbstractGeneratorCompiler::compileFromStarter(bool recursive){
    auto orders = reorderRule();
    unsigned bodysize = rule->getFormulas().size();
    for(unsigned starter = 0; starter < bodysize; starter++){
        if(rule->getFormulas()[starter]->isPositiveLiteral()){
            std::vector<unsigned>& order = orders[starter];
            compileSingleStarter(recursive,order,starter);
        }
    }
}
void AbstractGeneratorCompiler::compileNoStarter(bool recursive){
    auto orders = reorderRule();
    unsigned bodysize = rule->getFormulas().size();
    compileSingleStarter(recursive,orders[bodysize],bodysize);
}
std::vector<std::vector<unsigned>> AbstractGeneratorCompiler::reorderRule(){
    std::cout << "Reordering rule: ";rule->print();
    // general order + ordering starting from positive literal in the same component
    auto body = rule->getFormulas();
    std::vector<std::vector<unsigned>> orderByStarters;
    for(unsigned starter = 0; starter <= body.size(); starter++){
        orderByStarters.push_back({});
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;
        if(starter < body.size()){
            //component empty means declare structure for rule propagators            
            const aspc::Formula* startingFormula = body[starter];
            if(!startingFormula->isLiteral() || !startingFormula->isPositiveLiteral()) continue;
            
            // same component 
            visitedFormulas[starter]=true;
            startingFormula->addVariablesToSet(boundVars);
        }
        unsigned selectedFormula=0;
        std::vector<unsigned>* currentOrdering=&orderByStarters.back();
        while (selectedFormula < body.size()){
            selectedFormula = body.size();
            bool notVisited = false;
            for(unsigned i=0; i<body.size(); i++){
                if(!visitedFormulas[i]){
                    notVisited=true;
                    if(body[i]->isBoundedLiteral(boundVars) || body[i]->isBoundedRelation(boundVars) || body[i]->isBoundedValueAssignment(boundVars)){
                        selectedFormula=i;
                        break;
                    }
                    if(body[i]->isPositiveLiteral() && selectedFormula == body.size()) selectedFormula=i;
                }
            }
            if(selectedFormula != body.size()){
                visitedFormulas[selectedFormula]=true;
                const aspc::Formula* currentFormula = body[selectedFormula];
                currentOrdering->push_back(selectedFormula);
                if(currentFormula->isLiteral() && !currentFormula->isBoundedLiteral(boundVars)){
                    const aspc::Literal* literal = (const aspc::Literal*) currentFormula;
                    std::vector<unsigned> boundIndices;
                    for(unsigned k = 0; k<literal->getAriety(); k++){
                        if(!literal->isVariableTermAt(k) || boundVars.count(literal->getTermAt(k))){
                            boundIndices.push_back(k);
                        }
                    }
                    usedAuxMap[literal->getPredicateName()].insert(boundIndices);
                    literal->addVariablesToSet(boundVars);
                }else{
                    if(currentFormula->isBoundedValueAssignment(boundVars)){
                        const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) currentFormula;
                        boundVars.insert(ineq->getAssignedVariable(boundVars));
                    }
                }
            }else if(notVisited){
                std::cout << "Error ordering rule ";rule->print();
                exit(180);
            }
        }
    }    
    return orderByStarters;
}