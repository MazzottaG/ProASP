#include "AbstractGeneratorCompiler.h"

void AbstractGeneratorCompiler::printHeadDerivation(std::string tuplename){
    outfile << ind << "const auto& insertResult = "<<tuplename<<"->setStatus(Undef);\n";
    outfile << ind++ << "if(insertResult.second){\n";
        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList("<<tuplename<<"->getId());\n";
        outfile << ind << "AuxMapHandler::getInstance().initTuple("<<tuplename<<");\n";
        outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
        outfile << ind << "while ("<<tuplename<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
    outfile << --ind << "}\n";                        
}

void AbstractGeneratorCompiler::compileSingleStarter(bool recursive,std::vector<unsigned> order,unsigned starter){
    // if(order.empty() && starter >= rule->getFormulas().size()) return;
    std::unordered_set<std::string> boundVars;
    unsigned closingPars = 1;
    if(starter < rule->getFormulas().size()){
        const aspc::Literal* startingLit = (const aspc::Literal*) rule->getFormulas()[starter];
        if(startingLit->getPredicateName() != ""){
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<startingLit->getPredicateName()<<"()){\n";
            for(unsigned k=0; k<startingLit->getAriety(); k++){
                if(!startingLit->isVariableTermAt(k) || boundVars.count(startingLit->getTermAt(k))){
                    std::string term = isInteger(startingLit->getTermAt(k)) || startingLit->isVariableTermAt(k) ? startingLit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+startingLit->getTermAt(k)+"\")";
                    outfile << ind++ << "if(starter->at("<<k<<") == " << term << "){\n";
                    closingPars++;
                }else{
                    outfile << ind << "int "<<startingLit->getTermAt(k) << " = starter->at(" <<k<< ");\n"; 
                    boundVars.insert(startingLit->getTermAt(k));
                }
            }
        }else
            closingPars=0;
    }else{
        outfile << ind++ << "{\n";
    }
    if(!rule->isConstraint() && rule->getHead()[0].getPredicateName() == "sharedVar0"){
        std::cout << "Start debugger"<<std::endl;
    }
    std::cout << "   Compiling ";
    rule->print();
    std::cout << "      Starter: " << starter<<std::endl;
    for(unsigned index : order){
        const aspc::Formula* f = rule->getFormulas()[index];
        std::cout << "      Considering formula: "; f->print(); std::cout<<std::endl;
        if(f->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)f;
            if(lit->getPredicateName() == "") continue;
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
                    if(!rule->isConstraint())
                        closingPars += printTrackedCheck("tuple_"+std::to_string(index));
                }
            
                closingPars++;
            }else{
                std::string prefix = "AuxMapHandler::getInstance().get_";
                std::string mapName = lit->getPredicateName()+"_";
                std::string terms = "";
                std::unordered_set<int> boundIndices;
                std::string predStruct = predicateToStruct[lit->getPredicateName()];
                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                        std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                        mapName+=std::to_string(k)+"_";
                        terms += (terms != "" ? ","+term : term);
                        boundIndices.insert(k);
                    }
                }

                outfile << ind << structType<<" tuplesU_"<<index<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                outfile << ind << structType<<" tuples_"<<index<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                
                outfile << ind++ << "for(auto i=tuples_"<<index<<"->begin(); i!=tuplesU_"<<index<<"->end(); i++){\n";
                closingPars++;
                    outfile << ind << "if(i == tuples_"<<index<<"->end()) i=tuplesU_"<<index<<"->begin();\n";
                    outfile << ind << "if(i == tuplesU_"<<index<<"->end()) break;\n";
                    outfile << ind << "Tuple* tuple_"<<index<<"= TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
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
                if(!rule->isConstraint())
                    closingPars += printTrackedCheck("tuple_"+std::to_string(index));
            }
        }else if(!f->containsAggregate()){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) f;
            if(f->isBoundedValueAssignment(boundVars)){
                outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                boundVars.insert(ineq->getAssignedVariable(boundVars));
            }else{
                outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                closingPars++;
            }
        }else{
            std::cout << "  Printing aggregate initialization"<<std::endl;
            closingPars += printAggregateInitialization(boundVars);
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
            // std::cout << "Debug original predicates AbstractGeneratorCompiler";
            // for(std::string pred : originalPredicates){
            //     std::cout << pred << " ";
            // }
            // std::cout << std::endl;
            
            outfile << "}, AuxMapHandler::getInstance().get_"<<atom->getPredicateName()<<"(),"<<(originalPredicates.count(atom->getPredicateName()) ? "false" : "true")<<");\n";
            
            outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId())){\n";
                printUntrackLiteral("head_"+std::to_string(index));
                printAddSP(index);
                #ifdef DEBUG_GEN
                outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(head_"<<index<<");\n";
                #endif
                if(recursive){
                    outfile << ind << "stack.push_back(head_"<<index<<"->getId());\n";
                }else{
                    printHeadDerivation("head_"+std::to_string(index));
                }  
            outfile << --ind << "}//close if fact\n";                              
        }
    }else{
        printAddConstraintClause(order,starter < rule->getFormulas().size());
    }
    std::cout << "   Compiled rule"<<std::endl;
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
    std::cout << "   Reordering rule: ";rule->print();
    if(this->leaveAggregateAtEnd()) std::cout << "Aggregate Evaluated At The End"<<std::endl;
    else std::cout << "Aggregate Evaluated After Positive Body"<<std::endl;
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
                if(!visitedFormulas[i] && !body[i]->containsAggregate()){
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
                //there exists at least one formula not containing aggregates that has not been visited
                if(leaveAggregateAtEnd()){
                    std::cout << "Error ordering rule ";rule->print();
                    exit(180);
                }else{
                    for(unsigned i=0; i<body.size(); i++){
                        if(!visitedFormulas[i] && body[i]->containsAggregate() && body[i]->isBoundedValueAssignment(boundVars)){
                            currentOrdering->push_back(i);
                            visitedFormulas[i]=true;
                            boundVars.insert(((const aspc::ArithmeticRelationWithAggregate*)body[i])->getAssignedVariable(boundVars));
                            selectedFormula=i;
                        }
                    }
                }
                
            }
            if(selectedFormula<body.size()){
                std::cout << "   Selected ";body[selectedFormula]->print();std::cout << std::endl;
            }
        }
        for(unsigned i=0; i<body.size(); i++){
            if(!visitedFormulas[i] && body[i]->containsAggregate()){
                std::cout << "   Adding bound aggregate to current ordering"<<std::endl;
                currentOrdering->push_back(i);
                visitedFormulas[i]=true;
            }
        }
    }    
    std::cout << "   Reordered"<<std::endl;
    return orderByStarters;
}