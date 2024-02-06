#include "PropagatorCompiler.h"


void PropagatorCompiler::compileRuleFromStarter(unsigned ruleId, std::ofstream& outfile, Indentation& ind){
    outfile << ind++ << "Glucose::CRef propagate(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits,int literal) override {\n";
    outfile << ind << "Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID( literal > 0 ? literal : -literal);\n";
    outfile << ind << "std::vector<Glucose::Lit> propagations;\n";
    outfile << ind << "std::vector<bool> polarity;\n";

    aspc::Rule rule = program.getRule(ruleId);
    if(rule.containsAggregate()){
        compileEagerRuleWithAggregate(ruleId,outfile,ind,true);
    }else{
        if(!rule.isConstraint()){
            // normal rules are assumed with one literal in the body
            const aspc::Atom * head = &rule.getHead()[0];
            const aspc::Formula * body = rule.getFormulas()[0];

            {
                // starter is head predicate 
                std::unordered_set<std::string> boundVars;
                outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<< head->getPredicateName() << "() && !TupleFactory::getInstance().isFact(starter->getId())){\n";
                    outfile << ind << "propagations.clear();\n";
                    unsigned closingPars=0;
                    for(unsigned k=0; k<head->getAriety();k++){
                        if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                            std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                            outfile << ind++ << "if(starter->at("<<k<<") == " <<term << "){\n";
                            closingPars++;
                        }else{
                            outfile << ind << "int "<<head->getTermAt(k) << " = starter->at(" <<k<< ");\n"; 
                            boundVars.insert(head->getTermAt(k));
                        }
                    }
                    
                    if(body->isLiteral()){
                        const aspc::Literal* lit = (const aspc::Literal*) body;
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                            outfile << ind++ << "if(literal > 0){\n";
                            // head is true
                                if(lit->isNegated()){
                                    // outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                    //     outfile << ind << "solver->clearReasonClause();\n";
                                    //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                    //     outfile << ind << "solver->addLiteralToReason(boundBody->getId(),true);\n";
                                    //     #ifdef DEBUG_PROP
                                    //     outfile << ind << "std::cout << \"True head for false literal false\"<<std::endl;\n";
                                    //     #endif
                                    //     printConflict(outfile,ind,false);
                                    // outfile << --ind << "}\n";
                                    // outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                        // printAddPropagatedToReason(outfile,ind,"boundBody",true);
                                        //     printAddToReason(outfile,ind,"literal","true");
                                        //     printTuplePropagation(outfile,ind,"boundBody",true,false);
                                        // outfile << --ind << "}\n";
                                    // outfile << --ind << "}\n";
                                    outfile << ind << "assert(!(boundBody != NULL && boundBody->isTrue()) || solver->currentLevel() == 0);\n";
                                    outfile << ind++ << "if(boundBody != NULL && boundBody->isUndef()){\n";
                                        printAddPropagatedToReason(outfile,ind,"boundBody",true);
                                            printAddToReason(outfile,ind,"literal","true");
                                            printTuplePropagation(outfile,ind,"boundBody",true,false);
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue() && solver->currentLevel() == 0){\n";
                                        outfile << ind << "lits.clear();\n";
                                        outfile << ind << "solver->addClause_(lits);\n";
                                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                                    outfile << --ind << "}\n";
                                    
                                }else{
                                    // outfile << ind++ << "if(boundBody == NULL || boundBody->isFalse()){\n";
                                    //     #ifdef DEBUG_PROP
                                    //     outfile << ind << "std::cout << \"True head for bound positive literal false\"<<std::endl;\n";
                                    //     #endif
                                    //     outfile << ind << "solver->clearReasonClause();\n";
                                    //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                    //     outfile << ind << "if(boundBody != NULL) solver->addLiteralToReason(boundBody->getId(),false);\n";
                                    //     printConflict(outfile,ind,false);
                                    // outfile << --ind << "}\n";
                                    // outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                        
                                    //     printAddPropagatedToReason(outfile,ind,"boundBody",false);
                                    //         printAddToReason(outfile,ind,"literal","true");
                                    //         printTuplePropagation(outfile,ind,"boundBody",false,false);
                                    //     outfile << --ind << "}\n";

                                    // outfile << --ind << "}\n";
                                    outfile << ind << "assert(!(boundBody == NULL || boundBody->isFalse()) || solver->currentLevel() == 0);\n";
                                    outfile << ind++ << "if(boundBody != NULL && boundBody->isUndef()){\n";
                                        
                                        printAddPropagatedToReason(outfile,ind,"boundBody",false);
                                            printAddToReason(outfile,ind,"literal","true");
                                            printTuplePropagation(outfile,ind,"boundBody",false,false);
                                        outfile << --ind << "}\n";

                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if((boundBody == NULL || boundBody->isFalse()) && solver->currentLevel() == 0){\n";
                                        outfile << ind << "lits.clear();\n";
                                        outfile << ind << "solver->addClause_(lits);\n";
                                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                                    outfile << --ind << "}\n";
                                }
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else{\n";
                            // head is false
                                if(lit->isNegated()){
                                    // false head and negative body literal
                                    // outfile << ind++ << "if(boundBody == NULL || boundBody->isFalse()){\n";
                                    //     #ifdef DEBUG_PROP
                                    //     outfile << ind << "std::cout << \"False head for negative literal true\"<<std::endl;\n";
                                    //     #endif
                                    //     outfile << ind << "solver->clearReasonClause();\n";
                                    //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                    //     outfile << ind << "if(boundBody != NULL) solver->addLiteralToReason(boundBody->getId(),false);\n";
                                    //     printConflict(outfile,ind,false);
                                    // outfile << --ind << "}\n";
                                    // outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";

                                    //     printAddPropagatedToReason(outfile,ind,"boundBody",false);
                                    //         printAddToReason(outfile,ind,"-literal","false");
                                    //         printTuplePropagation(outfile,ind,"boundBody",false,false);
                                    //     outfile << --ind << "}\n";

                                    // outfile << --ind << "}\n";
                                    outfile << ind << "assert(!(boundBody == NULL || boundBody->isFalse()) || solver->currentLevel() == 0);\n";
                                    outfile << ind++ << "if(boundBody != NULL && boundBody->isUndef()){\n";

                                        printAddPropagatedToReason(outfile,ind,"boundBody",false);
                                            printAddToReason(outfile,ind,"-literal","false");
                                            printTuplePropagation(outfile,ind,"boundBody",false,false);
                                        outfile << --ind << "}\n";

                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if( (boundBody == NULL || boundBody->isFalse()) && solver->currentLevel() == 0){\n";
                                        outfile << ind << "lits.clear();\n";
                                        outfile << ind << "solver->addClause_(lits);\n";
                                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                                    outfile << --ind << "}\n";
                                }else{
                                    // false head and positive body literal
                                    // outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                    //     #ifdef DEBUG_PROP
                                    //     outfile << ind << "std::cout << \"False head for bound positive literal true\"<<std::endl;\n";
                                    //     #endif
                                    //     outfile << ind << "solver->clearReasonClause();\n";
                                    //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                    //     outfile << ind << "solver->addLiteralToReason(boundBody->getId(),true);\n";
                                    //     printConflict(outfile,ind,false);
                                    // outfile << --ind << "}\n";
                                    // outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                    //     printAddPropagatedToReason(outfile,ind,"boundBody",true);
                                    //         printAddToReason(outfile,ind,"-literal","false");
                                    //         printTuplePropagation(outfile,ind,"boundBody",true,false);
                                    //     outfile << --ind << "}\n";
                                    // outfile << --ind << "}\n";
                                    outfile << ind << "assert(!(boundBody != NULL && boundBody->isTrue()) || solver->currentLevel() == 0);\n";
                                    outfile << ind++ << "if(boundBody != NULL && boundBody->isUndef()){\n";
                                        printAddPropagatedToReason(outfile,ind,"boundBody",true);
                                            printAddToReason(outfile,ind,"-literal","false");
                                            printTuplePropagation(outfile,ind,"boundBody",true,false);
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue() && solver->currentLevel() == 0){\n";
                                        outfile << ind << "lits.clear();\n";
                                        outfile << ind << "solver->addClause_(lits);\n";
                                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                                    outfile << --ind << "}\n";
                                }
                            outfile << --ind << "}\n";

                        }else{
                            // not bound literal in rule body are positive for sure
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
                            outfile << ind << structType <<" bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType <<" bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind++ << "if(literal > 0){\n";
                            // head is true
                                // outfile << ind++ << "if(bodyTuplesU->size()+bodyTuplesP->size() == 0){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"True head for no positive literal true/undefined\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                //     outfile << ind << "std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                //     outfile << ind << "for(unsigned i =0; i< bodyTuplesF->size(); i++) solver->addLiteralToReason(bodyTuplesF->at(i),false);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){\n";
                                //     //last undef body as true
                                //     outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(0));\n";
                                //     outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                //     outfile << ind++ << "else{\n";
                                        
                                //         printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                //             printAddToReason(outfile,ind,"literal","true");
                                //             outfile << ind << "std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                //             outfile << ind++ << "for(unsigned i = 0; i< bodyTuplesF->size();i++){\n";
                                //                 printAddToReason(outfile,ind,"bodyTuplesF->at(i)","false");
                                //             outfile << --ind << "}\n";
                                //             printTuplePropagation(outfile,ind,"tupleU",false,false);
                                //         outfile << --ind << "}\n";

                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(bodyTuplesU->size()+bodyTuplesP->size() == 0) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){\n";
                                    //last undef body as true
                                    outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(*bodyTuplesU->begin());\n";
                                    outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                    outfile << ind++ << "else{\n";
                                        
                                        printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                            printAddToReason(outfile,ind,"literal","true");
                                            outfile << ind << structType << " bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                                            outfile << ind++ << "for(auto i = bodyTuplesF->begin(); i!= bodyTuplesF->end();i++){\n";
                                                printAddToReason(outfile,ind,"(*i)","false");
                                            outfile << --ind << "}\n";
                                            printTuplePropagation(outfile,ind,"tupleU",false,false);
                                        outfile << --ind << "}\n";

                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(bodyTuplesU->size()+bodyTuplesP->size() == 0 && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else{\n";
                                // // head is false
                                // outfile << ind++ << "if(bodyTuplesP->size() > 0){\n";
                                //     //TODO Fix reason calculus
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"False head for positive literal true\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                //     outfile << ind << "solver->addLiteralToReason(bodyTuplesP->at(0),true);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(bodyTuplesU->size() > 0){\n";
                                // // all undef body as false
                                //     outfile << ind++ << "for(unsigned i = 0; i<bodyTuplesU->size(); i++){\n";
                                //         outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(i));\n";
                                //         outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                //         outfile << ind++ << "else{\n";
                                //             printAddPropagatedToReason(outfile,ind,"tupleU",true);
                                //                 printAddToReason(outfile,ind,"-literal","false");
                                //                 printTuplePropagation(outfile,ind,"tupleU",true,false);
                                //             outfile << --ind << "}\n";
                                //         outfile << --ind << "}\n";
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(bodyTuplesP->size() > 0) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(bodyTuplesU->size() > 0){\n";
                                    // all undef body as false
                                    outfile << ind++ << "for(auto i = bodyTuplesU->begin(); i!=bodyTuplesU->end(); i++){\n";
                                        outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                                        outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                        outfile << ind++ << "else{\n";
                                            printAddPropagatedToReason(outfile,ind,"tupleU",true);
                                                printAddToReason(outfile,ind,"-literal","false");
                                                printTuplePropagation(outfile,ind,"tupleU",true,false);
                                            outfile << --ind << "}\n";
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(bodyTuplesP->size() > 0 && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                        }
                    }else{
                        //TODO head :- ineq
                    }
                    
                    while (closingPars > 0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                    outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
                        outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
                        outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
                        outfile << ind++ << "if(!assigned)\n";
                            outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
                        outfile << ind++ << "else if(foundConflict){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";
            }
            {
                if(body->isLiteral()){
                    std::unordered_set<std::string> headVars;
                    aspc::Literal(false,*head).addVariablesToSet(headVars);
                    const aspc::Literal* lit = (const aspc::Literal*) body;
                    std::unordered_set<std::string> boundVars;
                    outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<< lit->getPredicateName() << "()){\n";
                        outfile << ind << "propagations.clear();\n";
                        unsigned closingPars=0;
                        for(unsigned k=0; k<lit->getAriety();k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = isInteger(lit->getTermAt(k)) || lit->isVariableTermAt(k) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                outfile << ind++ << "if(starter->at("<<k<<") == " <<term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<lit->getTermAt(k) << " = starter->at(" <<k<< ");\n"; 
                                boundVars.insert(lit->getTermAt(k));
                            }
                        }
                        outfile << ind << "Tuple* head=TupleFactory::getInstance().find({";
                        for(unsigned k=0; k<head->getAriety(); k++){
                            if(k>0) outfile << ",";
                            outfile << (head->isVariableTermAt(k) || isInteger(head->getTermAt(k)) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")");
                        }
                        outfile << "}, AuxMapHandler::getInstance().get_"<<head->getPredicateName()<<"());\n";
                        
                        outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head->getId())){\n";
                        closingPars++; 
                        // for safety head is a bounded atom
                        if(lit->isNegated()){
                            //ground literal in the body
                            outfile << ind++ << "if(literal > 0){\n";
                                //body is false
                                // outfile << ind++ << "if(head != NULL && head->isTrue()){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"True head for negative literal false\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                //     outfile << ind << "solver->addLiteralToReason(head->getId(),true);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(head != NULL && head->isUndef()){\n";
                                //     printAddPropagatedToReason(outfile,ind,"head",true);
                                //         printAddToReason(outfile,ind,"literal","true");
                                //         printTuplePropagation(outfile,ind,"head",true,false);
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(head != NULL && head->isTrue()) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(head != NULL && head->isUndef()){\n";
                                    printAddPropagatedToReason(outfile,ind,"head",true);
                                        printAddToReason(outfile,ind,"literal","true");
                                        printTuplePropagation(outfile,ind,"head",true,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if( head != NULL && head->isTrue() && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else{\n";
                                //body is true
                                // outfile << ind++ << "if(head == NULL || head->isFalse()){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"False head for negative literal true\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                //     outfile << ind << "if(head != NULL) solver->addLiteralToReason(head->getId(),false);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(head != NULL && head->isUndef()){\n";
                                //     printAddPropagatedToReason(outfile,ind,"head",false);
                                //         printAddPropagatedToReason(outfile,ind,"-literal","false");
                                //         printTuplePropagation(outfile,ind,"head",false,false);
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(head == NULL || head->isFalse()) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(head != NULL && head->isUndef()){\n";
                                    printAddPropagatedToReason(outfile,ind,"head",false);
                                        printAddToReason(outfile,ind,"-literal","false");
                                        printTuplePropagation(outfile,ind,"head",false,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if((head == NULL || head->isFalse()) && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                            
                        }else if(lit->isBoundedLiteral(headVars)){
                            //unique body for head
                            outfile << ind++ << "if(literal > 0){\n";
                                //body is true
                                // outfile << ind++ << "if(head == NULL || head->isFalse()){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"False head for positive literal true\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                //     outfile << ind << "if(head != NULL) solver->addLiteralToReason(head->getId(),false);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(head != NULL && head->isUndef()){\n";
                                //     printAddPropagatedToReason(outfile,ind,"head",false);
                                //         printAddToReason(outfile,ind,"literal","true");
                                //         printTuplePropagation(outfile,ind,"head",false,false);
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(head == NULL || head->isFalse()) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(head != NULL && head->isUndef()){\n";
                                    printAddPropagatedToReason(outfile,ind,"head",false);
                                        printAddToReason(outfile,ind,"literal","true");
                                        printTuplePropagation(outfile,ind,"head",false,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if((head == NULL || head->isFalse()) && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else{\n";
                                //body is false
                                // outfile << ind++ << "if(head != NULL && head->isTrue()){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"True head for positive literal false\"<<std::endl;\n";
                                //     #endif
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                //     outfile << ind << "solver->addLiteralToReason(head->getId(),true);\n";
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(head != NULL && head->isUndef()){\n";
                                //     printAddPropagatedToReason(outfile,ind,"head",true);
                                //         printAddToReason(outfile,ind,"-literal","false");
                                //         printTuplePropagation(outfile,ind,"head",true,false);
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(head != NULL && head->isTrue()) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(head != NULL && head->isUndef()){\n";
                                    printAddPropagatedToReason(outfile,ind,"head",true);
                                        printAddToReason(outfile,ind,"-literal","false");
                                        printTuplePropagation(outfile,ind,"head",true,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(head != NULL && head->isTrue() && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                        }else{
                            std::string prefix = "AuxMapHandler::getInstance().get_"; 
                            std::string mapName = lit->getPredicateName()+"_";
                            std::string terms = "";
                            std::unordered_set<int> boundIndices;
                            std::string predStruct = predicateToStruct[lit->getPredicateName()];
                            std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                            
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || headVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << structType <<" bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType <<" bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind++ << "if(literal > 0){\n";
                                //body is true
                                // outfile << ind++ << "if(head == NULL || head->isFalse()){\n";
                                //     #ifdef DEBUG_PROP
                                //     outfile << ind << "std::cout << \"True body for false head\"<<std::endl;\n";
                                //     #endif
                                        
                                //     outfile << ind << "solver->clearReasonClause();\n";
                                //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                                //     outfile << ind << "if(head != NULL) solver->addLiteralToReason(head->getId(),false);\n";
                                    
                                //     printConflict(outfile,ind,false);
                                // outfile << --ind << "}\n";
                                // outfile << ind++ << "else if(head != NULL && head->isUndef()){\n";
                                //     printAddPropagatedToReason(outfile,ind,"head",false);
                                //         printAddToReason(outfile,ind,"literal","true");
                                //         printTuplePropagation(outfile,ind,"head",false,false);
                                //     outfile << --ind << "}\n";
                                // outfile << --ind << "}\n";
                                outfile << ind << "assert(!(head == NULL || head->isFalse()) || solver->currentLevel() == 0);\n";
                                outfile << ind++ << "if(head != NULL && head->isUndef()){\n";
                                    printAddPropagatedToReason(outfile,ind,"head",false);
                                        printAddToReason(outfile,ind,"literal","true");
                                        printTuplePropagation(outfile,ind,"head",false,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if((head == NULL || head->isFalse()) && solver->currentLevel() == 0){\n";
                                    outfile << ind << "lits.clear();\n";
                                    outfile << ind << "solver->addClause_(lits);\n";
                                    outfile << ind << "return Glucose::CRef_PropConf;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else{\n";
                                //current body is false
                                outfile << ind++ << "if(head != NULL && head->isTrue()){\n";
                                    //head is true
                                    // outfile << ind++ << "if(bodyTuplesU->size() == 0 && bodyTuplesP->size() == 0){\n";
                                    //     // no other body for head
                                    //     #ifdef DEBUG_PROP
                                    //     outfile << ind << "std::cout << \"No remaining body for true head\"<<std::endl;\n";
                                    //     #endif
                                    //     outfile << ind << "solver->clearReasonClause();\n";
                                    //     outfile << ind << "solver->addLiteralToReason(-literal,false);\n";
                                    //     outfile << ind << "solver->addLiteralToReason(head->getId(),true);\n";
                                    //     outfile << ind << "std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                    //     outfile << ind << "for(unsigned i = 0; i< bodyTuplesF->size(); i++) if(bodyTuplesF->at(i)!= -literal) solver->addLiteralToReason(bodyTuplesF->at(i),false);\n";
                                    //     printConflict(outfile,ind,false);
                                    // outfile << --ind << "}\n";
                                    // outfile << ind++ << "else if(bodyTuplesU->size() == 1 && bodyTuplesP->size() == 0){\n";
                                    //     //last body for true head 
                                    //     outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(0));\n";
                                    //     outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                    //     outfile << ind++ << "else{\n";
                                    //         #ifdef DEBUG_PROP
                                    //         outfile << ind << "std::cout << \"Last remaining body for true head\"<<std::endl;\n";
                                    //         #endif
                                    //         outfile << ind << "std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                    //         printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                    //             printAddToReason(outfile,ind,"-literal","false");
                                    //             outfile << ind++ << "for(unsigned i =0; i< bodyTuplesF->size(); i++){\n";
                                    //                 printAddToReason(outfile,ind,"bodyTuplesF->at(i)","false");
                                    //             outfile << --ind << "}\n";
                                    //             printAddToReason(outfile,ind,"head->getId()","true");
                                    //             printTuplePropagation(outfile,ind,"tupleU",false,false);
                                    //         outfile << --ind << "}\n";
                                    //     outfile << --ind << "}\n";
                                    // outfile << --ind << "}\n";
                                    outfile << ind << "assert(!(bodyTuplesU->size() + bodyTuplesP->size() == 0) || solver->currentLevel() == 0);\n";
                                    outfile << ind++ << "if(bodyTuplesU->size() == 1 && bodyTuplesP->size() == 0){\n";
                                        //last body for true head 
                                        outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(*bodyTuplesU->begin());\n";
                                        outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                        outfile << ind++ << "else{\n";
                                            #ifdef DEBUG_PROP
                                            outfile << ind << "std::cout << \"Last remaining body for true head\"<<std::endl;\n";
                                            #endif
                                            outfile << ind << structType<<" bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                                            
                                            printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                                printAddToReason(outfile,ind,"-literal","false");
                                                outfile << ind++ << "for(auto i = bodyTuplesF->begin(); i != bodyTuplesF->end(); i++){\n";
                                                    outfile << ind << "int reasonLit = *i;\n";
                                                    outfile << ind << "if(reasonLit == -literal) continue;\n";
                                                    printAddToReason(outfile,ind,"reasonLit","false");
                                                outfile << --ind << "}\n";
                                                printAddToReason(outfile,ind,"head->getId()","true");
                                                printTuplePropagation(outfile,ind,"tupleU",false,false);
                                            outfile << --ind << "}\n";
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if(bodyTuplesU->size() + bodyTuplesP->size() == 0 && solver->currentLevel() == 0){\n";
                                        outfile << ind << "lits.clear();\n";
                                        outfile << ind << "solver->addClause_(lits);\n";
                                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(head != NULL && head->isUndef() && bodyTuplesU->size() == 0 && bodyTuplesP->size() == 0){\n";
                                    #ifdef DEBUG_PROP
                                    outfile << ind << "std::cout << \"No remaining body for undefined head\"<<std::endl;\n";
                                    #endif
                                    outfile << ind << structType<<" bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                                    printAddPropagatedToReason(outfile,ind,"head",true);
                                        printAddToReason(outfile,ind,"-literal","false"); 
                                        outfile << ind++ << "for(auto i =bodyTuplesF->begin(); i != bodyTuplesF->end(); i++){\n";
                                            outfile << ind << "int reasonLit = *i;\n";
                                            outfile << ind << "if(reasonLit == -literal) continue;\n";
                                            printAddToReason(outfile,ind,"reasonLit","false");
                                        outfile << --ind << "}\n";
                                        printTuplePropagation(outfile,ind,"head",true,false);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                        }
                        while (closingPars > 0){
                            outfile << --ind << "}\n";
                            closingPars--;
                        }
                        outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
                            outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
                            outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
                            outfile << ind++ << "if(!assigned)\n";
                                outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
                            outfile << ind++ << "else if(foundConflict){\n";
                                outfile << ind << "lits.clear();\n";
                                outfile << ind << "solver->addClause_(lits);\n";
                                outfile << ind << "return Glucose::CRef_PropConf;\n";
                            outfile << --ind << "}\n";
                        outfile << --ind << "}\n";
                    outfile << --ind << "}\n";
                }
            }
        }else{
            auto & ordering = ruleOrdering[ruleId].first;
            const std::vector<const aspc::Formula *>* body = &rule.getFormulas();
            for(unsigned i = 0; i<body->size(); i++){
                if(!body->at(i)->isLiteral()) continue;
                const aspc::Literal* lit = (const aspc::Literal*) body->at(i);
                std::unordered_set<std::string> boundVars;
                
                outfile << ind++ << "if("<<(lit->isPositiveLiteral() ? "literal > 0" : "literal < 0")<<" && starter->getPredicateName() == AuxMapHandler::getInstance().get_"<< lit->getPredicateName() << "()){\n";
                    #ifdef DEBUG_PROP
                    outfile << ind << "std::cout << \" starter "<<i << "\"<<std::endl;\n";
                    #endif
                    if(rule.getSupportAtom() == i){
                        outfile << ind << "if(TupleFactory::getInstance().isFact(starter->getId())) return Glucose::CRef_Undef;\n";
                    }
                    outfile << ind << "propagations.clear();\n";
                    unsigned closingPars=0;
                    for(unsigned k=0; k<lit->getAriety();k++){
                        if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                            std::string term = isInteger(lit->getTermAt(k)) || lit->isVariableTermAt(k) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                            outfile << ind++ << "if(starter->at("<<k<<") == " <<term << "){\n";
                            closingPars++;
                        }else{
                            outfile << ind << "int "<<lit->getTermAt(k) << " = starter->at(" <<k<< ");\n"; 
                            boundVars.insert(lit->getTermAt(k));
                        }
                    }
                    outfile << ind << "Tuple* tupleU = NULL;\n";
                    outfile << ind << "bool tupleUNegated = false;\n";
                    for(unsigned index : ordering[i]){
                        if(!body->at(index)->isLiteral()){
                            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) body->at(index);
                            if(ineq->isBoundedValueAssignment(boundVars)){
                                outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                                boundVars.insert(ineq->getAssignedVariable(boundVars));
                            }else{
                                outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                                closingPars++;
                            }
                        }else{
                            const aspc::Literal* lit = (const aspc::Literal*) body->at(index);
                            if(lit->isBoundedLiteral(boundVars)){
                                outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                                for(unsigned k=0; k<lit->getAriety(); k++){
                                    if(k>0) outfile << ",";
                                    outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                                }
                                outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                                outfile << ind << "bool foundJoin = false;\n";
                                
                                outfile << ind++ << "if(boundBody!=NULL && boundBody->isUndef()){\n";
                                    outfile << ind++ << "if(tupleU == NULL){\n";
                                        outfile << ind << "foundJoin = true;\n";
                                        outfile << ind << "tupleU = boundBody;\n";
                                        if(lit->isNegated())
                                            outfile << ind << "tupleUNegated=true;\n";
                                        else
                                            outfile << ind << "tupleUNegated=false;\n";
                                    --ind;
                                if(lit->isNegated())
                                    outfile << ind++ << "}else if(tupleU->getId() == boundBody->getId() && tupleUNegated){\n";
                                else
                                    outfile << ind++ << "}else if(tupleU->getId() == boundBody->getId() && !tupleUNegated){\n";
                                        outfile << ind << "foundJoin = true;\n";
                                    outfile << --ind << "}\n";    
                                outfile << --ind << "}\n";
                                if(lit->isNegated())
                                    outfile << ind++ << "else if(boundBody == NULL || boundBody->isFalse())\n";
                                else
                                    outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue())\n";
                                        outfile << ind-- << "foundJoin = true;\n";
                                outfile << ind++ << "if(foundJoin){\n";
                                if(rule.getSupportAtom() == index){
                                    outfile << ind++ << "if(boundBody == NULL || !TupleFactory::getInstance().isFact(boundBody->getId())){\n";
                                    closingPars++;
                                }
                                closingPars++;
                                    outfile << ind << "Tuple* tuple_"<<index<<"=boundBody;\n";
                            }else{
                                outfile << ind << "std::vector<int> repeatedTuples;\n";
                                outfile << ind++ << "if(tupleU != NULL && !tupleUNegated && tupleU->getPredicateName() == AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"()){\n";
                                    outfile << ind << "repeatedTuples.push_back(tupleU->getId());\n";
                                outfile << --ind << "}\n";
                                std::string mapName = lit->getPredicateName()+"_";
                                std::string terms = "";
                                std::unordered_set<int> boundIndices;
                                std::string predStruct = predicateToStruct[lit->getPredicateName()];
                                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
                                std::string emptyStruct = predStruct == "Vec" ? "tuplesEmpty" : "tuplesSetEmpty";
                                
                                for(unsigned k=0; k<lit->getAriety(); k++){
                                    if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                        std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                        mapName+=std::to_string(k)+"_";
                                        terms += (terms != "" ? ","+term : term);
                                        boundIndices.insert(k);
                                    }
                                }
                                outfile << ind << structType << " tuplesU_"<<index<<" = tupleU == NULL ? &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"}) : &"<<emptyStruct<<";\n";
                                outfile << ind << structType << " tuples_"<<index<<" = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                                outfile << ind << "auto it"<<index<<" = tuples_"<<index<<"->begin();\n";
                                outfile << ind++ << "for(unsigned i=0; i<tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()+repeatedTuples.size(); i++){\n";
                                closingPars++;
                                    #ifdef DEBUG_PROP
                                    outfile << ind << "std::cout << \" Evaluating "<<index<<"\" << i << \" \" << tuples_"<<index<<"->size()<<std::endl;\n";
                                    #endif
                                        
                                    outfile << ind << "Tuple* tuple_"<<index<<"=NULL;\n";
                                    outfile << ind++ << "if(i < tuples_"<<index<<"->size()){\n";
                                        outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(*it"<<index<<");\n";
                                        outfile << ind << "it"<<index<<"++;\n";
                                        outfile << ind << "if(tuplesU_"<<index<<" != &"<<emptyStruct<<") tupleU=NULL;\n";
                                        if(rule.getSupportAtom() == index){
                                            outfile << ind << "if(TupleFactory::getInstance().isFact(tuple_"<<index<<"->getId())) continue;\n";
                                        }
                                    outfile << --ind << "}\n";
                                    outfile << ind++ << "else if(i < tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()){\n";
                                        outfile << ind << "if(it"<<index<<" == tuples_"<<index<<"->end()) it"<<index<<" = tuplesU_"<<index<<"->begin();\n";
                                        outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(*it"<<index<<");\n";
                                        outfile << ind << "it"<<index<<"++;\n";
                                        outfile << ind << "tupleU=tuple_"<<index<<";\n";
                                        outfile << ind-- << "tupleUNegated=false;\n";
                                    outfile << ind << "}else if(repeatedTuples.size() > 0) tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(repeatedTuples[0]);\n";

                                    outfile << ind++ << "if(tuple_"<<index<<"!= NULL){\n";
                                    closingPars++;
                                for(unsigned k=0; k<lit->getAriety(); k++){
                                    if(lit->isVariableTermAt(k) && !boundVars.count(lit->getTermAt(k))){
                                        outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<index<<"->at("<<k<<");\n";
                                        boundVars.insert(lit->getTermAt(k));
                                    }else{
                                        // TODO: some of this if statement could be omitted if current tuple is not a repeteated tuple
                                        std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                        outfile << ind++ << "if("<< term << " == tuple_"<<index<<"->at("<<k<<")){\n";
                                        closingPars++;
                                    }
                                }
                        
                            }
                        }
                    }
                    #ifdef DEBUG_PROP
                    outfile << ind++ << "if(tupleU == NULL){\n";
                    //     outfile << ind << "solver->clearReasonClause();\n";
                    //     #ifdef DEBUG_PROP
                    //     outfile << ind << "std::cout << \"Violated constraint\"<<std::endl;\n";
                    //     outfile << ind << "AuxMapHandler::getInstance().printTuple(starter);\n";
                    //     #endif
                    //     outfile << ind << "solver->addLiteralToReason(starter->getId(),literal > 0);\n";

                        outfile << ind << "AuxMapHandler::getInstance().printTuple(starter);\n";
                        for(unsigned index : ordering[i]){
                            if(body->at(index)->isLiteral()){
                                outfile << ind << "if(tuple_"<<index<<"!=NULL) AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";        
                            }
                        }
                    //     printConflict(outfile,ind,false);
                    outfile << --ind << "}\n";
                    #endif
                    // ind++;
                    //     printAddPropagatedToReason(outfile,ind,"tupleU",false,true);
                    //         printAddToReason(outfile,ind,"starter->getId()","literal > 0");
                    //         for(unsigned index : ordering[i]){
                    //             if(body->at(index)->isLiteral()){
                    //                 outfile << ind << "if(tuple_"<<index<<" != NULL && tuple_"<<index<<"!=tupleU){\n"; 
                    //                     printAddToReason(outfile,ind,"tuple_"+std::to_string(index)+"->getId()",(body->at(index)->isPositiveLiteral() ? "true":"false"));        
                    //             }
                    //         }
                    //         printTuplePropagation(outfile,ind,"tupleU",false,false,true);
                    //     outfile << --ind << "}\n";
                    // outfile << --ind << "}\n";
                    outfile << ind << "assert(tupleU != NULL || solver->currentLevel() == 0);\n";
                    outfile << ind++ << "if(tupleU != NULL){\n";
                        printAddPropagatedToReason(outfile,ind,"tupleU",false,true);
                            printAddToReason(outfile,ind,"starter->getId()","literal > 0");
                            for(unsigned index : ordering[i]){
                                if(body->at(index)->isLiteral()){
                                    outfile << ind++ << "if(tuple_"<<index<<" != NULL && tuple_"<<index<<"!=tupleU){\n"; 
                                        printAddToReason(outfile,ind,"tuple_"+std::to_string(index)+"->getId()",(body->at(index)->isPositiveLiteral() ? "true":"false"));        
                                    outfile << --ind << "}\n";
                                }
                            }
                            printTuplePropagation(outfile,ind,"tupleU",false,false,true);
                        outfile << --ind << "}\n";
                    outfile << --ind << "}else{\n";
                    ind++;
                        outfile << ind << "lits.clear();\n";
                        outfile << ind << "solver->addClause_(lits);\n";
                        outfile << ind << "return Glucose::CRef_PropConf;\n";
                    outfile << --ind << "}\n";
                    while(closingPars > 0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                    outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
                        outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
                        outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
                        outfile << ind++ << "if(!assigned)\n";
                            outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
                        outfile << ind++ << "else if(foundConflict){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";
                
            }
        }
    }
    outfile << ind << "return Glucose::CRef_Undef;\n";
    outfile << --ind << "}\n";
}
void PropagatorCompiler::printConflict(std::ofstream& outfile,Indentation& ind, bool level0){
    if(level0){
        #ifdef DEBUG_PROP
        outfile << ind << "std::cout << \"Conflict detected at level 0\"<<std::endl;\n";
        #endif
        outfile << ind << "lits.clear();\n";
        outfile << ind << "solver->addClause_(lits);\n";
    }else{
        #ifdef DEBUG_PROP
        outfile << ind << "std::cout << \"Conflict detected in the solver\"<<std::endl;\n";
        #endif
        outfile << ind << "return solver->storeConflictClause();\n";
    }
}

void PropagatorCompiler::printTuplePropagation(std::ofstream& outfile,Indentation& ind, std::string tuplename,bool asFalse,bool level0,bool constraint){
    if(level0){
        outfile << ind << "int var = "<<tuplename<<"->getId();\n";
        if(constraint)
            outfile << ind << "var = tupleUNegated ? var : -var;\n";
        else
            outfile << ind << "var = "<<(asFalse ? "-var" : "var")<< ";\n";    
        outfile << ind << "propagations.push_back((var >= 0) ? Glucose::mkLit(var) : Glucose::mkLit(-var,true));\n";
        outfile << ind << "polarity.push_back(var < 0);\n";
    }else{
        //  foundConflict -> violated clause is in solver
        outfile << ind++ << "if(solver->currentLevel() > 0){\n";
            outfile << ind << "Glucose::CRef clause = solver->externalPropagation("<<tuplename<<"->getId(),var < 0,this);\n";
            outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                outfile << ind-- << "return clause;\n";
        outfile << --ind << "}else{\n";
            outfile << ++ind << "propagations.push_back((var >= 0) ? Glucose::mkLit(var) : Glucose::mkLit(-var,true));\n";
            outfile << ind << "polarity.push_back(var < 0);\n";
        outfile << --ind << "}\n";
    }  
}

void PropagatorCompiler::printAddPropagatedToReason(std::ofstream& outfile,Indentation& ind, std::string tuplename,bool asFalse,bool constraint){
    outfile << ind << "int var = "<<tuplename<<"->getId();\n";
    if(constraint)
        outfile << ind << "var = tupleUNegated ? var : -var;\n";
    else
        outfile << ind << "var = "<<(asFalse ? "-var" : "var")<< ";\n";

    outfile << ind << "bool foundConflict = solver->isConflictPropagation("<<tuplename<<"->getId(),var < 0);\n";
    outfile << ind << "bool assigned = solver->isAssigned("<<tuplename<<"->getId());\n";
    
    outfile << ind++ << "if(!assigned || foundConflict){\n";
        #ifndef PURE_PROP
            outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = solver->getReasonClause();\n";
        #else
            outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? "<<tuplename<<"->getReasonLits() : solver->getReasonClause();\n";
        #endif
        outfile << ind << "propagationReason.clear();\n";
        outfile << ind << "propagationReason.push(Glucose::mkLit("<<tuplename<<"->getId(),var < 0));\n";

    // WARNING print a closing scope after calling this method
}
void PropagatorCompiler::printAddToReason(std::ofstream& outfile,Indentation& ind, std::string var,std::string sign){
    outfile << ind++ << "if(solver->levelFromPropagator("<<var<<")>0)\n";
        outfile << ind-- << "propagationReason.push(Glucose::mkLit("<<var<<","<<sign<<"));\n";
}

void PropagatorCompiler::compileRuleWatcher(unsigned ruleId,std::ofstream& outfile,Indentation& ind){
    outfile << ind << "virtual void printName()const {std::cout << \"External Propagator "<<ruleId<<"\"<<std::endl;}\n";
    outfile << ind++ << "virtual void attachWatched() override {\n";
    #ifdef DEBUG_PROP
    outfile << ind << "std::cout <<\"Attaching watched "<<ruleId<<"\"<<std::endl;\n";
    #endif
    //0 means current propagator not added to watchList
    //1 means current propagator added to positive literal watchList
    //-1 means current propagator added to negative literal watchList
    //2 means current propagator added to both positive and negative literal watchLists
    // outfile << ind << "std::vector<int> watched(TupleFactory::getInstance().size(),0);\n";
    aspc::Rule rule = program.getRule(ruleId);
    const std::vector<const aspc::Formula*>& body = rule.getFormulas();
    bool ruleWithAggregates = rule.containsAggregate();
    if ( false /* OPT_FULL_WATCHED */ ){
        if(!rule.isConstraint()){
            //rules have body of lenght 1
            if(!body[0]->isLiteral()){
                std::cout << "Warning: Rule with only one arithmetic relation in the body"<<std::endl;
            }else{
                const aspc::Atom* head = &rule.getHead()[0];
                const aspc::Literal* lit = (const aspc::Literal*) body[0];
                outfile << ind++ << "{\n";
                    std::string predStruct = predicateToStruct[head->getPredicateName()];
                    std::string predStructLit = predicateToStruct[lit->getPredicateName()];
                    std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
                    std::string structTypeLit = predStructLit == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                    
                    outfile << ind << structType << " tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                    outfile << ind << structType << " tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                    outfile << ind << structType << " tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                    std::unordered_set<std::string> boundVars;
                    outfile << ind++ << "for(auto i = tuplesP->begin(); i != tuplesU->end(); i++){\n";
                    
                        int closingPars=0;
                        // outfile << ind << "int id = i < tuplesP->size() ? tuplesP->at(i) : (i < tuplesP->size()+tuplesF->size() ? tuplesF->at(i - tuplesP->size()) : tuplesU->at(i - tuplesP->size() - tuplesF->size()));\n";
                        
                        outfile << ind << "if(i == tuplesP->end()) i=tuplesF->begin();\n";
                        outfile << ind << "if(i == tuplesF->end()) i=tuplesU->begin();\n";
                        outfile << ind << "if(i == tuplesU->end()) break;\n";
                        outfile << ind << "int id = *i;\n";

                        outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                        for(unsigned k=0; k<head->getAriety(); k++){
                            if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                                std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                boundVars.insert(head->getTermAt(k));
                            }
                        }
                            outfile << ind << "int& watchValue=watched[id];\n";
                            outfile << ind++ << "if(watchValue != 2){\n";
                                outfile << ind << "watchValue = 2;\n";
                                outfile << ind++ << "if(watchValue != 1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                                outfile << ind++ << "if(watchValue != -1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                            outfile << --ind << "}\n";

                        while(closingPars>0){
                            outfile << --ind << "}\n";
                            closingPars--;
                        }
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";

                outfile << ind++ << "{\n";
                    outfile << ind << structTypeLit << " tuplesU = &AuxMapHandler::getInstance().get_u"<<lit->getPredicateName()<<"_()->getValues"<<predStructLit<<"({});\n";
                    outfile << ind << structTypeLit << " tuplesF = &AuxMapHandler::getInstance().get_f"<<lit->getPredicateName()<<"_()->getValues"<<predStructLit<<"({});\n";
                    outfile << ind << structTypeLit << " tuplesP = &AuxMapHandler::getInstance().get_p"<<lit->getPredicateName()<<"_()->getValues"<<predStructLit<<"({});\n";
                    
                    boundVars.clear();
                    outfile << ind++ << "for(auto i = tuplesP->begin(); i != tuplesU->end(); i++){\n";
                    
                        closingPars=0;
                        outfile << ind << "if(i == tuplesP->end()) i=tuplesF->begin();\n";
                        outfile << ind << "if(i == tuplesF->end()) i=tuplesU->begin();\n";
                        outfile << ind << "if(i == tuplesU->end()) break;\n";
                        outfile << ind << "int id = *i;\n";

                        outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = isInteger(lit->getTermAt(k)) || lit->isVariableTermAt(k) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<lit->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                boundVars.insert(lit->getTermAt(k));
                            }
                        }
                            outfile << ind << "int& watchValue=watched[id];\n";
                            outfile << ind++ << "if(watchValue != 2){\n";
                                outfile << ind << "watchValue = 2;\n";
                                outfile << ind++ << "if(watchValue != 1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                                outfile << ind++ << "if(watchValue != -1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                            outfile << --ind << "}\n";
                            
                        while(closingPars>0){
                            outfile << --ind << "}\n";
                            closingPars--;
                        }
                    outfile << --ind << "}\n";
                outfile << "}\n";
            }
        }else{
            std::vector<unsigned> order = ruleOrdering[ruleId].first[body.size()];
            std::unordered_set<std::string> boundVars;
            outfile << ind++ << "{\n";
            unsigned closingPars=1;
                for(unsigned index : order){
                    const aspc::Formula* f = body[index];
                    if(f->isLiteral()){
                        const aspc::Literal* lit = (const aspc::Literal*)f;
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundTuple_"<<index<<"=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                            if(lit->isNegated()){
                                outfile << ind++ << "if(boundTuple_"<<index<<" == NULL || !boundTuple_"<<index<<"->isTrue()){\n";
                            }else{
                                outfile << ind++ << "if(boundTuple_"<<index<<" != NULL && !boundTuple_"<<index<<"->isFalse()){\n";
                            }
                            closingPars++;

                            outfile << ind << "int id_"<<index<<" = boundTuple_"<<index<<" != NULL ? boundTuple_"<<index<<"->getId() : 0;\n";
                            outfile << ind++ << "if(id_"<<index<<">0){\n";
                                outfile << ind << "int& watchValue=watched[id_"<<index<<"];\n";
                                if(lit->isNegated())
                                    outfile << ind++ << "if(watchValue != -1 && watchValue != 2){\n";
                                else
                                    outfile << ind++ << "if(watchValue < 1){\n";

                                    outfile << ind << "watchValue = watchValue != 0 ? 2 : "<<(lit->isNegated() ? -1 : 1)<<";\n";
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id_"<<index<<","<<(lit->isNegated() ? "true" : "false")<<");\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
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
                            outfile << ind << structType << " tuplesU_"<<index<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType << " tuples_"<<index<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind++ << "for(auto i=tuples_"<<index<<"->begin(); i!=tuplesU_"<<index<<"->end(); i++){\n";
                            closingPars++;
                                outfile << ind << "if(i == tuples_"<<index<<"->end()) i=tuplesU_"<<index<<"->begin();\n";
                                outfile << ind << "if(i == tuplesU_"<<index<<"->end()) break;\n";
                                outfile << ind << "int id = *i;\n";
                                outfile << ind << "Tuple* tuple_"<<index<<"= TupleFactory::getInstance().getTupleFromInternalID(id);\n";
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
                            outfile << ind << "int id_"<<index<<" = tuple_"<<index<<"->getId();\n";
                            outfile << ind << "int& watchValue=watched[id_"<<index<<"];\n";
                            outfile << ind++ << "if(watchValue < 1){\n";
                                outfile << ind << "watchValue = watchValue != 0 ? 2 : 1;\n";
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id_"<<index<<",false);\n";
                            outfile << --ind << "}\n";
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
            while(closingPars > 0){
                outfile << --ind << "}\n";
                closingPars--;
            }
        }
    }else{
        std::unordered_map<std::string,int> attached;
        if(!rule.isConstraint()){
            const std::vector<aspc::Atom>* headAtoms = &rule.getHead();
            for(int i=0;i<headAtoms->size();i++){
                const aspc::Atom* head = &headAtoms->at(i);
                std::string predicate = head->getPredicateName();
                std::string predStruct = predicateToStruct[predicate];
                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                auto attachedValue = attached.emplace(predicate,0);
                if(attachedValue.first->second != 2){
                    outfile << ind++ << "{\n";
                        outfile << ind << structType << " tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        outfile << ind << structType << " tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        outfile << ind << structType << " tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        
                        std::unordered_set<std::string> boundVars;
                        outfile << ind++ << "for(auto i = tuplesP->begin(); i != tuplesU->end(); i++){\n";
                        
                            int closingPars=0;
                            outfile << ind << "if(i == tuplesP->end()) i=tuplesF->begin();\n";
                            outfile << ind << "if(i == tuplesF->end()) i=tuplesU->begin();\n";
                            outfile << ind << "if(i == tuplesU->end()) break;\n";
                            outfile << ind << "int id = *i;\n";
                            outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                            for(unsigned k=0; k<head->getAriety(); k++){
                                if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                                    std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                    outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                    closingPars++;
                                }else{
                                    outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                    boundVars.insert(head->getTermAt(k));
                                }
                            }
                            if(attachedValue.first->second != 1)
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                            
                            if(attachedValue.first->second != -1)
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                            
                            attached[predicate]=2;
                            while(closingPars>0){
                                outfile << --ind << "}\n";
                                closingPars--;
                            }
                        outfile << --ind << "}\n";
                    outfile << --ind << "}\n";
                }
            }
        }
        const std::vector<const aspc::Formula*>* body = &rule.getFormulas();
        for(int i=0;i<body->size();i++){
            const aspc::Formula* formula = body->at(i);
            std::vector<aspc::Literal> formulaLiterals; 
            if(formula->isLiteral()){
                if(ruleWithAggregates) continue;
                formulaLiterals.push_back(aspc::Literal(*((const aspc::Literal*)formula)));
            }else if(formula->containsAggregate()){
                const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*) formula;
                const std::vector<aspc::Literal>* aggLits = &aggr->getAggregate().getAggregateLiterals(); 
                for(int litId = 0; litId < aggLits->size(); litId++)
                    formulaLiterals.push_back(aspc::Literal(aggLits->at(litId)));
            }else continue;
            for(int litId = 0; litId < formulaLiterals.size(); litId++){
                const aspc::Literal* lit = &formulaLiterals[litId];
                std::string predicate = lit->getPredicateName();
                std::string predStruct = predicateToStruct[predicate];
                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                auto attachedValue = attached.emplace(predicate,0);
                if(attachedValue.first->second == 2)
                    continue;
                int expected = lit->isNegated() ? -1 : 1;

                if(attachedValue.first->second != expected){
                    outfile << ind++ << "{\n";
                        outfile << ind << structType << " tuplesU = &AuxMapHandler::getInstance().get_u"<<lit->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        outfile << ind << structType << " tuplesF = &AuxMapHandler::getInstance().get_f"<<lit->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        outfile << ind << structType << " tuplesP = &AuxMapHandler::getInstance().get_p"<<lit->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                        
                        std::unordered_set<std::string> boundVars;
                        outfile << ind++ << "for(auto i = tuplesP->begin(); i != tuplesU->end(); i++){\n";
                        
                            int closingPars=0;
                            outfile << ind << "if(i == tuplesP->end()) i=tuplesF->begin();\n";
                            outfile << ind << "if(i == tuplesF->end()) i=tuplesU->begin();\n";
                            outfile << ind << "if(i == tuplesU->end()) break;\n";
                            outfile << ind << "int id = *i;\n";
                            outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                            // for(unsigned k=0; k<lit->getAriety(); k++){
                            //     if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                            //         std::string term = isInteger(lit->getTermAt(k)) || lit->isVariableTermAt(k) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                            //         outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                            //         closingPars++;
                            //     }else{
                            //         outfile << ind << "int "<<lit->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                            //         boundVars.insert(lit->getTermAt(k));
                            //     }
                            // }
                            if(!rule.isConstraint()){
                                if(attachedValue.first->second != 1)
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                                
                                if(attachedValue.first->second != -1)
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                                
                                attached[predicate]=2;
                            }else{
                                if(expected == 1)
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                                else
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                                attached[predicate]= attachedValue.first->second != 0 ? 2 : expected;
                            }
                            
                            while(closingPars>0){
                                outfile << --ind << "}\n";
                                closingPars--;
                            }
                        outfile << --ind << "}\n";
                    outfile << --ind << "}\n";
                }
            }
        }
    }
    
    outfile << --ind << "} //function\n";
}
void PropagatorCompiler::compileRuleLevelZero(unsigned ruleId,std::ofstream& outfile,Indentation& ind){
    
    outfile << ind++ << "virtual void propagateLevelZero(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits) override {\n";
    #ifdef DEBUG_PROP
    outfile << ind << "std::cout <<\"PropagateAtLevel0 "<<ruleId<<"\"<<std::endl;\n";
    #endif
    outfile << ind << "std::vector<Glucose::Lit> propagations;\n";
    outfile << ind << "std::vector<bool> polarity;\n";
    aspc::Rule rule = program.getRule(ruleId);
    const std::vector<const aspc::Formula*>& body = rule.getFormulas();
    if(rule.containsAggregate()){
        compileEagerRuleWithAggregate(ruleId, outfile, ind, false);
    }else{
        if(!rule.isConstraint()){
            //rules have body of lenght 1
            if(!body[0]->isLiteral()){
                std::cout << "Waring: Rule with only one arithmetic relation in the body"<<std::endl;
            }else{
                const aspc::Atom* head = &rule.getHead()[0];
                const aspc::Literal* lit = (const aspc::Literal*) body[0];
                std::string predStruct = predicateToStruct[head->getPredicateName()];
                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                outfile << ind << structType << " tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                outfile << ind << structType << " tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                outfile << ind << structType << " tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValues"<<predStruct<<"({});\n";
                
                {
                    std::unordered_set<std::string> boundVars;
                    int closingPars=0;
                    outfile << ind++ << "for(auto i = tuplesP->begin(); i != tuplesP->end(); i++){\n";
                    closingPars++;
                        outfile << ind << "int id = *i;\n";

                        outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                        outfile << ind++ << "if(tuple != NULL && !TupleFactory::getInstance().isFact(id)){\n";
                        closingPars++;
                        for(unsigned k=0; k<head->getAriety(); k++){
                            if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                                std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                boundVars.insert(head->getTermAt(k));
                            }
                        }
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                            
                            if(lit->isNegated()){
                                outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                    printConflict(outfile,ind,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                    printTuplePropagation(outfile,ind,"boundBody",true,true);
                                outfile << --ind << "}\n";
                                
                            }else{
                                outfile << ind++ << "if(boundBody == NULL || boundBody->isFalse()){\n";
                                    printConflict(outfile,ind,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                    printTuplePropagation(outfile,ind,"boundBody",false,true);
                                outfile << --ind << "}\n";
                            }
                        }else{
                            // not bound literal in rule body are positive for sure
                            std::string prefix = "AuxMapHandler::getInstance().get_"; 
                            std::string mapName = lit->getPredicateName()+"_";
                            std::string terms = "";
                            std::unordered_set<int> boundIndices;
                            std::string predToStruct = predicateToStruct[lit->getPredicateName()];
                            std::string structType = predToStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
                            
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << structType << " bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType << " bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            
                            outfile << ind++ << "if(bodyTuplesU->size()+bodyTuplesP->size() == 0){\n";
                                printConflict(outfile,ind,true);
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){\n";
                                outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(*bodyTuplesU->begin());\n";
                                outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                outfile << ind++ << "else{\n";
                                    printTuplePropagation(outfile,ind,"tupleU",false,true);
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";

                        }
                    while (closingPars > 0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                }
                {
                    std::unordered_set<std::string> boundVars;
                    int closingPars=0;
                    outfile << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                    closingPars++;
                        outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                        outfile << ind++ << "if(tuple != NULL){\n";
                        closingPars++;
                        for(unsigned k=0; k<head->getAriety(); k++){
                            if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                                std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                boundVars.insert(head->getTermAt(k));
                            }
                        }
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                            if(lit->isNegated()){
                                // false head and negative body literal
                                outfile << ind++ << "if(boundBody == NULL || boundBody->isFalse()){\n";
                                    printConflict(outfile,ind,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                    printTuplePropagation(outfile,ind,"boundBody",false,true);
                                outfile << --ind << "}\n";
                                
                            }else{
                                // false head and positive body literal
                                outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                    printConflict(outfile,ind,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                    printTuplePropagation(outfile,ind,"boundBody",true,true);
                                outfile << --ind << "}\n";
                            }
                        }else{
                            // not bound literal in rule body are positive for sure
                            std::string prefix = "AuxMapHandler::getInstance().get_"; 
                            std::string mapName = lit->getPredicateName()+"_";
                            std::string terms = "";
                            std::unordered_set<int> boundIndices;
                            std::string predToStruct = predicateToStruct[lit->getPredicateName()];
                            std::string structType = predToStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << structType << " bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType << " bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            
                            outfile << ind++ << "if(bodyTuplesP->size() > 0){\n";
                                printConflict(outfile,ind,true);
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(bodyTuplesU->size() > 0){\n";
                                #ifdef DEBUG_PROP
                                outfile << ind << "std::cout << \"Propagating all undefined as false\" <<std::endl;\n";
                                #endif
                                        
                                outfile << ind++ << "for(auto i = bodyTuplesU->begin(); i != bodyTuplesU->end(); i++){\n";
                                    outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                                    outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                    outfile << ind++ << "else{\n";
                                        printTuplePropagation(outfile,ind,"tupleU",true,true);
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                        }
                    while (closingPars > 0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                }
                {
                    std::unordered_set<std::string> boundVars;
                    int closingPars=0;
                    outfile << ind++ << "for(auto i = tuplesU->begin(); i != tuplesU->end(); i++){\n";
                    closingPars++;
                        outfile << ind << "int id = *i;\n";

                        outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                        outfile << ind++ << "if(tuple != NULL){\n";
                        closingPars++;
                        for(unsigned k=0; k<head->getAriety(); k++){
                            if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                                std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                                outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                                closingPars++;
                            }else{
                                outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                                boundVars.insert(head->getTermAt(k));
                            }
                        }
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";

                            if(lit->isNegated()){
                                // undef head and negative body literal
                                outfile << ind++ << "if(boundBody == NULL || boundBody->isFalse()){\n";
                                    printTuplePropagation(outfile,ind,"tuple",false,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue()){\n";
                                    printTuplePropagation(outfile,ind,"tuple",true,true);
                                outfile << --ind << "}\n";
                                
                            }else{
                                // undef head and positive body literal
                                outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                    printTuplePropagation(outfile,ind,"tuple",false,true);
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(boundBody == NULL && boundBody->isFalse()){\n";
                                    printTuplePropagation(outfile,ind,"tuple",true,true);
                                outfile << --ind << "}\n";
                            }
                        }else{
                            // not bound literal in rule body are positive for sure
                            std::string prefix = "AuxMapHandler::getInstance().get_"; 
                            std::string mapName = lit->getPredicateName()+"_";
                            std::string terms = "";
                            std::unordered_set<int> boundIndices;
                            std::string predToStruct = predicateToStruct[lit->getPredicateName()];
                            std::string structType = predToStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
                            
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << structType << " bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            outfile << ind << structType << " bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predToStruct<<"({"<<terms<<"});\n";
                            
                            outfile << ind++ << "if(bodyTuplesP->size() > 0){\n";
                                printTuplePropagation(outfile,ind,"tuple",false,true);
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(bodyTuplesU->size() == 0){\n";
                                printTuplePropagation(outfile,ind,"tuple",true,true);
                            outfile << --ind << "}\n";
                        }
                    while (closingPars > 0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                }
            }
        }else{
            std::vector<unsigned> order = ruleOrdering[ruleId].first[body.size()];
            std::unordered_set<std::string> boundVars;
            outfile << ind++ << "{\n";
            int closingPars = 1;
                outfile << ind << "Tuple* tupleU = NULL;\n";
                outfile << ind << "bool tupleUNegated = false;\n";
                for(unsigned index : order){
                    if(!body[index]->isLiteral()){
                        const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) body[index];
                        if(ineq->isBoundedValueAssignment(boundVars)){
                            outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                            boundVars.insert(ineq->getAssignedVariable(boundVars));
                        }else{
                            outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                            closingPars++;
                        }
                    }else{
                        const aspc::Literal* lit = (const aspc::Literal*) body[index];
                        if(lit->isBoundedLiteral(boundVars)){
                            outfile << ind << "Tuple* boundBody=TupleFactory::getInstance().find({";
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(k>0) outfile << ",";
                                outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                            }
                            outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";

                            outfile << ind << "bool foundJoin = false;\n";
                            outfile << ind++ << "if(boundBody!=NULL && boundBody->isUndef()){\n";
                                outfile << ind++ << "if(tupleU == NULL){\n";
                                    outfile << ind << "foundJoin = true;\n";
                                    outfile << ind << "tupleU = boundBody;\n";
                                    if(lit->isNegated())
                                        outfile << ind << "tupleUNegated=true;\n";
                                    else
                                        outfile << ind << "tupleUNegated=false;\n";
                                --ind;
                            if(lit->isNegated())
                                outfile << ind++ << "}else if(tupleU->getId() == boundBody->getId() && tupleUNegated){\n";
                            else
                                outfile << ind++ << "}else if(tupleU->getId() == boundBody->getId() && !tupleUNegated){\n";
                                    outfile << ind << "foundJoin = true;\n";
                                outfile << --ind << "}\n";    
                            outfile << --ind << "}\n";
                            if(lit->isNegated())
                                outfile << ind++ << "else if(boundBody == NULL || boundBody->isFalse())\n";
                            else
                                outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue())\n";
                                    outfile << ind-- << "foundJoin = true;\n";
                            outfile << ind++ << "if(foundJoin){\n";
                            closingPars++;
                                if(rule.getSupportAtom() == index){
                                    outfile << ind++ << "if(boundBody == NULL || !TupleFactory::getInstance().isFact(boundBody->getId())){\n";
                                    closingPars++;
                                }
                                outfile << ind << "Tuple* tuple_"<<index<<"=boundBody;\n";
                        }else{
                            outfile << ind << "std::vector<int> repeatedTuples;\n";
                            outfile << ind++ << "if(tupleU != NULL && !tupleUNegated && tupleU->getPredicateName() == AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"()){\n";
                                outfile << ind << "repeatedTuples.push_back(tupleU->getId());\n";
                            outfile << --ind << "}\n";
                            std::string mapName = lit->getPredicateName()+"_";
                            std::string terms = "";
                            std::unordered_set<int> boundIndices;
                            std::string predStruct = predicateToStruct[lit->getPredicateName()];
                            std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
                            std::string emptyStruct = predStruct == "Vec" ? "tuplesEmpty" : "tuplesSetEmpty";

                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << structType << " tuplesU_"<<index<<" = tupleU == NULL ? &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"}) : &"<<emptyStruct<<";\n";
                            outfile << ind << structType << " tuples_"<<index<<" = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                            outfile << ind << "auto it"<<index<<" = tuples_"<<index<<"->begin();\n";
                            outfile << ind++ << "for(unsigned i=0; i<tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()+repeatedTuples.size(); i++){\n";
                            closingPars++;
                                outfile << ind << "Tuple* tuple_"<<index<<"=NULL;\n";
                                outfile << ind++ << "if(i < tuples_"<<index<<"->size()){\n"; 
                                    outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(*it"<<index<<");\n";
                                    outfile << ind << "it"<<index<<"++;\n";
                                    // outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(tuples_"<<index<<"->at(i));\n";
                                    outfile << ind << "if(tuplesU_"<<index<<" != &"<<emptyStruct<<") tupleU=NULL;\n";
                                    if(rule.getSupportAtom() == index){
                                        outfile << ind << "if(TupleFactory::getInstance().isFact(tuple_"<<index<<"->getId())) continue;\n";
                                    }
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(i < tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()){\n";
                                    outfile << ind << "if(it"<<index<<" == tuples_"<<index<<"->end()) it"<<index<<"=tuplesU_"<<index<<"->begin();\n";
                                    outfile << ind << "if(it"<<index<<" == tuplesU_"<<index<<"->end()) {assert(false);}\n";
                                    outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(*it"<<index<<");\n";
                                    outfile << ind << "it"<<index<<"++;\n";
                                    outfile << ind << "tupleU=tuple_"<<index<<";\n";
                                    outfile << ind-- << "tupleUNegated=false;\n";
                                outfile << ind << "}else if(repeatedTuples.size() > 0) tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(repeatedTuples[0]);\n";

                                outfile << ind++ << "if(tuple_"<<index<<"!= NULL){\n";
                                closingPars++;
                                    
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(lit->isVariableTermAt(k) && !boundVars.count(lit->getTermAt(k))){
                                    outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<index<<"->at("<<k<<");\n";
                                    boundVars.insert(lit->getTermAt(k));
                                }else{
                                    // TODO: some of this if statement could be omitted if current tuple is not a repeteated tuple
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    outfile << ind++ << "if("<< term << " == tuple_"<<index<<"->at("<<k<<")){\n";
                                    closingPars++;
                                }
                            }
                    
                        }
                    }
                }
                outfile << ind++ << "if(tupleU == NULL){\n";
                    printConflict(outfile,ind,true);
                    #ifdef DEBUG_PROP
                        outfile << ind << "std::cout << \"Violated constraint\"<<std::endl;\n";
                        for(unsigned index : order){
                            if(body[index]->isLiteral()){
                                outfile << ind << "if(tuple_"<<index<<" != NULL){AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");}\n";        
                            }
                        }
                    #endif
                outfile << --ind << "}else{\n";
                    #ifdef DEBUG_PROP
                    outfile << ++ind << "std::cout << \"Building unit clause for level 0\" << std::endl;\n";
                    #endif
                    printTuplePropagation(outfile,ind,"tupleU",false,true,true);
                    #ifdef DEBUG_PROP
                    outfile << ind << "std::cout << \"Propagating body literal as false\" <<std::endl;\n";
                    #endif
                outfile << --ind << "}\n";
            while (closingPars > 0){
                outfile << --ind << "}\n";
                closingPars--;
            }
        }
    }
        outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
            outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
            outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
            outfile << ind++ << "if(!assigned)\n";
                outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
            outfile << ind++ << "else if(foundConflict){\n";
                outfile << ind << "lits.clear();\n";
                outfile << ind << "solver->addClause_(lits);\n";
                outfile << ind << "return;\n";
            outfile << --ind << "}\n";
        outfile << --ind << "}\n";
    outfile << --ind << "} //function\n";
}
void PropagatorCompiler::computePropagatorOrder(){
    
    int programSize = program.getRulesSize();
    for(unsigned ruleId = 0; ruleId < programSize; ruleId++){
        propagatorOrder.push_back(ruleId);
    }
}
void PropagatorCompiler::compile(){
    buildAuxMapHandler();
    computePropagatorOrder();
    for(unsigned ruleId : propagatorOrder){
        Indentation ind(0);
        std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
        std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/propagators/"+className+".h";
        std::ofstream outfile(executorPath);
        if(!outfile.is_open()){
            std::cout << "Error unable to open "+className+" file "<<executorPath<<std::endl;
            exit(180);
        } 
        outfile << ind << "#ifndef "<<className<<"_H\n";
        outfile << ind << "#define "<<className<<"_H\n";

        outfile << ind << "#include <vector>\n";
        outfile << ind << "#include \"../datastructures/TupleFactory.h\"\n";
        outfile << ind << "#include \"../datastructures/AuxiliaryMapSmart.h\"\n";
        outfile << ind << "#include \"../solver/AuxMapHandler.h\"\n";
        outfile << ind << "#include \"../solver/AbstractPropagator.h\"\n";
        outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
        outfile << ind << "#include \"../datastructures/VectorAsSet.h\"\n";
        // outfile << ind << "#include \"../../core/Solver.h\"\n";
        outfile << ind << "typedef TupleLight Tuple;\n";
        outfile << ind << "template<size_t S>\n";
        outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

        outfile << ind++ << "class "<<className<<": public AbstractPropagator{\n";
            outfile << ind << "std::vector<int> tuplesEmpty;\n";
            outfile << ind << "IndexedSet tuplesSetEmpty;\n";
            outfile << ind++ << "public:\n";
                outfile << ind << className << "(){}\n";
                compileRuleLevelZero(ruleId,outfile,ind);
                compileRuleFromStarter(ruleId,outfile,ind);
                compileRuleWatcher(ruleId,outfile,ind);
            --ind;
        outfile << --ind << "};\n";
        outfile << ind << "#endif\n";
    }    
    
    
    Indentation ind(0);
    std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/propagators/Propagator.cc";
    std::ofstream outfile(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open Generator file "<<executorPath<<std::endl;
        exit(180);
    } 

    outfile << ind << "#include \"../solver/Propagator.h\"\n\n";
    for(unsigned ruleId=0; ruleId < program.getRulesSize(); ruleId++){
        std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
        outfile << ind << "#include \"../propagators/"<<className<<".h\"\n\n";
    }
    outfile << ind++ << "Propagator::Propagator(){\n";
        outfile << ind << "active=false;\n";
        outfile << ind << "fullGrounding=true;\n";
        outfile << ind << "unsigned id = 0;\n";
        int propagatorId = 0;
        for(unsigned ruleId : propagatorOrder){
            std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
            outfile << ind << "propagators.push_back(new "<<className<<"());\n";
            outfile << ind << "propagators.back()->setId("<<propagatorId<<");\n";
            propagatorId++;
        }
    outfile << --ind << "}\n";

    printUpdateSum(outfile,ind,true);
    printUpdateSum(outfile,ind,false);
    outfile.close();

    
}
void PropagatorCompiler::printUpdateSum(std::ofstream& outfile, Indentation& ind, bool undef){
    outfile << ind++ << "void Propagator::updateSumFor"<<(undef ? "Undef" : "True")<<"Lit(Tuple* starter"<<(undef ? ", TruthStatus prevVal" : "")<<"){\n";
    for(unsigned ruleId=0; ruleId<program.getRulesSize(); ruleId++){
        const aspc::Rule* rule = & program.getRule(ruleId);
        if(rule->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* aggregate = &rule->getArithmeticRelationsWithAggregate()[0];
            if(!aggregate->getAggregate().isSum()) continue;
            
            const aspc::Literal* aggSet = &aggregate->getAggregate().getAggregateLiterals()[0]; 
            const aspc::Atom* aggID = &rule->getHead()[0];
            std::vector<unsigned> sharedVarAggrID;
            std::unordered_set<std::string> aggrSetVars;
            aggSet->addVariablesToSet(aggrSetVars);
            for(unsigned k = 0; k < aggID->getAriety(); k++){
                if(aggID->isVariableTermAt(k) && aggrSetVars.count(aggID->getTermAt(k))){
                    sharedVarAggrID.push_back(k);
                }
            }

            std::vector<unsigned> sharedVarAggrSet;
            std::unordered_set<std::string> aggrIdVars;
            aspc::Literal(false,*aggID).addVariablesToSet(aggrIdVars);
            for(unsigned k = 0; k < aggSet->getAriety(); k++){
                if(aggSet->isVariableTermAt(k) && aggrIdVars.count(aggSet->getTermAt(k))){
                    sharedVarAggrSet.push_back(k);
                }
            }
            std::string firstAggrVar = aggregate->getAggregate().getAggregateVariables()[0];
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<aggSet->getPredicateName()<<"()){\n"; 
            std::unordered_set<std::string> boundVariables;
            unsigned pars=1;
            for(unsigned i = 0; i<aggSet->getAriety(); i++){
                std::string term = aggSet->isVariableTermAt(i) || isInteger(aggSet->getTermAt(i)) ? aggSet->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggSet->getTermAt(i)+"\")"; 
                if(aggSet->isVariableTermAt(i) && boundVariables.count(aggSet->getTermAt(i))==0){
                    outfile << ind << "int "<<aggSet->getTermAt(i)<<" = starter->at("<<i<<");\n";
                    boundVariables.insert(aggSet->getTermAt(i));
                }else{
                    outfile << ind++ << "if("<<term<<" == starter->at("<<i<<")){\n";
                    pars++;
                }
            }
            
                
                
                if(sharedVarAggrID.size() < aggID->getAriety()){
                    outfile << ind << "std::vector<int> sharedVar({";
                    bool first=true;
                    for(unsigned i : sharedVarAggrSet){
                        if(first)
                            first=false;
                        else outfile <<",";
                        outfile << "starter->at("<<i<<")";
                    }
                    outfile << "});\n";
                    auxMapCompiler->addAuxMap(aggID->getPredicateName(),sharedVarAggrID);
                    outfile << ind << "std::vector<int>* tuples = &AuxMapHandler::getInstance().get_p"<<aggID->getPredicateName()<<"_";
                    for(unsigned k : sharedVarAggrID){
                        outfile << k << "_" ;
                    }
                    outfile<<"()->getValuesVec({sharedVar});\n";
                    outfile << ind << "std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<aggID->getPredicateName()<<"_";
                    for(unsigned k : sharedVarAggrID){
                        outfile << k << "_";
                    }
                    outfile<<"()->getValuesVec({sharedVar});\n";
                    outfile << ind << "std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<aggID->getPredicateName()<<"_";
                    for(unsigned k : sharedVarAggrID){
                        outfile << k << "_";
                    }
                    outfile<<"()->getValuesVec({sharedVar});\n";
                    outfile << ind++ << "for(unsigned i = 0; i < tuples->size()+tuplesU->size()+tuplesF->size(); i++){\n";
                    pars++;
                        outfile << ind << "int aggId = i<tuples->size() ? tuples->at(i) : (i-tuples->size() < tuplesU->size() ? tuplesU->at(i-tuples->size()) : tuplesF->at(i-tuples->size()-tuplesU->size()));\n";
                        outfile << ind << "Tuple* aggregate = TupleFactory::getInstance().getTupleFromInternalID(aggId);\n";
                }else{
                    outfile << ind << "Tuple* aggregate = TupleFactory::getInstance().find({";
                    for(unsigned i = 0; i<aggID->getAriety(); i++){
                        std::string term = aggID->isVariableTermAt(i) || isInteger(aggID->getTermAt(i)) ? aggID->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggID->getTermAt(i)+"\")"; 
                        if(i>0) outfile << ",";
                        outfile << term;
                    }
                    outfile << "},AuxMapHandler::getInstance().get_"<<aggID->getPredicateName()<<"());\n";
                    outfile << ind++ << "if(aggregate != NULL){\n";
                    pars++;
                }
                    if(!undef){
                        outfile << ind << "if(starter->isTrue()) TupleFactory::getInstance().incrementActualSumForLit(aggregate->getId(),"<<firstAggrVar<<");\n";
                        outfile << ind << "TupleFactory::getInstance().decrementPossibleSumForLit(aggregate->getId(),"<<firstAggrVar<<");\n";
                    }else{
                        outfile << ind << "if(prevVal == True) TupleFactory::getInstance().decrementActualSumForLit(aggregate->getId(),"<<firstAggrVar<<");\n";
                        outfile << ind << "TupleFactory::getInstance().incrementPossibleSumForLit(aggregate->getId(),"<<firstAggrVar<<");\n";
                    }
                    
            while (pars>0){
                outfile << --ind << "}\n"; 
                pars--;
            }
        }
    }
    outfile << --ind << "}\n"; 
}
void PropagatorCompiler::buildAuxMapHandler(){
    for(unsigned ruleId=0; ruleId < program.getRulesSize(); ruleId++){
        ruleOrdering.push_back(auxMapCompiler->declarePropagatorDataStructure(program.getRule(ruleId)));
    }
}

void PropagatorCompiler::buildPositiveDG(){
    std::cout << "Error: calling dismissed method"<<std::endl;
    exit(180);
}
void PropagatorCompiler::computeSCC(){
    std::cout << "Error: calling dismissed method"<<std::endl;
    exit(180);
}

void PropagatorCompiler::compileEagerRuleWithCount(unsigned ruleId, std::ofstream& outfile, Indentation& ind,bool fromStarter){

    const aspc::Rule& r = program.getRule(ruleId);
    const aspc::Literal* bodyPred = !r.getBodyLiterals().empty() ? &r.getBodyLiterals()[0] : NULL;
    const aspc::Literal* aggrSetPred = &r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
    const aspc::Atom* aggrIdAtom = &r.getHead()[0];
    const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &r.getArithmeticRelationsWithAggregate()[0];

    std::vector<unsigned> sharedVarAggrIDToBodyIndices;
    std::unordered_set<std::string> aggrSetVars;
    aggrSetPred->addVariablesToSet(aggrSetVars);
    for(unsigned k = 0; k < aggrIdAtom->getAriety(); k++){
        if(aggrIdAtom->isVariableTermAt(k) && aggrSetVars.count(aggrIdAtom->getTermAt(k))){
            sharedVarAggrIDToBodyIndices.push_back(k);
        }
    }
    auxMapCompiler->addAuxMap(aggrIdAtom->getPredicateName(),sharedVarAggrIDToBodyIndices);
    auxMapCompiler->addAuxMap(aggrIdAtom->getPredicateName(),{});

    std::vector<unsigned> sharedVarAggrIDToAggrSetIndices;
    std::unordered_set<std::string> aggrIdVars;
    aspc::Literal(false,*aggrIdAtom).addVariablesToSet(aggrIdVars);
    for(unsigned k = 0; k < aggrSetPred->getAriety(); k++){
        if(aggrSetPred->isVariableTermAt(k) && aggrIdVars.count(aggrSetPred->getTermAt(k))){
            sharedVarAggrIDToAggrSetIndices.push_back(k);
        }
    }

    auxMapCompiler->addAuxMap(aggrSetPred->getPredicateName(),sharedVarAggrIDToAggrSetIndices);
    auxMapCompiler->addAuxMap(aggrSetPred->getPredicateName(),{});
    // std::cout<<"Compile eager rule with aggr"<<std::endl;
    if(fromStarter){
        {
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<aggrIdAtom->getPredicateName()<<"()){\n";
            #ifdef TRACE_PROP_GEN
            outfile << ind << "std::cout<<\"Prop rule with aggr\"<<std::endl;\n";
            #endif
            std::unordered_set<std::string> boundVariables;
            unsigned pars=0;
            for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                    outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = starter->at("<<i<<");\n";
                    boundVariables.insert(aggrIdAtom->getTermAt(i));
                }else{
                    outfile << ind++ << "if("<<term<<" == starter->at("<<i<<")){\n";
                    pars++;
                }
            }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";
                        outfile << "starter->at("<<i<<")";
                    }
                }

                outfile << "});\n";

                std::string mapName=aggrSetPred->getPredicateName()+"_";
                for(unsigned i : sharedVarAggrIDToAggrSetIndices){
                    mapName+=std::to_string(i)+"_";
                }
                std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
                std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
                
                outfile << ind << "const IndexedSet* tuples = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* tuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind << "int startVar = literal;\n",
                outfile << ind << "int uStartVar = literal>0 ? literal : -literal;\n",
                outfile << ind++ << "if(startVar < 0){\n";

                    outfile << ind++ << "if(tuples->size()>="<<guard<<"){\n";
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                       // %%%%%%%%%% HANDLE CONFLICT %%%%%%%%%%
                       outfile << ind << "std::cout << \"Unexpected rule violation: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                       outfile << ind << "assert(false);\n";
                       // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                    outfile << --ind << "}else if(tuples->size() == "<<guard<<" -1){\n";
                    ind++;

                        // %%%%%%%%%% PROPAGATING AGGREGATE SET AS FALSE %%%%%%%%%%

                        outfile << ind++ << "for(auto i = tuplesU->begin(); i != tuplesU->end(); i++){\n";
                            outfile << ind << "int itProp = *i;\n";
                            outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(itProp);\n";
                        
                            // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS FALSE %%%%%%%%%%
                            //
                            // itProp is the id of aggreset undefined
                            // currentTuple is the undefined aggreset tuple
                        
                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,true);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";
                                    
                                    // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%
                        
                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";

                                        // startVar < 0 -> clause contains aggId as positive
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-startVar));\n";
                                        outfile << ind++ << "for(auto i = tuples->begin(); i != tuples->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // true aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                    
                                    // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp,true);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,true,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(itProp,true));}\n";

                            // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                        outfile << --ind << "}\n";
                        // }
                    outfile << --ind << "}\n";
                outfile << --ind << "}else{\n";
                ind++;
                    outfile << ind++ << "if(tuples->size()+tuplesU->size() < "<<guard<<"){\n";
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Unexpected rule violation: violated rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    
                    outfile << --ind << "}else if(tuples->size() + tuplesU->size() == "<<guard<<"){\n";
                    ind++;

                        // %%%%%%%%%% PROPAGATING AGGREGATE SET AS TRUE %%%%%%%%%%
                    
                        outfile << ind++ << "for(auto index=tuplesU->begin();index != tuplesU->end();index++){\n";
                            outfile << ind << "int itProp = *index;\n";
                            outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(itProp);\n";
                        
                            // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS TRUE %%%%%%%%%%
                            //
                            // itProp is the id of aggreset undefined
                            // currentTuple is the undefined aggreset tuple

                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,false);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";
                                    
                                    // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";

                                        // startVar > 0 -> clause contains aggId as negative
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(startVar,true));\n";
                                        outfile << ind << "const IndexedSet* tuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                        outfile << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // false aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                        outfile << --ind << "}\n";
                                    outfile << --ind << "}\n";
                                    
                                    // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,false,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(itProp));}\n";

                        outfile << --ind << "}\n";
                    
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";
                while (pars>0){
                    outfile << --ind << "}\n";
                    pars--;
                }
                
            outfile << --ind << "}//close aggr id starter\n";
            // std::cout<<"Compiled starter aggr id"<<std::endl;
        }
    }
    {
        if(fromStarter)
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<aggrSetPred->getPredicateName()<<"()){\n";
        else outfile << ind++ << "{\n";

        // outfile << ind << "std::cout<<\"Propagation start from aggr_set\"<<std::endl;\n";
        std::string mapName=aggrSetPred->getPredicateName()+"_";
        for(unsigned i : sharedVarAggrIDToAggrSetIndices){
            mapName+=std::to_string(i)+"_";
        }
        std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
        std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
            outfile << ind << "const std::vector<int>* tuples  = &AuxMapHandler::getInstance().get_p"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            // OPTIMIZATION Add if starter.isNegated
            // outfile << ind << "std::cout<<\"Prop for true head\"<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId true size: \"<<tuples->size()<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId undef size: \"<<tuplesU->size()<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId false size: \"<<tuplesF->size()<<std::endl;\n";

            outfile << ind++ << "for(unsigned i = 0; i<tuples->size(); i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuples->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                        std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                        if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                            outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                            boundVariables.insert(aggrIdAtom->getTermAt(i));
                        }else{
                            outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                            pars++;
                        }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";

                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples =  &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";

                outfile << ind << "int aggrIdIt=tuples->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind++ << "if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                    if(fromStarter){
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Violated rule: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    }else{
                        printConflict(outfile,ind,true);
                    }
                outfile << --ind << "}else if(joinTuples->size() + joinTuplesU->size() == "<<guard<<"){\n";
                ind++;
                    
                   outfile << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                        outfile << ind << "int itProp = *index;\n";
                        outfile << ind << "Tuple* currentJoinTuple = TupleFactory::getInstance().getTupleFromInternalID(itProp);\n";

                        if(fromStarter){
                        
                            // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS TRUE %%%%%%%%%%
                            //
                            // itProp is the id of aggreset undefined
                            // currentJoinTuple is the undefined aggreset tuple
                            // currentTuple is the aggId tuple

                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,false);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";

                                    // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                    outfile << ind << "assert(literal < 0);\n";
                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";

                                        // literal < 0 -> aggSet false
                                        outfile << ind << "bool found_starter=false;\n";

                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-literal));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(currentTuple->getId(),true));\n";
                                        outfile << ind << "const IndexedSet* joinTuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                        outfile << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // false aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != -literal) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                            outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == -literal) found_starter = true;\n";
                                        outfile << --ind << "}\n";
                                        outfile << ind << "assert(found_starter);\n";
                                    outfile << --ind << "}\n";
                                    
                                    // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentJoinTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,false,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(itProp));}\n";

                        }else{
                            // tupleU       -> TupleFactory::getInstance().getTupleFromInternalID(joinTuplesU->at(index))
                            // isNegated    -> false
                            // asNegative   -> false
                            outfile << ind << "{polarity.push_back(false);propagations.push_back(Glucose::mkLit(itProp));}\n";
                        }
                        
                    outfile << --ind << "} //close for joinTuplesU\n";
                outfile << --ind << "} //close else\n";
                while(pars>0){
                    pars--;
                    outfile << --ind << "}\n";
                }
            }
            outfile << --ind << "}//close true for\n";
            //OPTIMIZATION Add if !starter.isNegated

            // outfile << ind << "std::cout<<\"Prop for false head\"<<std::endl;\n";
            outfile << ind++ << "for(unsigned i = 0; i<tuplesF->size(); i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesF->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred != NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";

                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples = & AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "int aggrIdIt=tuplesF->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";

                // outfile << ind << "std::cout<<\"ActualSum: \"<<actualSum[aggrIdIt]<<std::endl;\n";
                // outfile << ind << "if(aggrIdIt == tupleToVar.end()) {std::cout<<\"Unable to find aggr id\"<<std::endl; continue;}\n";

                outfile << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";
                    //outfile << ind << "std::cout<<\"Conflitct on aggregate starting from false aggr id "<<r.getRuleId()<<"\"<<actualSum[aggrIdIt]<<std::endl;\n";
                    if(fromStarter){
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Violated rule: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    }else{
                        printConflict(outfile,ind,true);
                    }
                outfile << -- ind << "}else if(joinTuples->size() == "<<guard<<" -1){\n";
                ind++;
                    
                    outfile << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                        outfile << ind << "Tuple* currentJoinTuple = TupleFactory::getInstance().getTupleFromInternalID(*index);\n";
                        outfile << ind << "int itProp = *index;\n";

                        if(fromStarter){

                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,true);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";
                                    
                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                        
                                        outfile << ind << "bool found_starter=false;\n";
                                        // literal > 0 -> aggSet true
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(literal,true));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(currentTuple->getId()));\n";
                                        outfile << ind++ << "for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // true aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != literal) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                            outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == literal) found_starter=true;\n";
                                        outfile << --ind << "}\n";
                                        outfile << ind << "assert(found_starter);\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentJoinTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp,true);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,true,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(itProp,true));}\n";

                        }else{
                            // tupleU       -> currentJoinTuple
                            // isNegated    -> false
                            // asNegative   -> true
                            outfile << ind << "{polarity.push_back(true);propagations.push_back(Glucose::mkLit(itProp,true));}\n";
                        }
                    outfile << --ind << "} // closing for joinTuplesU\n";
                outfile << --ind << "} // close else if\n";
                while (pars>0){
                    outfile << --ind << "}\n";
                    pars--;
                }
            }
            outfile << --ind << "}//close false for\n";

            outfile << ind++ << "for(unsigned i = 0; i<tuplesU->size();i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesU->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";
                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples = & AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "int aggrIdIt=tuplesU->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind++ << "if(joinTuples->size() >= "<<guard<<"){\n";

                    if(fromStarter){

                        

                        // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS FALSE %%%%%%%%%%
                        //
                        // aggrIdIt is the id of aggreset undefined
                        // currentTuple is the undefined aggId tuple 

                        outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                            outfile << ind << "bool foundConflict = solver->isConflictPropagation(aggrIdIt,false);\n";
                            outfile << ind << "bool assigned = solver->isAssigned(aggrIdIt);\n";
                            outfile << ind++ << "if(!assigned || foundConflict){\n";
                                
                                // %%%%%%%%%% PROPAGATING AGG ID AS TRUE %%%%%%%%%%
                                
                                outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                    outfile << ind << "bool found_starter=false;\n";
                                    // literal > 0 -> aggSet true
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(literal,true));\n";
                                    outfile << ind++ << "for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                        outfile << ind << "int it = *i;\n";
                                        // true aggreset are flipped
                                        outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != literal) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                        outfile << ind << "if(solver->levelFromPropagator(it)>0 && it == literal) found_starter=true;\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind << "assert(found_starter);\n";
                                outfile << --ind << "}\n";
                                
                                // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                outfile << ind << "propagationReason[0]=Glucose::mkLit(aggrIdIt);\n";

                                outfile << ind << "Glucose::CRef clause = solver->externalPropagation(aggrIdIt,false,this);\n";
                                outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                    outfile << ind-- << "return clause;\n";
                            outfile << --ind << "}\n";
                        outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(aggrIdIt));}\n";

                    }else{
                        // tupleU       -> currentTuple
                        // isNegated    -> false
                        // asNegative   -> false
                        outfile << ind << "{polarity.push_back(false);propagations.push_back(Glucose::mkLit(aggrIdIt));}\n";
                    }
                    
                outfile << --ind << "}else if(joinTuples->size() + joinTuplesU->size() < "<<guard<<"){\n";
                ind++;
                    if(fromStarter){
                        // aggrIdIt is the id of aggreset undefined
                        // currentTuple is the undefined aggId tuple 

                        outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                            outfile << ind << "bool foundConflict = solver->isConflictPropagation(aggrIdIt,true);\n";
                            outfile << ind << "bool assigned = solver->isAssigned(aggrIdIt);\n";
                            outfile << ind++ << "if(!assigned || foundConflict){\n";

                                // %%%%%%%%%% PROPAGATING AGG ID AS FALSE %%%%%%%%%%
                                        
                                outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                    outfile << ind << "bool found_starter = false;\n";
                                    // literal < 0 -> aggSet false
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-literal));\n";
                                    outfile << ind << "const IndexedSet* joinTuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                    outfile << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                        outfile << ind << "int it = *i;\n";
                                        // true aggreset are flipped
                                        outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != -literal) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                        outfile << ind << "if(solver->levelFromPropagator(it)>0 && it == -literal) found_starter=true;\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind << "assert(found_starter);\n";
                                outfile << --ind << "}\n";
                                
                                // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                outfile << ind << "propagationReason[0]=Glucose::mkLit(aggrIdIt,true);\n";

                                outfile << ind << "Glucose::CRef clause = solver->externalPropagation(aggrIdIt,true,this);\n";
                                outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                    outfile << ind-- << "return clause;\n";
                            outfile << --ind << "}\n";
                        outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(aggrIdIt,true));}\n";

                    }else{
                        // tupleU       -> currentTuple
                        // isNegated    -> false
                        // asNegative   -> true
                        outfile << ind << "propagations.push_back(Glucose::mkLit(aggrIdIt,true));\n";
                        outfile << ind << "polarity.push_back(true);\n";
                    }
                    
                outfile << --ind << "} // close else if\n";
                while(pars > 0){
                    outfile << --ind << "}\n";
                    pars--;
                }
            }
            outfile << --ind << "}//close undef for\n";
        outfile << --ind << "}//close aggr set starter\n";
    }
    if(fromStarter){
        outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
            outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
            outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
            outfile << ind++ << "if(!assigned)\n";
                outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
            outfile << ind++ << "else if(foundConflict){\n";
                outfile << ind << "lits.clear();\n";
                outfile << ind << "solver->addClause_(lits);\n";
                outfile << ind << "return Glucose::CRef_PropConf;\n";
            outfile << --ind << "}\n";
        outfile << --ind << "}\n";
    }
}
void PropagatorCompiler::compileEagerRuleWithSum(unsigned ruleId, std::ofstream& outfile, Indentation& ind,bool fromStarter){

    const aspc::Rule& r = program.getRule(ruleId);
    const aspc::Literal* bodyPred = !r.getBodyLiterals().empty() ? &r.getBodyLiterals()[0] : NULL;
    const aspc::Literal* aggrSetPred = &r.getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
    const aspc::Atom* aggrIdAtom = &r.getHead()[0];
    const aspc::ArithmeticRelationWithAggregate* aggregateRelation = &r.getArithmeticRelationsWithAggregate()[0];

    std::vector<unsigned> sharedVarAggrIDToBodyIndices;
    std::unordered_set<std::string> aggrSetVars;
    aggrSetPred->addVariablesToSet(aggrSetVars);
    for(unsigned k = 0; k < aggrIdAtom->getAriety(); k++){
        if(aggrIdAtom->isVariableTermAt(k) && aggrSetVars.count(aggrIdAtom->getTermAt(k))){
            sharedVarAggrIDToBodyIndices.push_back(k);
        }
    }

    std::vector<unsigned> sharedVarAggrIDToAggrSetIndices;
    std::unordered_set<std::string> aggrIdVars;
    aspc::Literal(false,*aggrIdAtom).addVariablesToSet(aggrIdVars);
    for(unsigned k = 0; k < aggrSetPred->getAriety(); k++){
        if(aggrSetPred->isVariableTermAt(k) && aggrIdVars.count(aggrSetPred->getTermAt(k))){
            sharedVarAggrIDToAggrSetIndices.push_back(k);
        }
    }
    std::string firstAggrVar = aggregateRelation->getAggregate().getAggregateVariables()[0];
    unsigned varIndex = 0;
    for(unsigned var = 0; var<aggrSetPred->getAriety(); var++){
        if(firstAggrVar == aggrSetPred->getTermAt(var)){
            varIndex = var;
            break;
        }
    }

    // std::cout<<"Compile eager rule with aggr"<<std::endl;
    if(fromStarter){
        {
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<aggrIdAtom->getPredicateName()<<"()){\n";
            #ifdef TRACE_PROP_GEN
            outfile << ind << "std::cout<<\"Prop rule with aggr\"<<std::endl;\n";
            #endif
            std::unordered_set<std::string> boundVariables;
            unsigned pars=0;
            for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                    outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = starter->at("<<i<<");\n";
                    boundVariables.insert(aggrIdAtom->getTermAt(i));
                }else{
                    outfile << ind++ << "if("<<term<<" == starter->at("<<i<<")){\n";
                    pars++;
                }
            }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";
                        outfile << "starter->at("<<i<<")";
                    }
                }

                outfile << "});\n";

                std::string mapName=aggrSetPred->getPredicateName()+"_";
                for(unsigned i : sharedVarAggrIDToAggrSetIndices){
                    mapName+=std::to_string(i)+"_";
                }
                std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
                std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
                
                outfile << ind << "const IndexedSet* tuples = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* tuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind << "int startVar = literal;\n",
                outfile << ind << "int uStartVar = literal>0 ? literal : -literal;\n",
                outfile << ind++ << "if(startVar < 0){\n";
                    outfile << ind << "int& actSum = TupleFactory::getInstance().getActualSumForLit(uStartVar);\n";
                    outfile << ind++ << "if(actSum>="<<guard<<"){\n";
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                       // %%%%%%%%%% HANDLE CONFLICT %%%%%%%%%%
                       outfile << ind << "std::cout << \"Unexpected rule violation: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                       outfile << ind << "assert(false);\n";
                       // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                    outfile << --ind << "}else{\n";
                    ind++;
                        outfile << ind++ << "for(auto itUndef = tuplesU->begin(); itUndef != tuplesU->end(); itUndef++){\n";
                            outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(*itUndef);\n";
                            outfile << ind++ << "if(actSum >= "<<guard<<"-currentTuple->at("<<varIndex<<")){\n";
                                outfile << ind << "int itProp = currentTuple->getId();\n";

                                // %%%%%%%%%% PROPAGATING AGGREGATE SET AS FALSE %%%%%%%%%%
                                
                                

                                // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS FALSE %%%%%%%%%%
                                //
                                // itProp is the id of aggreset undefined
                                // currentTuple is the undefined aggreset tuple

                                outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                    outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,true);\n";
                                    outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                    outfile << ind++ << "if(!assigned || foundConflict){\n";

                                        // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                        outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                            outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";

                                            // startVar < 0 -> clause contains aggId as positive
                                            outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-startVar));\n";
                                            outfile << ind++ << "for(auto i = tuples->begin(); i != tuples->end(); i++){\n";
                                                outfile << ind << "int it = *i;\n";
                                                // true aggreset are flipped
                                                outfile << ind << "if(solver->levelFromPropagator(it)>0) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                            outfile << --ind << "}\n";
                                        outfile << --ind << "}\n";
                                        
                                        // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                        outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                        outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                        outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp,true);\n";

                                        outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,true,this);\n";
                                        outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                            outfile << ind-- << "return clause;\n";
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(itProp,true));}\n";

                                // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                
                            outfile << --ind << "}else break;\n";
                        outfile << --ind << "}\n";
                        // }
                    outfile << --ind << "}\n";
                outfile << --ind << "}else{\n";
                ind++;
                    outfile << ind << "int& actSum = TupleFactory::getInstance().getActualSumForLit(uStartVar);\n";
                    outfile << ind << "int& posSum = TupleFactory::getInstance().getPossibleSumForLit(uStartVar);\n";
                    outfile << ind++ << "if(actSum+posSum < "<<guard<<"){\n";
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Unexpected rule violation: violated rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    
                    outfile << --ind << "}else{\n";
                    ind++;
                        outfile << ind++ << "for(auto index=tuplesU->begin(); index != tuplesU->end(); index++){\n";
                            outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(*index);\n";
                            // outfile << ind++ << "if(actSum+posSum-currentTuple->at("<<varIndex<<") < "<<guard<<"){\n";
                            outfile << ind++ << "if(actSum < "<<guard<<"-posSum+currentTuple->at("<<varIndex<<")){\n";
                                outfile << ind << "int itProp = currentTuple->getId();\n";

                                // %%%%%%%%%% PROPAGATING AGGREGATE SET AS TRUE %%%%%%%%%%
                                
                                

                                // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS TRUE %%%%%%%%%%
                                //
                                // itProp is the id of aggreset undefined
                                // currentTuple is the undefined aggreset tuple

                                outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                    outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,false);\n";
                                    outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                    outfile << ind++ << "if(!assigned || foundConflict){\n";

                                        // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                        outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                            outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";

                                            // startVar > 0 -> clause contains aggId as negative
                                            outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(startVar,true));\n";
                                            outfile << ind << "const IndexedSet* tuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                            outfile << ind++ << "for(auto i = tuplesF->begin(); i != tuplesF->end(); i++){\n";
                                                outfile << ind << "int it = *i;\n";
                                                // false aggreset are flipped
                                                outfile << ind << "if(solver->levelFromPropagator(it)>0) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                            outfile << --ind << "}\n";
                                        outfile << --ind << "}\n";
                                        
                                        // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                                        outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                        outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                        outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp);\n";

                                        outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,false,this);\n";
                                        outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                            outfile << ind-- << "return clause;\n";
                                    outfile << --ind << "}\n";
                                outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(itProp));}\n";

                                // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

                            outfile << --ind << "}else break;\n";
                        outfile << --ind << "}\n";
                        // }
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";
                while (pars>0){
                    outfile << --ind << "}\n";
                    pars--;
                }
                
            outfile << --ind << "}//close aggr id starter\n";
            // std::cout<<"Compiled starter aggr id"<<std::endl;
        }
    }
    {
        if(fromStarter)
            outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<aggrSetPred->getPredicateName()<<"()){\n";
        else outfile << ind++ << "{\n";

        // outfile << ind << "std::cout<<\"Propagation start from aggr_set\"<<std::endl;\n";
        std::string mapName=aggrSetPred->getPredicateName()+"_";
        for(unsigned i : sharedVarAggrIDToAggrSetIndices){
            mapName+=std::to_string(i)+"_";
        }
        std::string plusOne = r.getArithmeticRelationsWithAggregate()[0].isPlusOne() ? "+1":"";
        std::string guard = r.getArithmeticRelationsWithAggregate()[0].getGuard().getStringRep()+plusOne;
            outfile << ind << "const std::vector<int>* tuples  = &AuxMapHandler::getInstance().get_p"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<aggrIdAtom->getPredicateName()<<"_()->getValuesVec({});\n";
            // OPTIMIZATION Add if starter.isNegated
            // outfile << ind << "std::cout<<\"Prop for true head\"<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId true size: \"<<tuples->size()<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId undef size: \"<<tuplesU->size()<<std::endl;\n";
            // outfile << ind << "std::cout<<\"AggrId false size: \"<<tuplesF->size()<<std::endl;\n";

            outfile << ind++ << "for(unsigned i = 0; i<tuples->size(); i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuples->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                        std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                        if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                            outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                            boundVariables.insert(aggrIdAtom->getTermAt(i));
                        }else{
                            outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                            pars++;
                        }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";

                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples =  &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";

                outfile << ind << "int aggrIdIt=tuples->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind << "int& actSum = TupleFactory::getInstance().getActualSumForLit(aggrIdIt);\n";
                outfile << ind << "int& posSum = TupleFactory::getInstance().getPossibleSumForLit(aggrIdIt);\n";

                outfile << ind++ << "if(actSum < "<<guard<<"-posSum){\n";
                    if(fromStarter){
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Violated rule: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    }else{
                        printConflict(outfile,ind,true);
                    }
                outfile << --ind << "}else{\n";
                ind++;
                    outfile << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                        outfile << ind << "Tuple* currentJoinTuple = TupleFactory::getInstance().getTupleFromInternalID(*index);\n";
                        outfile << ind << "if(actSum >= "<<guard<<"-posSum+currentJoinTuple->at("<<varIndex<<")) {break;}\n";
                        outfile << ind << "int itProp = *index;\n";
                        if(fromStarter){
                            
                            // %%%%%%%%%% PROPAGATING AGGREGATE SET AS TRUE %%%%%%%%%%
                                    
                            // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS TRUE %%%%%%%%%%
                            //
                            // itProp is the id of aggreset undefined
                            // currentJoinTuple is the undefined aggreset tuple
                            // currentTuple is the aggId tuple

                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,false);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";
        
                                    // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                        outfile << ind << "bool found_starter = false;\n";

                                        // literal < 0 -> aggSet false
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-literal));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(currentTuple->getId(),true));\n";
                                        outfile << ind << "const IndexedSet* joinTuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                        outfile << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // false aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != -literal) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                            outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == -literal) found_starter=true;\n";
                                        outfile << --ind << "}\n";
                                        outfile << ind << "assert(found_starter);\n";
                                    outfile << --ind << "}\n";
                                    
                                    // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentJoinTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,false,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(itProp));}\n";

                        }else{
                            outfile << ind << "propagations.push_back(Glucose::mkLit(itProp));\n";
                            outfile << ind << "polarity.push_back(false);\n";
                        }
                    outfile << --ind << "} //close for joinTuplesU\n";
                outfile << --ind << "} //close else\n";
                
                while(pars>0){
                    pars--;
                    outfile << --ind << "}\n";
                }
            }
            outfile << --ind << "}//close true for\n";
            //OPTIMIZATION Add if !starter.isNegated

            // outfile << ind << "std::cout<<\"Prop for false head\"<<std::endl;\n";
            outfile << ind++ << "for(unsigned i = 0; i<tuplesF->size(); i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesF->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred != NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";

                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples = & AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "int aggrIdIt=tuplesF->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind << "int& actSum = TupleFactory::getInstance().getActualSumForLit(aggrIdIt);\n";
                outfile << ind++ << "if(actSum >= "<<guard<<"){\n";
                    //outfile << ind << "std::cout<<\"Conflitct on aggregate starting from false aggr id "<<r.getRuleId()<<"\"<<actualSum[aggrIdIt]<<std::endl;\n";
                    if(fromStarter){
                        outfile << ind++ << "if(solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
                        outfile << --ind << "}\n";
                        outfile << ind << "std::cout << \"Violated rule: rule with aggregate "<<ruleId<<"\"<<std::endl;\n";
                        outfile << ind << "assert(0);\n";
                    }else{
                        printConflict(outfile,ind,true);
                    }
                outfile << --ind << "}else{\n";
                ind++;
                    
                    outfile << ind++ << "for(auto index=joinTuplesU->begin(); index != joinTuplesU->end(); index++){\n";
                        outfile << ind << "Tuple* currentJoinTuple = TupleFactory::getInstance().getTupleFromInternalID(*index);\n";
                        outfile << ind << "int itProp = *index;\n";
                        outfile << ind << "if(actSum < "<<guard<<"-currentJoinTuple->at("<<varIndex<<"))break;\n";

                        if(fromStarter){
                            // %%%%%%%%%% PROPAGATING AGGREGATE SET AS FALSE %%%%%%%%%%
                            
                            // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS FALSE %%%%%%%%%%
                            //
                            // itProp is the id of aggreset undefined
                            // currentJoinTuple is the undefined aggreset tuple
                            // currentTuple is the aggId tuple

                            outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                                outfile << ind << "bool foundConflict = solver->isConflictPropagation(itProp,true);\n";
                                outfile << ind << "bool assigned = solver->isAssigned(itProp);\n";
                                outfile << ind++ << "if(!assigned || foundConflict){\n";

                                    // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                    outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";

                                        outfile << ind << "bool found_starter=false;\n";
                                        // literal > 0 -> aggSet true
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(literal,true));\n";
                                        outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(currentTuple->getId()));\n";
                                        outfile << ind++ << "for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                            outfile << ind << "int it = *i;\n";
                                            // true aggreset are flipped
                                            outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != literal) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                            outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == literal) found_starter=true;\n";
                                        outfile << --ind << "}\n";
                                        outfile << ind << "assert(found_starter);\n";
                                    outfile << --ind << "}\n";
                                    
                                    // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentJoinTuple->getReasonLits() : solver->getReasonClause();\n";
                                    outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                    outfile << ind << "propagationReason[0]=Glucose::mkLit(itProp,true);\n";

                                    outfile << ind << "Glucose::CRef clause = solver->externalPropagation(itProp,true,this);\n";
                                    outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                        outfile << ind-- << "return clause;\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(itProp,true));}\n";

                        }else{
                            // tupleU       -> currentJoinTuple
                            // isNegated    -> false
                            // asNegative   -> true
                            outfile << ind << "propagations.push_back(Glucose::mkLit(itProp,true));\n";
                            outfile << ind << "polarity.push_back(true);\n";
                        }
                    outfile << --ind << "} // closing for joinTuplesU\n";
                outfile << --ind << "} // close else if\n";
                while (pars>0){
                    outfile << --ind << "}\n";
                    pars--;
                }
            }
            outfile << --ind << "}//close false for\n";

            outfile << ind++ << "for(unsigned i = 0; i<tuplesU->size();i++){\n";
            {
                unsigned pars=0;
                outfile << ind << "Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesU->at(i));\n";
                std::unordered_set<std::string> boundVariables;
                for(unsigned i = 0; i<aggrIdAtom->getAriety(); i++){
                    std::string term = aggrIdAtom->isVariableTermAt(i) || isInteger(aggrIdAtom->getTermAt(i)) ? aggrIdAtom->getTermAt(i) : "ConstantsManager::getInstance().mapConstant(\""+aggrIdAtom->getTermAt(i)+"\")"; 
                    if(aggrIdAtom->isVariableTermAt(i) && boundVariables.count(aggrIdAtom->getTermAt(i))==0){
                        outfile << ind << "int "<<aggrIdAtom->getTermAt(i)<<" = currentTuple->at("<<i<<");\n";
                        boundVariables.insert(aggrIdAtom->getTermAt(i));
                    }else{
                        outfile << ind++ << "if("<<term<<" == currentTuple->at("<<i<<")){\n";
                        pars++;
                    }
                }
                outfile << ind << "std::vector<int> sharedVar({";
                if(bodyPred!=NULL){
                    bool first=true;
                    for(unsigned i : sharedVarAggrIDToBodyIndices){
                        if(first)
                            first=false;
                        else outfile <<",";
                        outfile << "currentTuple->at("<<i<<")";
                    }
                }
                outfile << "});\n";
                outfile << ind << "const IndexedSet* joinTuples = & AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "const IndexedSet* joinTuplesU = &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesSet(sharedVar);\n";
                outfile << ind << "int aggrIdIt=tuplesU->at(i);\n";
                outfile << ind << "std::shared_ptr<VectorAsSet<Glucose::Lit>> shared_reason = std::make_shared<VectorAsSet<Glucose::Lit>>();\n";
                outfile << ind << "int& actSum = TupleFactory::getInstance().getActualSumForLit(aggrIdIt);\n";
                outfile << ind << "int& posSum = TupleFactory::getInstance().getPossibleSumForLit(aggrIdIt);\n";
                outfile << ind++ << "if(actSum >= "<<guard<<"){\n";
                if(fromStarter){

                    // %%%%%%%%%% PROPAGATING AGG ID AS TRUE %%%%%%%%%%
                     

                    // %%%%%%%%%% PROPAGATE UNDEF AGGREGATEID AS TRUE %%%%%%%%%%
                    //
                    // aggrIdIt is the id of aggreset undefined
                    // currentTuple is the undefined aggId tuple 

                    outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                        outfile << ind << "bool foundConflict = solver->isConflictPropagation(aggrIdIt,false);\n";
                        outfile << ind << "bool assigned = solver->isAssigned(aggrIdIt);\n";
                        outfile << ind++ << "if(!assigned || foundConflict){\n";
                                   
                            // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%
                            // 0, starter, true aggset/starter

                            outfile << ind << "assert(literal > 0);\n";
                            outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                outfile << ind << "bool found_starter = false;\n";
                                // literal > 0 -> aggSet true
                                outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(literal,true));\n";
                                outfile << ind++ << "for(auto i = joinTuples->begin(); i != joinTuples->end(); i++){\n";
                                    outfile << ind << "int it = *i;\n";
                                    // true aggreset are flipped
                                    outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != literal) shared_reason.get()->insert(Glucose::mkLit(it,true));\n";
                                    outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == literal) found_starter=true;\n";
                                outfile << --ind << "}\n";
                                outfile << ind << "assert(found_starter);\n";
                            outfile << --ind << "}\n";
                            
                            // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                            outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                            outfile << ind << "propagationReason[0]=Glucose::mkLit(aggrIdIt);\n";

                            outfile << ind << "Glucose::CRef clause = solver->externalPropagation(aggrIdIt,false,this);\n";
                            outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                outfile << ind-- << "return clause;\n";
                        outfile << --ind << "}\n";
                    outfile << --ind << "}else {polarity.push_back(false);propagations.push_back(Glucose::mkLit(aggrIdIt));}\n";

                }else{
                    // tupleU       -> currentTuple
                    // isNegated    -> false
                    // asNegative   -> false
                    outfile << ind << "propagations.push_back(Glucose::mkLit(aggrIdIt));\n";
                    outfile << ind << "polarity.push_back(false);\n";
                }
                outfile << --ind << "}else if(actSum < "<<guard<<" - posSum){\n";
                ind++;
                    if(fromStarter){

                        // %%%%%%%%%% PROPAGATING AGG ID AS TRUE %%%%%%%%%%
                                
                        // %%%%%%%%%% PROPAGATE UNDEF AGGREGATESET AS FALSE %%%%%%%%%%
                        //
                        // aggrIdIt is the id of aggreset undefined
                        // currentTuple is the undefined aggId tuple 

                        outfile << ind++ << "if(solver->currentLevel() > 0){\n";
                            outfile << ind << "bool foundConflict = solver->isConflictPropagation(aggrIdIt,true);\n";
                            outfile << ind << "bool assigned = solver->isAssigned(aggrIdIt);\n";
                            outfile << ind++ << "if(!assigned || foundConflict){\n";

                                // %%%%%%%%%% COMPUTING REASON %%%%%%%%%%

                                outfile << ind++ << "if(shared_reason.get()->empty() && solver->currentLevel() > 0){\n";
                                    outfile << ind << "bool found_starter=false;\n";
                                    // literal > 0 -> aggSet true
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(0));\n";
                                    outfile << ind << "shared_reason.get()->insert(Glucose::mkLit(-literal,true));\n";
                                    outfile << ind << "const IndexedSet* joinTuplesF = &AuxMapHandler::getInstance().get_f"<<mapName<<"()->getValuesSet(sharedVar);\n";
                                    outfile << ind++ << "for(auto i = joinTuplesF->begin(); i != joinTuplesF->end(); i++){\n";
                                        outfile << ind << "int it = *i;\n";
                                        // true aggreset are flipped
                                        outfile << ind << "if(solver->levelFromPropagator(it)>0 && it != -literal) shared_reason.get()->insert(Glucose::mkLit(it));\n";
                                        outfile << ind << "else if(solver->levelFromPropagator(it)>0 && it == -literal) found_starter=true;\n";
                                    outfile << --ind << "}\n";
                                    outfile << ind << "assert(found_starter);\n";
                                outfile << --ind << "}\n";
                                
                                // %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                                outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason = !assigned ? currentTuple->getReasonLits() : solver->getReasonClause();\n";
                                outfile << ind << "propagationReason.copyFrom(shared_reason.get()->getData(),shared_reason.get()->size());\n";
                                outfile << ind << "propagationReason[0]=Glucose::mkLit(aggrIdIt,true);\n";

                                outfile << ind << "Glucose::CRef clause = solver->externalPropagation(aggrIdIt,true,this);\n";
                                outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                                    outfile << ind-- << "return clause;\n";
                            outfile << --ind << "}\n";
                        outfile << --ind << "}else {polarity.push_back(true);propagations.push_back(Glucose::mkLit(aggrIdIt,true));}\n";

                    }else{
                        // tupleU       -> currentTuple
                        // isNegated    -> false
                        // asNegative   -> true
                        outfile << ind << "propagations.push_back(Glucose::mkLit(aggrIdIt,true));\n";
                        outfile << ind << "polarity.push_back(true);\n";
                    }
                    
                outfile << --ind << "} // close else if\n";
                while(pars > 0){
                    outfile << --ind << "}\n";
                    pars--;
                }
            }
            outfile << --ind << "}//close undef for\n";
        outfile << --ind << "}//close aggr set starter\n";
    }

    if(fromStarter){
        outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
            outfile << ind << "bool foundConflict = solver->isConflictPropagation(var(propagations[i]), polarity[i]);\n";
            outfile << ind << "bool assigned = solver->isAssigned(var(propagations[i]));\n";
            outfile << ind++ << "if(!assigned)\n";
                outfile << ind-- << "solver->assignFromPropagators(propagations[i]);\n";
            outfile << ind++ << "else if(foundConflict){\n";
                outfile << ind << "lits.clear();\n";
                outfile << ind << "solver->addClause_(lits);\n";
                outfile << ind << "return Glucose::CRef_PropConf;\n";
            outfile << --ind << "}\n";
        outfile << --ind << "}\n";
    }
}
void PropagatorCompiler::compileEagerRuleWithAggregate(unsigned ruleId, std::ofstream& outfile, Indentation& ind,bool fromStarter){
    if(program.getRule(ruleId).getArithmeticRelationsWithAggregate()[0].getAggregate().isSum()){
        compileEagerRuleWithSum(ruleId,outfile,ind,fromStarter);
    }else{
        compileEagerRuleWithCount(ruleId,outfile,ind,fromStarter);
    }
}