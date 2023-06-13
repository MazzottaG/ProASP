#include "PropagatorCompiler.h"


void PropagatorCompiler::compileRuleFromStarter(unsigned ruleId, std::ofstream& outfile, Indentation& ind){
    outfile << ind++ << "Glucose::CRef propagate(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits,int literal) override {\n";
    outfile << ind << "Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID( literal > 0 ? literal : -literal);\n";
    outfile << ind << "if(starter == NULL){if(literal != 0){std::cout << \"Error: unable to find starting literal\" <<std::endl; exit(180);}}\n";
    #ifdef DEBUG_PROP
    outfile << ind << "std::cout << \"Propagator "<<ruleId<<": Propagating \"<<literal << \" \"; AuxMapHandler::getInstance().printTuple(starter); std::cout << std::endl;\n";
    #endif
    outfile << ind++ << "if(starter->isUndef()){\n";
        outfile << ind << "const auto& insertResult = starter->setStatus(literal > 0 ? True : False);\n";
        outfile << ind++ << "if(insertResult.second){\n";
            outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(starter->getId());\n";
            outfile << ind << "if(literal > 0) AuxMapHandler::getInstance().insertTrue(insertResult);\n";
            outfile << ind << "else AuxMapHandler::getInstance().insertFalse(insertResult);\n";
        outfile << --ind << "}\n";    
    outfile << --ind << "}\n";
    outfile << ind++ << "else{\n";
        outfile << ind << "if((literal > 0 && starter->isFalse()) || (literal < 0 && starter->isTrue())) {std::cout << \"Error: literal already assigned with different value\" <<std::endl; exit(180);}\n";
    outfile << --ind << "}\n";     
    outfile << ind << "std::vector<Glucose::Lit> propagations;\n";

    aspc::Rule rule = program.getRule(ruleId);
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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind << "const std::vector<int>* bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind++ << "if(literal > 0){\n";
                        // head is true
                            // outfile << ind++ << "if(bodyTuplesU->size()+bodyTuplesP->size() == 0){\n";
                            //     #ifdef DEBUG_PROP
                            //     outfile << ind << "std::cout << \"True head for no positive literal true/undefined\"<<std::endl;\n";
                            //     #endif
                            //     outfile << ind << "solver->clearReasonClause();\n";
                            //     outfile << ind << "solver->addLiteralToReason(literal,true);\n";
                            //     outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
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
                            //             outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
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
                                outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(0));\n";
                                outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                outfile << ind++ << "else{\n";
                                    
                                    printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                        printAddToReason(outfile,ind,"literal","true");
                                        outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                        outfile << ind++ << "for(unsigned i = 0; i< bodyTuplesF->size();i++){\n";
                                            printAddToReason(outfile,ind,"bodyTuplesF->at(i)","false");
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
                                outfile << ind++ << "for(unsigned i = 0; i<bodyTuplesU->size(); i++){\n";
                                    outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(i));\n";
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
                    outfile << ind << "lits.clear();\n";
                    outfile << ind << "lits.push( propagations[i] );\n";
                    outfile << ind << "if(!solver->addClause_(lits)) return Glucose::CRef_PropConf;\n";
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
                                    printAddPropagatedToReason(outfile,ind,"-literal","false");
                                    printTuplePropagation(outfile,ind,"head",false,false);
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if((head == NULL || head->isFalse()) && solver->currentLevel() == 0){\n";
                            outfile << ind << "lits.clear();\n";
                            outfile << ind << "solver->addClause_(lits);\n";
                            outfile << ind << "return Glucose::CRef_PropConf;\n";
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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || headVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind << "const std::vector<int>* bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
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
                                //     outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
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
                                //         outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
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
                                    outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(0));\n";
                                    outfile << ind << "if(tupleU == NULL){ std::cout << \"Error: Unable to find tuple to propagate\"<<std::endl; exit(180);}\n";
                                    outfile << ind++ << "else{\n";
                                        #ifdef DEBUG_PROP
                                        outfile << ind << "std::cout << \"Last remaining body for true head\"<<std::endl;\n";
                                        #endif
                                        outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                        printAddPropagatedToReason(outfile,ind,"tupleU",false);
                                            printAddToReason(outfile,ind,"-literal","false");
                                            outfile << ind++ << "for(unsigned i =0; i< bodyTuplesF->size(); i++){\n";
                                                outfile << ind << "int reasonLit = bodyTuplesF->at(i);\n";
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
                                outfile << ind << "const std::vector<int>* bodyTuplesF = &"<<prefix<<"f"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                                printAddPropagatedToReason(outfile,ind,"head",true);
                                    printAddToReason(outfile,ind,"-literal","false"); 
                                    outfile << ind++ << "for(unsigned i =0; i< bodyTuplesF->size(); i++){\n";
                                        outfile << ind << "int reasonLit = bodyTuplesF->at(i);\n";
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
                        outfile << ind << "lits.clear();\n";
                        outfile << ind << "lits.push( propagations[i] );\n";
                        outfile << ind << "if(!solver->addClause_(lits)) return Glucose::CRef_PropConf;\n";
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
                            
                            for(unsigned k=0; k<lit->getAriety(); k++){
                                if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                    std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                    mapName+=std::to_string(k)+"_";
                                    terms += (terms != "" ? ","+term : term);
                                    boundIndices.insert(k);
                                }
                            }
                            outfile << ind << "const std::vector<int>* tuplesU_"<<index<<" = tupleU == NULL ? &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesVec({"<<terms<<"}) : &tuplesEmpty;\n";
                            outfile << ind << "const std::vector<int>* tuples_"<<index<<" = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                            outfile << ind++ << "for(unsigned i=0; i<tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()+repeatedTuples.size(); i++){\n";
                            closingPars++;
                                #ifdef DEBUG_PROP
                                outfile << ind << "std::cout << \" Evaluating "<<index<<"\" << i << \" \" << tuples_"<<index<<"->size()<<std::endl;\n";
                                #endif
                                    
                                outfile << ind << "Tuple* tuple_"<<index<<"=NULL;\n";
                                outfile << ind++ << "if(i < tuples_"<<index<<"->size()){\n";
                                    outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(tuples_"<<index<<"->at(i));\n";
                                    outfile << ind << "if(tuplesU_"<<index<<" != &tuplesEmpty) tupleU=NULL;\n";
                                    if(rule.getSupportAtom() == index){
                                        outfile << ind << "if(TupleFactory::getInstance().isFact(tuple_"<<index<<"->getId())) continue;\n";
                                    }
                                outfile << --ind << "}\n";
                                outfile << ind++ << "else if(i < tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()){\n";
                                    outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(tuplesU_"<<index<<"->at(i-tuples_"<<index<<"->size()));\n";
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
                    outfile << ind << "lits.clear();\n";
                    outfile << ind << "lits.push( propagations[i] );\n";
                    outfile << ind << "if(!solver->addClause_(lits)) return Glucose::CRef_PropConf;\n";
                outfile << --ind << "}\n";
            outfile << --ind << "}\n";
            
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
    }else{
        //  foundConflict -> violated clause is in solver
        outfile << ind++ << "if(solver->currentLevel() > 0){\n";
            outfile << ind << "Glucose::CRef clause = solver->externalPropagation("<<tuplename<<"->getId(),var < 0,this);\n";
            outfile << ind++ << "if(clause != Glucose::CRef_Undef)\n";
                outfile << ind-- << "return clause;\n";
        outfile << --ind << "}else propagations.push_back((var >= 0) ? Glucose::mkLit(var) : Glucose::mkLit(-var,true));\n";
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
    outfile << ind << "std::vector<int> watched(TupleFactory::getInstance().size(),0);\n";
    aspc::Rule rule = program.getRule(ruleId);
    const std::vector<const aspc::Formula*>& body = rule.getFormulas();
    if ( false /* OPT_FULL_WATCHED */ ){
        if(!rule.isConstraint()){
            //rules have body of lenght 1
            if(!body[0]->isLiteral()){
                std::cout << "Warning: Rule with only one arithmetic relation in the body"<<std::endl;
            }else{
                const aspc::Atom* head = &rule.getHead()[0];
                const aspc::Literal* lit = (const aspc::Literal*) body[0];
                outfile << "{\n";
                    outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                    
                    std::unordered_set<std::string> boundVars;
                    outfile << ind++ << "for(int i = 0; i < tuplesP->size() + tuplesF->size() + tuplesU->size(); i++){\n";
                    
                        int closingPars=0;
                        outfile << ind << "int id = i < tuplesP->size() ? tuplesP->at(i) : (i < tuplesP->size()+tuplesF->size() ? tuplesF->at(i - tuplesP->size()) : tuplesU->at(i - tuplesP->size() - tuplesF->size()));\n";
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
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this,id,false);\n";
                                outfile << ind++ << "if(watchValue != -1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this,id,true);\n";
                            outfile << --ind << "}\n";

                        while(closingPars>0){
                            outfile << --ind << "}\n";
                            closingPars--;
                        }
                    outfile << --ind << "}\n";
                outfile << "}\n";

                outfile << ind++ << "{\n";
                    outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    
                    boundVars.clear();
                    outfile << ind++ << "for(int i = 0; i < tuplesP->size() + tuplesF->size() + tuplesU->size(); i++){\n";
                    
                        closingPars=0;
                        outfile << ind << "int id = i < tuplesP->size() ? tuplesP->at(i) : (i < tuplesP->size()+tuplesF->size() ? tuplesF->at(i - tuplesP->size()) : tuplesU->at(i - tuplesP->size() - tuplesF->size()));\n";
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
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this,id,false);\n";
                                outfile << ind++ << "if(watchValue != -1)\n";
                                    outfile << ind-- << "TupleFactory::getInstance().addWatcher(this,id,true);\n";
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
                                    outfile << ind << "TupleFactory::getInstance().addWatcher(this,id_"<<index<<","<<(lit->isNegated() ? "true" : "false")<<");\n";
                                outfile << --ind << "}\n";
                            outfile << --ind << "}\n";
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
                            outfile << ind << "int id_"<<index<<" = tuple_"<<index<<"->getId();\n";
                            outfile << ind << "int& watchValue=watched[id_"<<index<<"];\n";
                            outfile << ind++ << "if(watchValue < 1){\n";
                                outfile << ind << "watchValue = watchValue != 0 ? 2 : 1;\n";
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id_"<<index<<",false);\n";
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
                auto attachedValue = attached.emplace(predicate,0);
                if(attachedValue.first->second != 2){
                    outfile << "{\n";
                        outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                        outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                        outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
                        
                        std::unordered_set<std::string> boundVars;
                        outfile << ind++ << "for(int i = 0; i < tuplesP->size() + tuplesF->size() + tuplesU->size(); i++){\n";
                        
                            int closingPars=0;
                            outfile << ind << "int id = i < tuplesP->size() ? tuplesP->at(i) : (i < tuplesP->size()+tuplesF->size() ? tuplesF->at(i - tuplesP->size()) : tuplesU->at(i - tuplesP->size() - tuplesF->size()));\n";
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
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,false);\n";
                            
                            if(attachedValue.first->second != -1)
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,true);\n";
                            
                            attached[predicate]=2;
                            while(closingPars>0){
                                outfile << --ind << "}\n";
                                closingPars--;
                            }
                        outfile << --ind << "}\n";
                    outfile << "}\n";
                }
            }
        }
        const std::vector<const aspc::Formula*>* body = &rule.getFormulas();
        for(int i=0;i<body->size();i++){
            const aspc::Formula* formula = body->at(i);
            if(!formula->isLiteral())
                continue;
            const aspc::Literal* lit = (const aspc::Literal*) formula;

            std::string predicate = lit->getPredicateName();
            auto attachedValue = attached.emplace(predicate,0);
            if(attachedValue.first->second == 2)
                continue;
            int expected = lit->isNegated() ? -1 : 1;

            if(attachedValue.first->second != expected){
                outfile << ind++ << "{\n";
                    outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<lit->getPredicateName()<<"_()->getValuesVec({});\n";
                    
                    std::unordered_set<std::string> boundVars;
                    outfile << ind++ << "for(int i = 0; i < tuplesP->size() + tuplesF->size() + tuplesU->size(); i++){\n";
                    
                        int closingPars=0;
                        outfile << ind << "int id = i < tuplesP->size() ? tuplesP->at(i) : (i < tuplesP->size()+tuplesF->size() ? tuplesF->at(i - tuplesP->size()) : tuplesU->at(i - tuplesP->size() - tuplesF->size()));\n";
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
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,false);\n";
                            
                            if(attachedValue.first->second != -1)
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,true);\n";
                            
                            attached[predicate]=2;
                        }else{
                            if(expected == 1)
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,false);\n";
                            else
                                outfile << ind << "TupleFactory::getInstance().addWatcher(this,id,true);\n";
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
    
    outfile << --ind << "} //function\n";
}
void PropagatorCompiler::compileRuleLevelZero(unsigned ruleId,std::ofstream& outfile,Indentation& ind){
    
    outfile << ind++ << "virtual void propagateLevelZero(Glucose::Solver* solver,Glucose::vec<Glucose::Lit>& lits) override {\n";
    #ifdef DEBUG_PROP
    outfile << ind << "std::cout <<\"PropagateAtLevel0 "<<ruleId<<"\"<<std::endl;\n";
    #endif
    outfile << ind << "std::vector<Glucose::Lit> propagations;\n";
    aspc::Rule rule = program.getRule(ruleId);
    const std::vector<const aspc::Formula*>& body = rule.getFormulas();
    if(!rule.isConstraint()){
        //rules have body of lenght 1
        if(!body[0]->isLiteral()){
            std::cout << "Waring: Rule with only one arithmetic relation in the body"<<std::endl;
        }else{
            const aspc::Atom* head = &rule.getHead()[0];
            const aspc::Literal* lit = (const aspc::Literal*) body[0];

            outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
            outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
            
            {
                std::unordered_set<std::string> boundVars;
                int closingPars=0;
                outfile << ind++ << "for(int i = 0; i < tuplesP->size(); i++){\n";
                closingPars++;
                    outfile << ind << "int id = tuplesP->at(i);\n";

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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind << "const std::vector<int>* bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        
                        outfile << ind++ << "if(bodyTuplesU->size()+bodyTuplesP->size() == 0){\n";
                            printConflict(outfile,ind,true);
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){\n";
                            outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(0));\n";
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
                outfile << ind++ << "for(int i = 0; i < tuplesF->size(); i++){\n";
                closingPars++;
                    outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesF->at(i));\n";
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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind << "const std::vector<int>* bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        
                        outfile << ind++ << "if(bodyTuplesP->size() > 0){\n";
                            printConflict(outfile,ind,true);
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if(bodyTuplesU->size() > 0){\n";
                            #ifdef DEBUG_PROP
                            outfile << ind << "std::cout << \"Propagating all undefined as false\" <<std::endl;\n";
                            #endif
                                    
                            outfile << ind++ << "for(unsigned i = 0; i<bodyTuplesU->size(); i++){\n";
                                outfile << ind << "Tuple* tupleU = TupleFactory::getInstance().getTupleFromInternalID(bodyTuplesU->at(i));\n";
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
                outfile << ind++ << "for(int i = 0; i < tuplesU->size(); i++){\n";
                closingPars++;
                    outfile << ind << "int id = tuplesU->at(i);\n";

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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* bodyTuplesU = &"<<prefix<<"u"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind << "const std::vector<int>* bodyTuplesP = &"<<prefix<<"p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        
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
                        
                        for(unsigned k=0; k<lit->getAriety(); k++){
                            if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                                std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                                mapName+=std::to_string(k)+"_";
                                terms += (terms != "" ? ","+term : term);
                                boundIndices.insert(k);
                            }
                        }
                        outfile << ind << "const std::vector<int>* tuplesU_"<<index<<" = tupleU == NULL ? &AuxMapHandler::getInstance().get_u"<<mapName<<"()->getValuesVec({"<<terms<<"}) : &tuplesEmpty;\n";
                        outfile << ind << "const std::vector<int>* tuples_"<<index<<" = &AuxMapHandler::getInstance().get_p"<<mapName<<"()->getValuesVec({"<<terms<<"});\n";
                        outfile << ind++ << "for(unsigned i=0; i<tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()+repeatedTuples.size(); i++){\n";
                        closingPars++;
                            outfile << ind << "Tuple* tuple_"<<index<<"=NULL;\n";
                            outfile << ind++ << "if(i < tuples_"<<index<<"->size()){\n"; 
                                outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(tuples_"<<index<<"->at(i));\n";
                                outfile << ind << "if(tuplesU_"<<index<<" != &tuplesEmpty) tupleU=NULL;\n";
                                if(rule.getSupportAtom() == index){
                                    outfile << ind << "if(TupleFactory::getInstance().isFact(tuple_"<<index<<"->getId())) continue;\n";
                                }
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(i < tuples_"<<index<<"->size()+tuplesU_"<<index<<"->size()){\n";
                                outfile << ind << "tuple_"<<index<<" = TupleFactory::getInstance().getTupleFromInternalID(tuplesU_"<<index<<"->at(i-tuples_"<<index<<"->size()));\n";
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
        outfile << ind++ << "for(unsigned i = 0; i< propagations.size(); i++){\n";
            outfile << ind << "lits.clear();\n";
            outfile << ind << "lits.push( propagations[i] );\n";
            outfile << ind << "solver->addClause_(lits);\n";
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
        // outfile << ind << "#include \"../../core/Solver.h\"\n";
        outfile << ind << "typedef TupleLight Tuple;\n";
        outfile << ind << "template<size_t S>\n";
        outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

        outfile << ind++ << "class "<<className<<": public AbstractPropagator{\n";
            outfile << ind << "const std::vector<int> tuplesEmpty;\n";
            outfile << ind++ << "public:\n";
                outfile << ind << className << "():tuplesEmpty({}){}\n";
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
        for(unsigned ruleId : propagatorOrder){
            std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
            outfile << ind << "propagators.push_back(new "<<className<<"());\n";
        }
    outfile << --ind << "}\n";
    outfile.close();

    
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
