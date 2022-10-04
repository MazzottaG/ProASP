#include "PropagatorCompiler.h"

void PropagatorCompiler::compileRuleLevelZero(unsigned ruleId,std::ofstream& outfile,Indentation& ind){
    
    outfile << ind++ << "void propagateLevelZero()override {\n";
    
    aspc::Rule rule = program.getRule(ruleId);
    const std::vector<const aspc::Formula*>& body = rule.getFormulas();
    if(!rule.isConstraint()){
        //rules have body of lenght 1
        std::unordered_set<std::string> boundVars;
        if(!body[0]->isLiteral()){
            std::cout << "Waring: Rule with only one arithmetic relation in the body"<<std::endl;
        }else{
            const aspc::Atom* head = &rule.getHead()[0];
            const aspc::Literal* lit = (const aspc::Literal*) body[0];

            outfile << ind << "const std::vector<int>* tuplesU = &AuxMapHandler::getInstance().get_u"<<head->getPredicateName()<<"_()->getValuesVec();\n";
            outfile << ind << "const std::vector<int>* tuplesF = &AuxMapHandler::getInstance().get_f"<<head->getPredicateName()<<"_()->getValuesVec();\n";
            outfile << ind << "const std::vector<int>* tuplesP = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValuesVec();\n";
            
            {
                int closingPars=0;
                outfile << ind++ << "for(int i = 0; i < tuplesP->size(); i++){\n";
                closingPars++;
                    outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesP->at(i));\n";
                    outfile << ind++ << "if(tuple != NULL){\n";
                    closingPars++;
                    for(unsigned k=0; k<head->getAriety(); k++){
                        if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                            std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant("+head->getTermAt(k)+")";
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
                                outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                outfile << ind << "std::cout << \"Propagate body atom as false\"; <<std::endl;\n";
                            outfile << --ind << "}\n";
                            
                        }else{
                            outfile << ind++ << "if(boundBody != NULL && boundBody->isFalse()){\n";
                                outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                outfile << ind << "std::cout << \"Propagate body atom as true\"; <<std::endl;\n";
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
                            outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if(bodyTuplesP->size() == 0 && bodyTuplesU->size() == 1){\n";
                            outfile << ind << "std::cout << \"Propagating last undefined as true\" <<std::endl;\n";
                        outfile << --ind << "}\n";
                    }
                while (closingPars > 0){
                    outfile << --ind << "}\n";
                    closingPars--;
                }
            }
            {
                int closingPars=0;
                outfile << ind++ << "for(int i = 0; i < tuplesF->size(); i++){\n";
                closingPars++;
                    outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesP->at(i));\n";
                    outfile << ind++ << "if(tuple != NULL){\n";
                    closingPars++;
                    for(unsigned k=0; k<head->getAriety(); k++){
                        if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                            std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant("+head->getTermAt(k)+")";
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
                            outfile << ind++ << "if(boundBody != NULL && boundBody->isFalse()){\n";
                                outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                outfile << ind << "std::cout << \"Propagate body atom as true\"; <<std::endl;\n";
                            outfile << --ind << "}\n";
                            
                        }else{
                            // false head and positive body literal
                            outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody != NULL && boundBody->isUndef()){\n";
                                outfile << ind << "std::cout << \"Propagate body atom as false\"; <<std::endl;\n";
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
                            outfile << ind << "std::cout << \"Conflict detected at level 0\" <<std::endl;\n";
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if(bodyTuplesU->size() > 0){\n";
                            outfile << ind << "std::cout << \"Propagating all undefined as false\" <<std::endl;\n";
                        outfile << --ind << "}\n";
                    }
                while (closingPars > 0){
                    outfile << --ind << "}\n";
                    closingPars--;
                }
            }
            {
                int closingPars=0;
                outfile << ind++ << "for(int i = 0; i < tuplesU->size(); i++){\n";
                closingPars++;
                    outfile << ind << "Tuple* tuple = TupleFactory::getInstance().getTupleFromInternalID(tuplesP->at(i));\n";
                    outfile << ind++ << "if(tuple != NULL){\n";
                    closingPars++;
                    for(unsigned k=0; k<head->getAriety(); k++){
                        if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                            std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant("+head->getTermAt(k)+")";
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
                                outfile << ind << "std::cout << \"Propagate head as true\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody != NULL && boundBody->isTrue()){\n";
                                outfile << ind << "std::cout << \"Propagate head as false\"; <<std::endl;\n";
                            outfile << --ind << "}\n";
                            
                        }else{
                            // undef head and positive body literal
                            outfile << ind++ << "if(boundBody != NULL && boundBody->isTrue()){\n";
                                outfile << ind << "std::cout << \"Propagate head as true\" <<std::endl;\n";
                            outfile << --ind << "}\n";
                            outfile << ind++ << "else if(boundBody == NULL && boundBody->isFalse()){\n";
                                outfile << ind << "std::cout << \"Propagate head as false\"; <<std::endl;\n";
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
                            outfile << ind << "std::cout << \"Propagate head as true\" <<std::endl;\n";
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else if(bodyTuplesU->size() == 0){\n";
                            outfile << ind << "std::cout << \"Propagate head as false\" <<std::endl;\n";
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
                    if(f->isBoundedValueAssignment(boundVars)){
                        outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<std::endl;
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
                            outfile << ind++ << "}else if(*tupleU == *boundBody && tupleUNegated){\n";
                        else
                            outfile << ind++ << "}else if(*tupleU == *boundBody && !tupleUNegated){\n";
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
                            outfile << ind << "Tuple* tuple_"<<index<<"=boundBody;\n";
                    }else{
                        outfile << ind << "std::vector<int> repeatedTuple;\n";
                        
                    }
                    
                }
            }
    }
    outfile << --ind << "}\n";
}
void PropagatorCompiler::compile(){
    buildAuxMapHandler();
    for(unsigned ruleId=0; ruleId < program.getRulesSize(); ruleId++){
        Indentation ind(0);
        std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
        std::string executorPath = executablePath + "/../src/propagators/"+className+".h";
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
        outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
        outfile << ind << "typedef TupleLight Tuple;\n";
        outfile << ind << "template<size_t S>\n";
        outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";
        outfile << ind << "typedef std::vector<const Tuple* > Tuples;\n";

        outfile << ind++ << "class "<<className<<": public AbstractGenerator{\n";
            outfile << ind++ << "public:\n";
                compileRuleLevelZero(ruleId,outfile,ind);
            --ind;
        outfile << --ind << "};\n";
        outfile << ind << "#endif\n";
    }
    
    
    
}
void PropagatorCompiler::buildAuxMapHandler(){
    for(unsigned ruleId=0; ruleId < program.getRulesSize(); ruleId++){
        ruleOrdering.push_back(auxMapCompiler->declarePropagatorDataStructure(program.getRule(ruleId)));
    }
}
        