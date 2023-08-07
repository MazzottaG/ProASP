#include "GeneratorCompiler.h"
void GeneratorCompiler::compile(){
    buildAuxMapHandler();
    buildGenerator();
}
void GeneratorCompiler::buildComponentGenerator(int componentId){
    Indentation ind(0);
    std::string className=compPrefix+"_"+std::to_string(componentId)+"_Gen";
    std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/generators/"+className+".h";
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
    outfile << ind << "#include \"../solver/AbstractGenerator.h\"\n";
    outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";
    outfile << ind << "typedef std::vector<const Tuple* > Tuples;\n";

    outfile << ind << "class "<<className<<": public AbstractGenerator{\n";
    outfile << ++ind << "public:\n";
    ind++;
        outfile << ind++ << "void generate(Glucose::SimpSolver* solver)override {\n";
            bool isRecursive = components[componentId].size() > 1;
            if(!isRecursive){
                std::string predicate = *components[componentId].begin();
                for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                    aspc::Rule r = program.getRule(ruleIndex);
                    const std::vector<const aspc::Formula*>& body = r.getFormulas();
                    for(unsigned i = 0; i<body.size(); i++){
                        if(body[i]->isLiteral() && body[i]->isPositiveLiteral()){
                            const aspc::Literal* lit = (const aspc::Literal*) body[i];
                            if(predicate == lit->getPredicateName()){
                                isRecursive=true;
                                break;
                            }
                        }
                    }
                    if(isRecursive) break;
                }                 
            }
            if(isRecursive)
                outfile << ind << "std::vector<int> stack;\n";
            for(const std::string& predicate: components[componentId]){
                for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                    compileComponentRules(outfile,ind,program.getRule(ruleIndex).getFormulas().size(),componentId,isRecursive,ruleIndex);
                }
            }
            if(isRecursive){
                outfile << ind++ << "while(!stack.empty()){\n";
                    outfile << ind << "Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
                    outfile << ind << "stack.pop_back();\n";
                    outfile << ind++ << "if(starter != NULL){\n";
                    if(isDatalog){
                        outfile << ind << "const auto& insertResult = starter->setStatus(True);\n";
                        outfile << ind++ << "if(insertResult.second){\n";
                            #ifdef DEBUG_GEN
                            outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(starter);\n";
                            #endif
                            outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(starter->getId());\n";
                            outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
                            if(!modelFound)
                                outfile << ind << "while (starter->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                        outfile << --ind << "}else continue;\n";
                    }else{
                        outfile << ind << "const auto& insertResult = starter->setStatus(Undef);\n";
                        outfile << ind++ << "if(insertResult.second){\n";
                            #ifdef DEBUG_GEN
                            outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(starter);\n";
                            #endif
                            outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(starter->getId());\n";
                            outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                            outfile << ind << "while (starter->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                        outfile << --ind << "}else continue;\n";
                    }
                    for(const std::string& predicate: components[componentId]){
                        for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                            aspc::Rule r = program.getRule(ruleIndex);
                            const std::vector<const aspc::Formula*>& body = r.getFormulas();
                            for(unsigned starter = 0; starter < body.size(); starter++){
                                const aspc::Formula* startingFormula = body[starter];
                                if(!startingFormula->isLiteral() || !startingFormula->isPositiveLiteral()) continue;
                                
                                // starting formula is a positive literal
                                const aspc::Literal* literal = (const aspc::Literal*) startingFormula;
                                
                                if(!components[componentId].count(literal->getPredicateName())) continue;
                                    
                                compileComponentRules(outfile,ind,starter,componentId,isRecursive,ruleIndex);
                            }
                        }
                    }           
                    outfile << --ind << "} else std::cout << \"Warning null tuple in generation stack\"<<std::endl;\n";
                outfile << --ind << "}\n";
            }
            #ifdef DEBUG_GEN
            outfile << ind << "std::cout << \"Generator "<<className<<"\"<<std::endl;\n";
            #endif
        outfile << --ind << "}\n";
    ind--;
    outfile << --ind << "};\n";
    
    outfile << ind << "#endif\n";
    outfile.close();
}
void GeneratorCompiler::compileComponentRules(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleIndex){
    std::string className=compPrefix+"_"+std::to_string(componentId)+"_Gen";
    aspc::Rule r = program.getRule(ruleIndex);
    const std::vector<const aspc::Formula*>& body = r.getFormulas();
    std::unordered_set<std::string> boundVars;
    int closingPars=0;
    
    if(starter != body.size()){
        const aspc::Literal* startingLit = (const aspc::Literal*) body[starter];
        outfile << ind++ << "if(starter->getPredicateName() == AuxMapHandler::getInstance().get_"<<startingLit->getPredicateName()<<"()){\n";
        closingPars++;
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
    }else{
        outfile << ind++ << "{\n";
        closingPars++;
    }
    
    std::vector<unsigned>& order = ruleOrdering[ruleIndex][starter];
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
                    if(isDatalog){
                        outfile << ind++ << "if(boundTuple_"<<index<<" == NULL || boundTuple_"<<index<<"->isFalse()){\n";
                    }else{
                        outfile << ind++ << "if(boundTuple_"<<index<<" == NULL || !boundTuple_"<<index<<"->isTrue()){\n";
                    }
                }else{
                    if(isDatalog){
                        outfile << ind++ << "if(boundTuple_"<<index<<" != NULL && boundTuple_"<<index<<"->isTrue()){\n";
                    }else{
                        outfile << ind++ << "if(boundTuple_"<<index<<" != NULL && !boundTuple_"<<index<<"->isFalse()){\n";
                    }
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

                outfile << ind << structType <<" tuples_"<<index<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                if(!isDatalog){
                    outfile << ind << structType << " tuplesU_"<<index<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                }
                if(!isDatalog)
                    outfile << ind++ << "for(auto i=tuples_"<<index<<"->begin(); i != tuplesU_"<<index<<"->end(); i++){\n";
                else
                    outfile << ind++ << "for(auto i=tuples_"<<index<<"->begin(); i != tuples_"<<index<<"->end(); i++){\n";
                closingPars++;
                    if(!isDatalog){
                        outfile << ind << "if(i==tuples_"<<index<<"->end()) i=tuplesU_"<<index<<"->begin();\n";
                        outfile << ind << "if(i==tuplesU_"<<index<<"->end()) break;\n";
                        outfile << ind << "Tuple* tuple_"<<index<<"= TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                    }
                    else
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
    //storing possible heads
    std::vector<aspc::Atom> head = r.getHead();
    for(int index=0;index<head.size();index++){
        aspc::Atom* atom = &head[index];
        outfile << ind << "Tuple* head_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";
        for(unsigned k=0; k<atom->getAriety(); k++){
            if(k>0) outfile << ",";
            outfile << (atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+atom->getTermAt(k)+"\")");
        }
        outfile << "}, AuxMapHandler::getInstance().get_"<<atom->getPredicateName()<<"(),"<<(originalPredicates.count(atom->getPredicateName()) ? "false" : "true")<<");\n";
        outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId())){\n";
            #ifdef DEBUG_GEN
            outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(head_"<<index<<");\n";
            #endif
            if(isRecursive){
                outfile << ind << "stack.push_back(head_"<<index<<"->getId());\n";
            }else{
                if(isDatalog){
                    outfile << ind << "const auto& insertResult = head_"<<index<<"->setStatus(True);\n";
                    outfile << ind++ << "if(insertResult.second){\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(head_"<<index<<"->getId());\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
                        if(!modelFound)
                            outfile << ind << "while (head_"<<index<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                    outfile << --ind << "}\n";
                }else{
                    outfile << ind << "const auto& insertResult = head_"<<index<<"->setStatus(Undef);\n";
                    outfile << ind++ << "if(insertResult.second){\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(head_"<<index<<"->getId());\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                        outfile << ind << "while (head_"<<index<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                    outfile << --ind << "}\n";
                }
            }  
        outfile << --ind << "}\n";                              
    }
    while (closingPars > 0){
        outfile << --ind << "}// closing"<<std::endl;
        closingPars--;
    }
}
void GeneratorCompiler::buildGenerator(){
    computeSCC();
    Indentation ind(0);
    std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/generators/"+generatorClass+".cc";
    std::ofstream outfile(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open Generator file "<<executorPath<<std::endl;
        exit(180);
    } 

    outfile << ind << "#include \"../solver/"<<generatorClass<<".h\"\n\n";
    for(int componentId = components.size()-1; componentId >= 0; componentId--){
        std::string className=compPrefix+"_"+std::to_string(componentId)+"_Gen";
        outfile << ind << "#include \"../generators/"<<className<<".h\"\n\n";
    }
    outfile << ind++ <<generatorClass<<"::"<<generatorClass<<"(){\n";
    for(int componentId = components.size()-1; componentId >= 0; componentId--){
        buildComponentGenerator(componentId);
        std::string className=compPrefix+"_"+std::to_string(componentId)+"_Gen";
        outfile << ind << "generators.push_back(new "<<className<<"());\n";
        outfile << ind << "solvedByGenerator = " << (solvedByGenerator ? "true" : "false")<<";\n";
    }
    outfile << --ind << "}\n";
    outfile.close();

    
}
void GeneratorCompiler::buildAuxMapHandler(){
    
    computeSCC();

    for(int componentId = components.size()-1; componentId >= 0; componentId--){
        for(const std::string& predicate : components[componentId]){
            for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                if(ruleIndex >= ruleOrdering.size()){
                    ruleOrdering.resize(ruleIndex+1);
                }
                ruleOrdering[ruleIndex] = auxMapCompiler->declareGeneratorDataStructure(program.getRule(ruleIndex),components[componentId]);
            }
        }
    }
	
}
void GeneratorCompiler::buildPositiveDG(){
    for(const aspc::Rule& r : program.getRules()){
        for(const aspc::Atom& a : r.getHead()){
            auto it =local_predicates.emplace(a.getPredicateName(),localPredicatesName.size());
            if(it.second){
                pdg.addNode(localPredicatesName.size());
                localPredicatesName.push_back(a.getPredicateName());
            }
        }
        for(const aspc::Literal& l : r.getBodyLiterals()){
            if(l.isPositiveLiteral()){
                auto it =local_predicates.emplace(l.getPredicateName(),localPredicatesName.size());
                if(it.second){
                    pdg.addNode(localPredicatesName.size());
                    localPredicatesName.push_back(l.getPredicateName());
                }
                for(const aspc::Atom& a : r.getHead()){
                    unsigned headPred =local_predicates[a.getPredicateName()];
                    pdg.addEdge(it.first->second,headPred);
                }
            }
        }
    }
}
void GeneratorCompiler::computeSCC(){
    if(!builtSCC){
        builtSCC=true;
        buildPositiveDG();
        scc = pdg.SCC();
        for(unsigned componentId=0;componentId<scc.size(); componentId++){
            components.push_back({});
            std::set<std::string>* component=&components.back();
            for(unsigned i=0;i<scc[componentId].size();i++){
                component->insert(localPredicatesName[scc[componentId][i]]);
            }
        }
    }
    
}
