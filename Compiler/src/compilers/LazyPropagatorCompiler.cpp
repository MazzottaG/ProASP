#include "LazyPropagatorCompiler.h"

LazyPropagatorCompiler::LazyPropagatorCompiler(const aspc::Program& program, std::string& execPath, DataStructureCompiler* dc, const std::unordered_map<std::string, std::string>& predToStruct): program(program), execPath(execPath), auxMapCompiler(dc), predicateToStruct(predToStruct), ind(Indentation(0)){
    depManager.buildDependecyGraph(program);
}

void LazyPropagatorCompiler::compile(){
    std::cout <<"Lazy compiler called\n";
    std::vector<std::vector<int>> sccs = depManager.getSCC();

    for(int i = sccs.size() -1; i >= 0; --i){
        std::cout <<"Compiling SCC with lazy propagators\n";
        std::cout <<"Predicates: ";
        for(int j = 0; j < sccs.at(i).size(); ++j){
            std::cout << depManager.getPredicateName(sccs[i][j])<< " ";
        }
        std::cout << std::endl;
        compileSCC(sccs[i], i);
    }
    //compileConstraints();
    compileLazyPropClass();
}

void LazyPropagatorCompiler::compileSCC(std::vector<int> scc, unsigned index){
    openPropagatorFile(index);
    std::vector<unsigned> rulesForComponent;
    for(unsigned predicate : scc){
        std::vector<unsigned> rulesForPredicate = program.getRulesForPredicate(depManager.getPredicateName(predicate));
        for(unsigned rule : rulesForPredicate){
            rulesForComponent.push_back(rule);
        }
    }
    compileFixPointComputation(scc,rulesForComponent);

    //starters:
    //a(X,Y) :- b(X), d(X), c(X,Y).
    //given that component is a, b, d
    //starters is:
    //{ (0) -> <0,1,2>
    //  (1) -> <1,0,2>
    //                } 

    //compileComponentWatched(scc, index);
    closePropagatorFile();
}

void LazyPropagatorCompiler::compileFixPointComputation(std::vector<int> scc, std::vector<unsigned> rules){
    outfile << ind++ << "void computeFixpoint(){\n";
    outfile << ind++ << "{\n";
    std::set<std::string> componentPredicateNames;
    for(unsigned predId : scc){
        componentPredicateNames.insert(depManager.getPredicateName(predId));
    }


    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        auto res = auxMapCompiler->declareGeneratorDataStructure(rule, componentPredicateNames);
        ruleOrderings.emplace(ruleID, res.first);

    }
    std::vector<unsigned> nonExitRules = findNonExitRule(scc, rules);
    bool isRecursive = nonExitRules.size() > 0;
    //print stack
    if(isRecursive){
        outfile << ind << "std::vector<int> stack;\n";
    }
    //compile exit and non exit rule to be executed once with default starter
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        compileRuleByStarter(ruleID, rule, rule.getFormulas().size(), componentPredicateNames, isRecursive);
    }
    if(isRecursive){
        outfile << ind++ << "while(!stack.empty()){\n";
        outfile << ind << "Tuple* tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
        outfile << ind << "stack.pop_back();\n";
    }
    //compile recursive rules inside while
    //one compilation for every starter in the body
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        int formulaID = 0;
        for(const aspc::Formula* f : rule.getFormulas()){ 
            if(f->isLiteral() && f->isPositiveLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)f;
                if(std::find(componentPredicateNames.begin(), componentPredicateNames.end(), lit->getPredicateName()) != componentPredicateNames.end()){
                    compileRuleByStarter(ruleID, rule, formulaID, componentPredicateNames, isRecursive);
                }
            }
            formulaID++;
        }
    }
    if(isRecursive){
        outfile << --ind << "}\n";
    }
    //scc scope
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
}

std::vector<unsigned> LazyPropagatorCompiler::findNonExitRule(std::vector<int> scc, std::vector<unsigned> rules){
    std::vector<unsigned> nonExit;
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        bool exit = true;
        for(const aspc::Literal& lit : rule.getBodyLiterals()){
            if(std::find(scc.begin(), scc.end(), depManager.getPredicateId(lit.getPredicateName())) != scc.end()){
                exit = false;
                break;
            }
        }
        if(!exit)
            nonExit.push_back(ruleID);
    }
    return nonExit;
}

void LazyPropagatorCompiler::compileRuleByStarter(unsigned id, const aspc::Rule& rule, unsigned starter, const std::set<std::string>& componentPreds, bool isRecursive){
    //std::cout <<"compiling rule: ";
    rule.print();
    std::cout <<"\n";
    int closingPars = 0;
    outfile << ind++ << "{\n";
    const std::vector<const aspc::Formula*> formulas = rule.getFormulas();
    std::unordered_set<std::string> boundVars;

    outfile << ind << "std::vector<std::pair<std::pair<const Tuple *, bool>, int>> insertResults;\n";
    //when starter is a body literal that literal is not in the ordered body formulas
    int numberOfFormulas = starter == rule.getFormulas().size() ? ruleOrderings[id][starter].size() : ruleOrderings[id][starter].size() +1;
    for(unsigned i = 0; i < numberOfFormulas; ++i){
        const aspc::Formula* formula = formulas[numberOfFormulas == rule.getFormulas().size() ? i : i-1];
        
        if(formula->isLiteral()){
            if(i == 0){
                outfile << ind << "bool undefTuple_" << i << " = false;\n";
            }
            else{
                outfile << ind << "bool undefTuple_" << i << " = undefTuple_" << i-1 << ";\n";
            }
        }
        //compile starter literal
        if(starter != formulas.size() && i == 0){
            const aspc::Literal* lit = (const aspc::Literal*)formula;
            for (unsigned k = 0; k < lit->getAriety(); k++)
            {
                //declare vars
                if(lit->isVariableTermAt(k)){
                    outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<i<<"->at("<<k<<");\n";
                    boundVars.insert(lit->getTermAt(k));
                }
            }
            outfile << ind << "undefTuple_" << i << " = tuple_0->isUndef();\n";
            outfile << ind++ << "if(tuple_"<<i<<" != NULL){\n";
            closingPars++;
        }else{
            if(formula->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)formula;
                if(lit->isBoundedLiteral(boundVars)){
                    //bound lit
                    outfile << ind << "Tuple* tuple_" << i << " = TupleFactory::getInstance().find({";
                    for (unsigned k = 0; k < lit->getAriety(); k++)
                    {
                        if (k > 0)
                            outfile << ",";
                        outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\"" + lit->getTermAt(k) + "\")");
                    }
                    outfile << "}, AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
                    bool isComponentLit = std::find(componentPreds.begin(), componentPreds.end(), lit->getPredicateName()) != componentPreds.end(); 
                    //define boundTupleUndef
                    if(lit->isNegated()){
                        if(isComponentLit){
                            outfile << ind << "if(tuple_" << i << " == NULL || "<<" !tuple_" << i << "->isTrue()) undefTuple_" << i << " = true;\n";
                        }else{
                            outfile << ind << "if(tuple_" << i << " != NULL && "<<"tuple_" << i << "->isUndef()) undefTuple_" << i << " = true;\n";
                        }
                        outfile << ind++ << "if(tuple_" << i <<" == NULL || !tuple_" << i << "->isTrue()){\n";    
                    }else{
                        outfile << ind << "if(tuple_" << i << " != NULL && "<<"tuple_" << i << "->isUndef()) undefTuple_" << i << " = true;\n";
                        outfile << ind++ << "if(tuple_" << i <<" != NULL){\n";
                    }
                    closingPars++;
                }else{
                    std::string prefix = "AuxMapHandler::getInstance().get_";
                    std::string mapName = lit->getPredicateName()+"_";
                    std::string terms = "";
                    std::unordered_set<int> boundIndices;
                    std::string predStruct = predicateToStruct[lit->getPredicateName()];
                    std::string structType = "std::vector<int>*";

                    for(unsigned k=0; k<lit->getAriety(); k++){
                        if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                            std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                            mapName+=std::to_string(k)+"_";
                            terms += (terms != "" ? ","+term : term);
                            boundIndices.insert(k);
                        }
                    }

                    outfile << ind << structType <<" tuples_"<<i<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                    outfile << ind << structType << " tuplesU_"<<i<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                    outfile << ind++ << "for(auto i=tuples_"<<i<<"->begin(); i != tuplesU_"<<i<<"->end(); i++){\n";
                    
                    closingPars++;
                    outfile << ind << "if(i == tuples_"<<i<<"->end()) i=tuplesU_"<<i<<"->begin();\n";
                    outfile << ind << "if(i == tuplesU_"<<i<<"->end()) break;\n";
                    outfile << ind << "Tuple* tuple_"<<i<<" = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";

                    outfile << ind++ << "if(tuple_"<<i<<" != NULL){\n";
                    closingPars++;
                    for(unsigned k=0; k<lit->getAriety(); k++){
                        if(lit->isVariableTermAt(k) && !boundIndices.count(k)){
                            if(!boundVars.count(lit->getTermAt(k))){
                                outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<i<<"->at("<<k<<");\n";
                                boundVars.insert(lit->getTermAt(k));
                            }else{
                                outfile << ind++ << "if("<< lit->getTermAt(k)<< " == tuple_"<<i<<"->at("<<k<<")){\n";
                                closingPars++;
                            }
                        }
                    }
                }
            
            }else{
                const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) formula;
                if(formula->isBoundedValueAssignment(boundVars)){
                    outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                    boundVars.insert(ineq->getAssignedVariable(boundVars));
                }else{
                    outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                    closingPars++;
                }
            }
        }
        if(i == formulas.size() -1){
            outfile << ind << "//Rule is firing;\n";
        }
    }
    std::vector<aspc::Atom> head = rule.getHead();
    for(int index=0;index<head.size();index++){
        aspc::Atom* atom = &head[index];
        outfile << ind << "Tuple* head_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";
        for(unsigned k=0; k<atom->getAriety(); k++){
            if(k>0) outfile << ",";
            outfile << (atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+atom->getTermAt(k)+"\")");
        }
        outfile << "}, AuxMapHandler::getInstance().get_"<<atom->getPredicateName()<<"(),false);\n";
        outfile << ind << "std::pair<const Tuple *, bool> insertResult;\n";
        outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId()) && head_" << index << "->isUnknown()){\n";
        if(isRecursive){
            if(std::find(componentPreds.begin(), componentPreds.end(), atom->getPredicateName()) != componentPreds.end()){
                outfile << ind << "stack.push_back(head_" << index << "->getId());\n";
            }
        }
        outfile << ind << "AuxMapHandler::getInstance().initTuple(head_" << index << ");\n";
        outfile << ind++ << "if(undefTuple_" << formulas.size() -1 << "){\n";
        outfile << ind << "insertResult = head_" << index <<"->setStatus(TruthStatus::Undef);\n";
        outfile << ind << "insertResults.push_back(std::make_pair(insertResult, LazyPropagator::INSERT_AS_UNDEF));\n";
        outfile << --ind << "}\n";
        outfile << ind++ << "else{\n";
        outfile << ind << "insertResult = head_" << index <<"->setStatus(TruthStatus::True);\n";
        outfile << ind << "insertResults.push_back(std::make_pair(insertResult, LazyPropagator::INSERT_AS_TRUE));\n";
        outfile << --ind << "}\n";
             
        outfile << --ind << "}\n";                              
    }
    for (int i = closingPars; i > 0; --i) {
        outfile << --ind << "}//close par\n";
        //just before closing rule scope
        if(i == 1){
            outfile << ind++ << "for(unsigned i = 0; i < insertResults.size(); ++i){\n";
            outfile << ind << "if(insertResults[i].second == LazyPropagator::INSERT_AS_TRUE) AuxMapHandler::getInstance().insertTrue(insertResults[i].first);\n";
            outfile << ind << "else if(insertResults[i].second == LazyPropagator::INSERT_AS_UNDEF) AuxMapHandler::getInstance().insertUndef(insertResults[i].first);\n";
            outfile << ind++ << "else if(insertResults[i].second == LazyPropagator::REMOVE_FROM_UNDEF){\n";
            outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(insertResults[i].first.first->getId());\n";
            outfile << ind << "AuxMapHandler::getInstance().initTuple(TupleFactory::getInstance().getTupleFromInternalID(insertResults[i].first.first->getId()));\n";
            outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResults[i].first);\n";
            outfile << --ind <<"}\n";
            outfile << --ind <<"}\n";           
        }
        
    }
    //std::cout <<std::endl;
    outfile << --ind << "}\n";
}
void LazyPropagatorCompiler::openPropagatorFile(unsigned compID){

    ind = Indentation(0);
    std::string prefix = "Comp";
    std::string className = prefix +"_"+std::to_string(compID)+"_Propagator";
    propagatorNames.push_back(className);
    std::string executorPath = execPath + "/../../glucose-4.2.1/sources/simp/propagators/"+className+".h";
    outfile =  std::ofstream(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open " + className + " file "<< executorPath << std::endl;
        exit(180);
    } 
    outfile << ind << "#ifndef " << className << "_H\n";
    outfile << ind << "#define " << className << "_H\n";

    outfile << ind << "#include <vector>\n";
    outfile << ind << "#include \"../datastructures/TupleFactory.h\"\n";
    outfile << ind << "#include \"../datastructures/AuxiliaryMapSmart.h\"\n";
    outfile << ind << "#include \"../solver/AuxMapHandler.h\"\n";
    outfile << ind << "#include \"../solver/AbstractPropagator.h\"\n";
    outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
    outfile << ind << "#include \"../datastructures/VectorAsSet.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

    outfile << ind++ << "class " << className << ": public AbstractLazyPropagator{\n";
    outfile << ind << "std::vector<int> tuplesEmpty;\n";
    outfile << ind << "IndexedSet tuplesSetEmpty;\n";
    outfile << ind++ << "public:\n";
    outfile << ind << className << "(){}\n";
}

void LazyPropagatorCompiler::closePropagatorFile(){
    --ind;
    outfile << --ind << "};\n";
    outfile << ind << "#endif\n";
}

void LazyPropagatorCompiler::compileComponentWatched(std::vector<int> scc, unsigned index){
    outfile << ind << "virtual void printName()const {std::cout << \"External positive-cycle Propagator "<<index<<"\"<<std::endl;}\n";
    outfile << ind++ << "virtual void attachWatched() override {\n";
    std::unordered_map<std::string, int> attached;
    for(unsigned i = 0; i < scc.size(); ++i){
        for(unsigned ruleID : program.getRulesForPredicate(depManager.getPredicateName(scc[i]))){
            compileRuleWatcher(ruleID, attached);
        }
    }
    outfile << --ind << "} //function\n";
}

void LazyPropagatorCompiler::compileRuleWatcher(unsigned ruleId, std::unordered_map<std::string, int>& attached){
    const aspc::Rule rule = program.getRule(ruleId);
    const std::vector<aspc::Literal>& body = rule.getBodyLiterals();

    //attach watchers for head predicates 
    const std::vector<aspc::Atom>* headAtoms = &rule.getHead();
    for(int i = 0; i < headAtoms->size(); i++){
        const aspc::Atom* head = &headAtoms->at(i);
        std::string predicate = head->getPredicateName();
        std::string predStruct = predicateToStruct[predicate];
        std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

        auto attachedValue = attached.emplace(predicate,2);
        if(attachedValue.second){
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
                for(unsigned k = 0; k < head->getAriety(); k++){
                    if(!head->isVariableTermAt(k) || boundVars.count(head->getTermAt(k))){
                        std::string term = isInteger(head->getTermAt(k)) || head->isVariableTermAt(k) ? head->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head->getTermAt(k)+"\")";
                        outfile << ind++ << "if(tuple->at("<<k<<") == " << term << "){\n";
                        closingPars++;
                    }else{
                        outfile << ind << "int "<<head->getTermAt(k) << " = tuple->at(" <<k<< ");\n"; 
                        boundVars.insert(head->getTermAt(k));
                    }
                }
                outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";             
                outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                
                while(closingPars>0){
                    outfile << --ind << "}\n";
                    closingPars--;
                }
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";
        }
    }
    const std::vector<aspc::Literal>* bodyLiterals = &rule.getBodyLiterals();
    for(int litId = 0; litId < bodyLiterals->size(); litId++){
        const aspc::Literal* lit = &bodyLiterals->at(litId);
        std::string predicate = lit->getPredicateName();
        std::string predStruct = predicateToStruct[predicate];
        std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

        auto attachedValue = attached.emplace(predicate,2);
        if(attachedValue.second){
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

                    if(attachedValue.first->second != 1)
                        outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,false);\n";
                    
                    if(attachedValue.first->second != -1)
                        outfile << ind << "TupleFactory::getInstance().addWatcher(this->getId(),id,true);\n";
                    
                    
                    while(closingPars>0){
                        outfile << --ind << "}\n";
                        closingPars--;
                    }
                outfile << --ind << "}\n";
            outfile << --ind << "}\n";
        }

    }

}

void LazyPropagatorCompiler::compileLazyPropClass(){
    ind = Indentation(0);
    std::string executorPath = execPath + "/../../glucose-4.2.1/sources/simp/propagators/LazyPropagator.cc";
    std::ofstream outfile(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open Generator file "<<executorPath<<std::endl;
        exit(180);
    } 

    outfile << ind << "#include \"../solver/LazyPropagator.h\"\n\n";
    for(unsigned i = 0; i < propagatorNames.size(); ++i){
        std::string className = propagatorNames[i];
        outfile << ind << "#include \"../propagators/"<<className<<".h\"\n\n";
    }
    outfile << ind << "int LazyPropagator::INSERT_AS_UNDEF = 0;\n";
    outfile << ind << "int LazyPropagator::INSERT_AS_TRUE = 1;\n";
    outfile << ind << "int LazyPropagator::REMOVE_FROM_UNDEF = 2;\n";
    outfile << ind++ << "LazyPropagator::LazyPropagator(){\n";
    //int propagatorId = 0;
    for(unsigned i = 0; i < propagatorNames.size(); ++i){
        std::string className = propagatorNames[i];
        //std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
        outfile << ind << "propagators.push_back(new "<<className<<"());\n";
        //outfile << ind << "propagators.back()->setId("<<propagatorId<<");\n";
        //propagatorId++;
    }
    outfile << --ind << "}\n";
}