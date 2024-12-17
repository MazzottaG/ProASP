#include "LazyPropagatorCompiler.h"

LazyPropagatorCompiler::LazyPropagatorCompiler(const aspc::Program& program, std::string& execPath, DataStructureCompiler* dc, const std::unordered_map<std::string, std::string>& predToStruct): program(program), execPath(execPath), auxMapCompiler(dc), predicateToStruct(predToStruct), ind(Indentation(0)){
    depManager.buildDependecyGraph(program);
}

void LazyPropagatorCompiler::setAlwaysToCheckPredicates(std::unordered_set<std::string> alwaysToCheckPredicates){
    this->alwaysToCheckPredicates = alwaysToCheckPredicates;
}

void LazyPropagatorCompiler::compile(){
    std::cout <<"Lazy compiler called\n";
    compileTupleFactoryCC();
    std::vector<std::vector<int>> sccs = depManager.getSCC();
    positiveProgramHeadPredicates = program.getHeadPredicates();
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

void LazyPropagatorCompiler::compileTupleFactoryCC(){
    ind = Indentation(0);
    std::string className = "TupleFactory.cc";

    std::string executorPath = execPath + "/../../glucose-4.2.1/sources/simp/solver/"+className;
    outfile =  std::ofstream(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open " + className + " file "<< executorPath << std::endl;
        exit(180);
    }
    outfile << ind << "#include \"../datastructures/TupleFactory.h\"\n";
    outfile << ind << "#include \"../../core/Solver.h\"\n";
    outfile << ind << "#include \"AuxMapHandler.h\"\n";
    outfile << ind << "#include \"LazyPropagator.h\"\n";
    outfile << ind << "TupleLight TupleFactory::bufferTuple;\n";
    outfile << ind << "bool TupleFactory::usedFindNoSet=false;\n";
    outfile << ind << "std::vector<unsigned> TupleFactory::EMPTY_WATCHER;\n";
    outfile << ind << "\n";

    // std::set<std::string> headPredicates = program.getHeadPredicates();
    // for(std::string predName: headPredicates){
    //     outfile << ind << "allAssigned = !(AuxMapHandler::getInstance().get_u" << predName << "_()->getValuesVec({}).size() > 0);\n";
    // }
    // std::set<std::string> bodyPredicates = program.getBodyPredicates();
    // for(std::string predName: bodyPredicates){
    //     outfile << ind << "allAssigned = !(AuxMapHandler::getInstance().get_u" << predName << "_()->getValuesVec({}).size() > 0);\n";
    // }
    // totalNumOfPredicates = headPredicates.size() + bodyPredicates.size();


    outfile << ind++ << "Glucose::vec<Glucose::Lit>& TupleFactory::explain(unsigned var){\n";
    outfile << ind << "assert(var<internalIDToTuple.size());\n";
    outfile << ind++ << "if(propagatedByLazyPropTuples.count(var)){\n";
    outfile << ind << "trueTupleReasons.clear();\n";
    outfile << ind << "LazyPropagator::getInstance().explainTrueLiteral(var, trueTupleReasons);\n";
    outfile << ind << "return trueTupleReasons;\n";
    outfile << --ind <<"}\n";
    outfile << ind <<"else return internalIDToTuple[var]->getReasonLits();\n";
    outfile << --ind << "}\n";

    outfile << ind++ << "void TupleFactory::explainNoAnalyze(unsigned var, Glucose::vec<Glucose::Lit>& tupleReasons, std::unordered_set<int>* reasonSet){\n";
    outfile << ind << "assert(var<internalIDToTuple.size());\n";
    outfile << ind++ << "if(propagatedByLazyPropTuples.count(var)){\n";
    outfile << ind << "LazyPropagator::getInstance().explainTrueLiteral(var, tupleReasons, reasonSet);\n";
    outfile << --ind <<"}\n";
    outfile << ind++ <<"else{\n";
    
    outfile << ind++ << "if(!reasonSet->count(var)){\n";
    outfile << ind << "int levelFromProp = LazyPropagator::getInstance().getSolver()->levelFromPropagator(var);\n";
    outfile << ind << "tupleReasons.push(Glucose::mkLit(var, true));\n";
    outfile << ind++ << "if(levelFromProp > 0 && levelFromProp == LazyPropagator::getInstance().getSolver()->currentLevel())\n";
    outfile << ind << "LazyPropagator::getInstance().switchIfNoCurrentLevelTupleFound(tupleReasons.size()-1, tupleReasons);\n";
    --ind;
    outfile << ind << "reasonSet->insert(var);\n";
    outfile << --ind << "}\n";
    // outfile << ind << "if(LazyPropagator::getInstance().getSolver()->levelFromPropagator(var) > 0) tupleReasons.push(Glucose::mkLit(var, true));\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";

    outfile << ind++ << "void TupleFactory::notifyTupleDeleted(int tupleId){\n";
    outfile << ind << "PositiveProgramFactory::getInstance().removePossibleSupportsFromUndo(tupleId, true);\n";
    outfile << ind << "PositiveProgramFactory::getInstance().onDeleteLazyTuple(tupleId);\n";
    outfile << --ind << "}\n";
    outfile << ind++ << "void TupleFactory::notifyTupleLostSupport(int tupleId, int predicateId){\n";
    outfile << ind << "PositiveProgramFactory::getInstance().addToCheckTuple(tupleId);\n";
    outfile << ind << "LazyPropagator::getInstance().addAlwaysToCheckTuple(tupleId, predicateId);\n";
    outfile << --ind << "}\n";
    outfile << ind++ << "void TupleFactory::notifyAddedCheckedTuple(int tupleId){\n";
    outfile << ind << "LazyPropagator::getInstance().removeAlwaysToCheckTuple(tupleId);\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileSCC(std::vector<int> scc, unsigned index){
    std::vector<unsigned> rulesForComponent;
    for(unsigned predicate : scc){
        std::vector<unsigned> rulesForPredicate = program.getRulesForPredicate(depManager.getPredicateName(predicate));
        for(unsigned rule : rulesForPredicate){
            rulesForComponent.push_back(rule);
        }
    }
    std::set<std::string> componentPredicateNames;
    for(unsigned predId : scc){
        componentPredicateNames.insert(depManager.getPredicateName(predId));
    }
    std::vector<unsigned> nonExitRules = findNonExitRule(scc, rulesForComponent);

    for(unsigned ruleID : rulesForComponent){
        const aspc::Rule& rule = program.getRule(ruleID);
        auto res = auxMapCompiler->declarePropagatorDataStructure(rule);
        ruleOrderings.emplace(ruleID, res.first);
        ruleOrderingsByHead.emplace(ruleID, res.second);
        auto res1 = auxMapCompiler->declareExplainFalseDataStructure(rule, positiveProgramHeadPredicates);//, componentPredicateNames);
        ruleOrderingsExplainFalse.emplace(ruleID, res1);
        // std::cout <<"Rule ID: " << ruleID << " ORDERINGS\n";
        // for(int i = 0; i< res.first.size(); ++i){
        //     std::cout <<"Starter: " << i << "\n\t";
        //     for(int j = 0; j< res.first.at(i).size(); ++j){
        //         std::cout << res.first.at(i).at(j)<< " ";
        //     }
        //     std::cout <<std::endl;
        // }
    }
    openPropagatorFile(index, componentPredicateNames);
    compileFixPointComputationLevelZero(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    compileFixPointComputation(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    compileExplainFalse(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    compileComponentWatched(scc, rulesForComponent);
    compileStopPropagateToFalse();
    closePropagatorFile();
}

void LazyPropagatorCompiler::compileFixPointComputationLevelZero(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "std::pair<bool, Glucose::CRef> computeFixpointLevelZero(Glucose::Solver* s, Glucose::vec<Glucose::Lit>& lits){\n";
    outfile << ind++ << "{\n";
    //std::cout <<"Orderings: \n";
    bool isRecursive = nonExitRules.size() > 0;
    outfile << ind << "std::vector<int> stack;\n";
    outfile << ind << "bool generated = false;\n";
    outfile << ind << "Glucose::CRef confl;\n";

    //exit rule compilation
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        if(std::find(nonExitRules.begin(), nonExitRules.end(), ruleID) == nonExitRules.end())
            compileRuleByStarter(ruleID, rule, rule.getFormulas().size(), componentPredicateNames, isRecursive, true, false, true);

    }
    //nonExitRules by default starter
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        if(std::find(nonExitRules.begin(), nonExitRules.end(), ruleID) != nonExitRules.end())
            compileRuleByStarter(ruleID, rule, rule.getFormulas().size(), componentPredicateNames, isRecursive, true, false, false);

    }
    outfile << ind++ << "while(!stack.empty()){\n";
    outfile << ind <<"Tuple* tuple_0;\n";
    outfile << ind << "tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
    outfile << ind << "bool sign = tuple_0->isTrue();\n";
    outfile << ind << "stack.pop_back();\n";
    //compile rules inside while
    //one compilation for every starter in the body that is a predicate of the component
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        //orders are head, body
        int formulaID = 0;
        for(const aspc::Formula* f : rule.getFormulas()){
            if(f->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)f;
                if(std::find(componentPredicateNames.begin(), componentPredicateNames.end(), lit->getPredicateName()) != componentPredicateNames.end()){
                    //positive literal can generate when a tuple of that predicate is set to true,
                    //false literal can generate when a tuple of that predicate is set to false
                    std::string signCondition = lit->isPositiveLiteral() ? "sign" : "!sign";
                    outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "() && " << signCondition << "){\n";
                    compileRuleByStarter(ruleID, rule, formulaID, componentPredicateNames, isRecursive, true, false, false);
                    outfile << --ind <<"}\n";
                }
            }
            formulaID++;
        }
    }
    //compilation inside stack scope
    outfile << --ind << "}\n";

    //scc scope
    outfile << ind << "return std::make_pair(generated, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileFixPointComputation(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "std::pair<bool, Glucose::CRef> computeFixpoint(Glucose::Solver* s, std::vector<int>& propagatedTuples, Glucose::vec<Glucose::Lit>& lits){\n";
    outfile << ind++ << "{\n";
    //std::cout <<"Orderings: \n";
    bool isRecursive = nonExitRules.size() > 0;

    outfile << ind << "std::vector<int> stack = std::vector<int>(propagatedTuples.begin(), propagatedTuples.end());\n";
    outfile << ind << "propagatedTuples.clear();\n";
    outfile << ind << "bool generated = false;\n";

    outfile << ind++ << "while(!stack.empty()){\n";
    outfile << ind <<"Tuple* tuple_0;\n";
    outfile << ind << "tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
    outfile << ind << "bool sign = tuple_0->isTrue();\n";
    outfile << ind << "stack.pop_back();\n";
    //compile rules inside while
    //one compilation for every starter in the body
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        //orders are head, body
        int formulaID = 0;
        for(const aspc::Formula* f : rule.getFormulas()){
            if(f->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)f;
                //positive literal can generate when a tuple of that predicate is set to true,
                //false literal can generate when a tuple of that predicate is set to false
                std::string signCondition = lit->isPositiveLiteral() ? "sign" : "!sign";
                outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "() && " << signCondition << "){\n";
                compileRuleByStarter(ruleID, rule, formulaID, componentPredicateNames, isRecursive, true, false, false);
                outfile << --ind <<"}\n";
            }
            formulaID++;
        }
    }
    //compilation inside stack scope
    outfile << --ind << "}\n";

    //scc scope
    outfile << ind << "return std::make_pair(generated, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}


void LazyPropagatorCompiler::compileExplainFalse(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "std::pair<bool, Glucose::CRef> propagateToFalse(Glucose::Solver* s, Tuple* tuple, Tuple* original, Glucose::vec<Glucose::Lit>& tupleReasons, std::unordered_set<int>& reasonSet, bool makePropagation, bool tupleNegated){\n";
    outfile << ind << "Glucose::vec<Glucose::Lit> lits;\n";
    outfile << ind << "bool canPropagate = true;\n";
    outfile << ind << "unsigned tupleReasonBeforePropF = tupleReasons.size() -1;\n";
    bool isRecursive = nonExitRules.size() != 0;
    if(isRecursive){
        outfile << ind << "std::vector<Tuple*> toExplain;\n";
        outfile << ind << "std::vector<TupleSignSet> toExplainUndefs;\n";
        outfile << ind << "toExplain.push_back(tuple);\n";
        outfile << ind << "toExplainUndefs.push_back(TupleSignSet());\n";
        outfile << ind << "std::unordered_map<int, int> tupleToParent;\n";
        outfile << ind << "std::unordered_map<int, std::unordered_set<int>> tupleToChildren;\n";
    }
    if(!isRecursive)
        outfile << ind << "LazyPropagator::getInstance().addExplainingTuple(tuple->getId());\n";
    outfile << ind << "std::unordered_set<int> dummyTuplesInBody;\n";

    if(isRecursive){
        outfile << ind++ << "while(!toExplain.empty()){\n";
        outfile << ind << "Tuple* tuple_0 = toExplain.back();\n";
        outfile << ind << "toExplain.pop_back();\n";
        outfile << ind << "int toExplainSize = toExplain.size();\n";

        outfile << ind++ << "if(LazyPropagator::getInstance().isTupleAlreadyExplained(tuple_0->getId())){\n";
        outfile << ind << "toExplainUndefs.pop_back();\n";
        outfile << ind << "continue;\n";
        outfile << --ind << "}\n";
        outfile << ind << "for(auto undef : toExplainUndefs.back()) LazyPropagator::getInstance().addBodyLiteral(undef.value, undef.sign);\n";
        outfile << ind << "LazyPropagator::getInstance().addExplainingTuple(tuple_0->getId());\n";
        outfile << ind << "toExplainUndefs.pop_back();\n";
        outfile << ind << "LazyPropagator::getInstance().addAlreadyExplainedTuple(tuple_0->getId());\n";
    }else{
        outfile << ind << "Tuple* tuple_0 = tuple;\n";
    }
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << rule.getHead().at(0).getPredicateName() <<"()){\n";
        bool isExit = std::find(nonExitRules.begin(), nonExitRules.end(), ruleID) == nonExitRules.end();
        compileRuleByStarter(ruleID, rule, -1, componentPredicateNames, isRecursive, false, true, isExit);
        outfile << --ind <<"}\n";
    }
    if(isRecursive){
        outfile << ind++ << "if(toExplainSize == toExplain.size()){\n";
        outfile << ind << "int currentTuple = tuple_0->getId();\n";
        outfile << ind++ << "while(tupleToParent.count(currentTuple)){\n";
        //closing branch and therefore undefs must be removed
        outfile << ind << "LazyPropagator::getInstance().removeBodyLiteralsAddedByTuple(currentTuple, false);\n";
        outfile << ind << "int parentTuple = tupleToParent.at(currentTuple);\n";
        outfile << ind << "tupleToChildren.at(parentTuple).erase(currentTuple);\n";
        outfile << ind << "if(tupleToChildren.at(parentTuple).size() != 0) break;\n";
        outfile << ind << "tupleToParent.erase(currentTuple);\n";
        outfile << ind << "currentTuple = parentTuple;\n";
        outfile << --ind << "}\n";
        outfile << --ind << "}\n";
        outfile << ind << "LazyPropagator::getInstance().removeBodyLiteralsAddedByTuple(tuple_0->getId());\n";
    }

    if(isRecursive){
        //end while
        outfile << --ind << "}\n";
    }

    outfile << ind << "if(tuple->isFalse()) return std::make_pair(false, Glucose::CRef_Undef);\n";
    outfile << ind++ <<"if(makePropagation){\n";
    #ifdef COMPILE_DEBUG_PRINT
        outfile << ind <<"std::cout <<\"Clause for false prop: \\n\";\n";
        outfile << ind++ <<"for(int i = 0; i < tupleReasons.size(); ++i){\n";
        outfile << ind << "std::cout << \"[\";\n";
        outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(tupleReasons[i])));\n";
        outfile << ind << "std::cout <<\", \"<<Glucose::sign(tupleReasons[i]) << \"] \";\n";
        outfile << --ind << "}\n";
        outfile << ind << "std::cout <<std::endl;\n";
    #endif
    outfile << ind << "assert(s->currentLevel() == 0 || tupleReasons.size() >= 2);\n";
    outfile << ind << "bool tupleIsFromInputInterface = TupleFactory::getInstance().isTupleFromInputInterface(original->getId());\n";
    outfile << ind++ << "if(tupleIsFromInputInterface){\n";
    outfile << ind << "bool foundConflict = s->isConflictPropagation(tuple->getId(), true);\n";
    outfile << ind << "bool assigned = s->isAssigned(tuple->getId());\n";
    outfile << ind++ << "if(!assigned || foundConflict){\n";
    outfile << ind++ << "if(s->currentLevel() > 0){\n";
    //reorder reason s.t. solver invariant is respected
    // outfile << ind << "int currentLevelTupleIndex = -1;\n";
    // outfile << ind++ << "for(unsigned i = 1; i < tupleReasons.size(); ++i){\n";
    // outfile << ind++ << "if(s->levelFromPropagator(var(tupleReasons[i])) == s->currentLevel()){\n";
    // outfile << ind << "currentLevelTupleIndex = i;\n";
    // outfile << ind << "break;\n";
    // outfile << --ind << "}\n";
    // outfile << --ind << "}\n";
    // outfile << ind << "assert(currentLevelTupleIndex != -1);\n";
    // outfile << ind << "Glucose::Lit temp = tupleReasons[1];\n";
    // outfile << ind << "tupleReasons[1] = tupleReasons[currentLevelTupleIndex];\n";
    // outfile << ind << "tupleReasons[currentLevelTupleIndex] = temp;\n";
    outfile << ind << "assert(s->levelFromPropagator(Glucose::var(tupleReasons[1])) == s->currentLevel());\n";
    
    outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(tuple->getId());\n";
    outfile << ind << "Glucose::CRef clause = s->externalPropagation(original->getId(), true);\n";
    outfile << ind++ << "if(clause != Glucose::CRef_Undef){\n";
    outfile << ind << "TupleFactory::getInstance().removePropagationFromLazyProp(tuple->getId());\n";
    outfile << --ind << "}\n";
    outfile << ind << "return std::make_pair(true, clause);\n";

    outfile << --ind << "}\n";
    outfile << ind++ <<"else{\n";
    outfile << ind++ << "if(!assigned){\n";
    outfile << ind << "s->assignFromPropagators(Glucose::mkLit(original->getId(), true));\n";
    outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(original->getId());\n";
    outfile << ind << "TupleFactory::getInstance().addCheckedTuple(original->getId());\n";
    outfile << ind << "return std::make_pair(true, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";
    outfile << ind++ << "else if(foundConflict){\n";
    outfile << ind << "lits.clear();\n";
    outfile << ind << "s->addClause_(lits);\n";
    outfile << ind << "return std::make_pair(true, Glucose::CRef_PropConf);\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
    outfile << ind << "return std::make_pair(false, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";
    outfile << ind++ << "else{\n";
    outfile << ind << "return std::make_pair(true, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";

    outfile << --ind <<"}\n";
    outfile << ind << "LazyPropagator::getInstance().removeBodyLiteralsAddedByTuple(tuple->getId());\n";
    outfile << ind << "return std::make_pair(true, Glucose::CRef_Undef);\n";
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

void LazyPropagatorCompiler::compileRuleByStarter(unsigned id, const aspc::Rule& rule, int starter, const std::set<std::string>& componentPreds, bool isRecursive, bool fixpointCompilation, bool explainFalse, bool compileAsExit){
    // std::cout <<"compiling rule: ";
    // rule.print();
    // std::cout <<"\n";
    int closingPars = 0;
    outfile << ind++ << "{\n";

    const std::vector<const aspc::Formula*> formulas = rule.getFormulas();
    std::unordered_set<std::string> boundVars;
    std::vector<int> declaredTuples;
    std::vector<std::pair<int, bool>> reasonTupleWithSign;
    std::unordered_map<int, int> removeBodyLiteralsBlocksAndSymbols;
    std::unordered_map<int, int> removeDummyBlocksAndSymbols;
    std::unordered_map<int, int> removeNegatedUndefBlocks;
    std::vector<int> redirectPropFalseTuples;
    std::unordered_set<int> tupleFromPPIdx;
    //when evaluating rule by started the zero tuple has been declared outside the compileRule
    if(starter != formulas.size()){
        declaredTuples.push_back(0);
    }
    outfile << ind << "std::vector<std::pair<const Tuple *, bool>> insertResults;\n";
    outfile << ind << "std::vector<int> propagations;\n";
    //when starter is a body literal that literal is not in the ordered body formulas
    //-1 is intended as head starter
    int numberOfFormulas;
    if(starter != -1){
        numberOfFormulas = rule.getFormulas().size();
    }
    else{
        numberOfFormulas = rule.getFormulas().size() +1;
    }
    //std::cout <<"number of formulas is " << numberOfFormulas << std::endl;
    for(int i = 0; i < numberOfFormulas; ++i){
        const aspc::Formula* formula = nullptr;
        if(starter == -1){
            //assuming only one head is used
            if(i > 0){
                if(explainFalse)
                    formula = formulas[ruleOrderingsExplainFalse[id][0][i-1]];
                else
                    formula = formulas[ruleOrderingsByHead[id][0][i-1]];
                //std::cout <<"Formula: "<< ruleOrderingsByHead[id][0][i-1] << std::endl;
            }
        }else if(starter == rule.getFormulas().size()){
            formula = formulas[ruleOrderings[id][starter][i]];
            //std::cout <<"Formula: "<< ruleOrderings[id][starter][i] << std::endl;
        }else{
            if(i > 0){
                formula = formulas[ruleOrderings[id][starter][i-1]];
                //std::cout <<"Formula: "<< ruleOrderings[id][starter][i-1] << std::endl;
            }else{
                formula = formulas[starter];
            }
        }

        //compile starter literal
        if(starter != formulas.size() && i == 0){
            const aspc::Literal* lit = nullptr;
            //head starter
            if(starter == -1){
                const aspc::Atom& head = rule.getHead().at(0);
                for (unsigned k = 0; k < head.getAriety(); k++){
                    //declare vars
                    if(head.isVariableTermAt(k) && ! boundVars.count(head.getTermAt(k))){
                        outfile << ind << "int "<< head.getTermAt(k)<< " = tuple_"<<i<<"->at("<<k<<");\n";
                        boundVars.insert(head.getTermAt(k));
                    }else if(!head.isVariableTermAt(k)){
                        std::string term = isInteger(head.getTermAt(k)) || head.isVariableTermAt(k) ? head.getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+head.getTermAt(k)+"\")";
                        outfile << ind++ << "if(tuple_"<<i<<"->at("<<k<<") == " << term << "){\n";
                        closingPars++;
                    }

                }
            }
            else{
                //std::cout <<"Compiling body starter\n";
                //declared tuple for starter literal in body (tuple_0 is declared outside except for body starter)
                //declaredTuples.push_back(i);
                lit = (const aspc::Literal*)formula;
                reasonTupleWithSign.push_back(std::make_pair(i, !lit->isNegated()? true : false));
                for (unsigned k = 0; k < lit->getAriety(); k++){
                    //declare vars
                    if(lit->isVariableTermAt(k) && ! boundVars.count(lit->getTermAt(k))){
                        outfile << ind << "int "<< lit->getTermAt(k)<< " = tuple_"<<i<<"->at("<<k<<");\n";
                        boundVars.insert(lit->getTermAt(k));
                    }else if(!lit->isVariableTermAt(k)){
                        std::string term = isInteger(lit->getTermAt(k)) || lit->isVariableTermAt(k) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                        outfile << ind++ << "if(tuple_"<<i<<"->at("<<k<<") == " << term << "){\n";
                        closingPars++;
                    }
                }
            }

            if(starter != -1 && lit != nullptr){
                if(lit->isNegated()){
                    outfile << ind++ << "if(tuple_"<<i<<" ->isFalse()){\n";
                    closingPars++;
                }
            }else{
                outfile << ind++ << "if(tuple_"<<i<<" != NULL){\n";
                closingPars++;
            }

            if(starter == -1)
                continue;
        }else{
            if(formula->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)formula;
                bool predDefinedInPosProgram = positiveProgramHeadPredicates.count(lit->getPredicateName());
                if(predDefinedInPosProgram) tupleFromPPIdx.insert(i);
                if(lit->isBoundedLiteral(boundVars)){
                    //bound lit
                    declaredTuples.push_back(i);
                    reasonTupleWithSign.push_back(std::make_pair(i, !lit->isNegated()? true : false));
                    outfile << ind << "Tuple* tuple_" << i << " = TupleFactory::getInstance().find({";
                    for (unsigned k = 0; k < lit->getAriety(); k++)
                    {
                        if (k > 0)
                            outfile << ",";
                        outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\"" + lit->getTermAt(k) + "\")");
                    }
                    outfile << "}, AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
                    bool isComponentLit = std::find(componentPreds.begin(), componentPreds.end(), lit->getPredicateName()) != componentPreds.end();
                    
                    if(lit->isNegated()){
                        if(explainFalse){
                            
                            if(predDefinedInPosProgram){
                                outfile << ind << "bool propFalse_" << i << " = false;\n";
                            }
                            outfile << ind << "bool addedBodyLit_" << i << " = false;\n";
                            outfile << ind++ << "if(tuple_" << i << " != NULL){\n";
                            std::string addBodyLitCondition =  predDefinedInPosProgram ? "!TupleFactory::getInstance().isFact(tuple_" + std::to_string(i) + "->getId()) && !TupleFactory::getInstance().isTupleDummy(tuple_" + std::to_string(i) + "->getId()) ": "s->levelFromPropagator(tuple_" + std::to_string(i)+ "->getId()) > 0 || !s->isAssigned(tuple_" + std::to_string(i) + "->getId())";
                            outfile << ind++ << "if(" << addBodyLitCondition << ")\n";
                            outfile << ind << "addedBodyLit_" << i << " = LazyPropagator::getInstance().addBodyLiteral(tuple_" << i << "->getId(), !tupleNegated ? true : false);\n";
                            --ind;
                            outfile << ind++ << "if(tuple_" << i << "->isTrue()){\n";
                            //add reasons of true that will be part of the reasons of propagated to false
                            outfile << ind << "TupleFactory::getInstance().explainNoAnalyze(tuple_" << i << "->getId(), tupleReasons, &reasonSet);\n";
                            outfile << --ind <<"}\n";
                            outfile << --ind <<"}\n";
                            if(predDefinedInPosProgram){
                                //NULL and explainFalse -> create tuple and check if it is false
                                outfile << ind++ <<"else{\n";
                                outfile << ind << "std::pair<Tuple*, bool> tupleAndAdded_" << i << " = TupleFactory::getInstance().addNewLazyFalseTuple({";
                                for (unsigned k = 0; k < lit->getAriety(); k++)
                                {
                                    if (k > 0)
                                        outfile << ",";
                                    outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\"" + lit->getTermAt(k) + "\")");
                                }
                                outfile << "}, AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
                                outfile << ind++ <<"if(!tupleAndAdded_" << i << ".second){\n";
                                outfile << ind <<"propFalse_" << i << " = true;\n";
                                outfile << ind <<"tuple_" << i << " = tupleAndAdded_" << i << ".first;\n";
                                outfile << --ind <<"}\n";
                                outfile << ind++ << "else{\n";
                                outfile << ind << "tuple_" << i << " = tupleAndAdded_" << i << ".first;\n";
                                outfile << ind << "int predicateId = tuple_" << i << "->getPredicateName();\n";
                                outfile << ind <<"int tupleReasonBeforePropFalse = tupleReasons.size()-1;\n";
                                outfile << ind << "std::pair<bool, Glucose::CRef> propFalseAndConf_" << i << " = LazyPropagator::getInstance().getPropagatorFromPredicateId(predicateId)->propagateToFalse(s, tuple_" << i << ", original, tupleReasons, reasonSet, false, true);\n";
                                outfile << ind << "LazyPropagator::getInstance().removeBodyLiteralsAddedByTuple(tuple_" << i << "->getId(), false);\n";
                                outfile << ind << "propFalse_" << i << "= propFalseAndConf_" << i << ".first;\n";
                                outfile << ind << "assert(propFalseAndConf_" << i << ".second == Glucose::CRef_Undef);\n";
                                outfile << ind++ << "if(!propFalse_" << i << "){\n"; 
                                outfile << ind << "toClearLazyFalseTuples.push_back(tuple_" << i << ");\n";
                                
                                outfile << --ind <<"}\n";

                                outfile << ind++ << "else{\n";
                                outfile << ind << "Glucose::vec<Glucose::Lit>& dummyFalseReason = tuple_" << i << "->getReasonLits();\n";
                                outfile << ind << "dummyFalseReason.clear();\n";
                                outfile << ind << "for(unsigned t = tupleReasonBeforePropFalse; t < tupleReasons.size(); ++t) dummyFalseReason.push(tupleReasons[t]);\n";
                                outfile << ind << "tuple_" << i << "->setStatus(TruthStatus::False);\n";
                                outfile << --ind <<"}\n";
                                outfile << ind++ << "if(LazyPropagator::getInstance().isPropagationDone()){\n";
                                outfile << ind <<"stopPropagateToFalse();\n";
                                outfile << ind << "return propFalseAndConf_" << i << ";\n";
                                outfile << --ind <<"}\n";
                                outfile << --ind <<"}\n";
                
                                outfile << --ind <<"}\n";
                            }
                            removeBodyLiteralsBlocksAndSymbols.emplace(std::make_pair(closingPars, i));
                            removeNegatedUndefBlocks.insert(std::make_pair(closingPars, i));
                        }
                        //
                        if(fixpointCompilation){
                            //if false then go ahead, otherwise no
                            //create tuple and do explainFalse
                            if(predDefinedInPosProgram){
                                outfile << ind << "Glucose::CRef conflProp;\n";
                                outfile << ind << "bool propFalse_" << i << " = false;\n";
                                outfile << ind++ << "if(tuple_" << i << " == NULL){\n";
                                outfile << ind << "std::pair<Tuple*, bool> tupleAndAdded_" << i << " = TupleFactory::getInstance().addNewLazyFalseTuple({";
                                for (unsigned k = 0; k < lit->getAriety(); k++)
                                {
                                    if (k > 0)
                                        outfile << ",";
                                    outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\"" + lit->getTermAt(k) + "\")");
                                }
                                outfile << "}, AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
                                outfile << ind <<"if(!tupleAndAdded_" << i << ".second) propFalse_" << i << " = true;\n";
                                outfile << ind++ << "else{\n";
                                outfile << ind << "tuple_" << i << " = tupleAndAdded_" << i << ".first;\n";
                                outfile << ind << "std::pair<bool, Glucose::CRef> propFalseAndConf_" << i << " = PositiveProgramFactory::getInstance().hasPossibleSupport(tuple_" << i << "->getId()) ? std::make_pair(false, Glucose::CRef_Undef) : LazyPropagator::getInstance().propagateToFalse(tuple_" << i << ", true);\n";
                                outfile << ind << "propFalse_" << i << " = propFalseAndConf_" << i << ".first;\n";
                                outfile << ind << "assert(propFalseAndConf_" << i << ".second == Glucose::CRef_Undef);\n";
                                //if propagationDone is set in propFalse redirection for negated tuple then it just means that the redirection propagated the dummy tuple
                                outfile << ind++ << "if(propFalse_" << i << "){\n";
                                outfile << ind << "tuple_" << i << "->setStatus(TruthStatus::False);\n";
                                outfile << ind << "LazyPropagator::getInstance().attachWatched(tuple_" << i << "->getId());\n";
                                //outfile << ind << "LazyPropagator::getInstance().requireRestartFixpoint();\n";
                                outfile << --ind <<"}\n";
                                outfile << ind <<"else TupleFactory::getInstance().deleteLastTuple(tuple_" << i << "->getId());\n";
                                outfile << --ind << "}\n";
                                outfile << --ind << "}\n";
                            }
                            removeNegatedUndefBlocks.insert(std::make_pair(closingPars, i));
                        }
                        std::string continueCondition;
                        if(predDefinedInPosProgram && fixpointCompilation) continueCondition = "(tuple_" + std::to_string(i) + "->isFalse() && TupleFactory::getInstance().isTupleFromInputInterface(tuple_" + std::to_string(i) + "->getId())) ||  propFalse_" + std::to_string(i);
                        else if(predDefinedInPosProgram && explainFalse) continueCondition = "propFalse_" + std::to_string(i) + " || !tuple_" + std::to_string(i) + "->isTrue()";
                        else if (!predDefinedInPosProgram && fixpointCompilation) continueCondition = "tuple_" + std::to_string(i) + "== NULL || tuple_" + std::to_string(i) + "->isFalse()";
                        else if(!predDefinedInPosProgram && explainFalse) continueCondition = "tuple_" + std::to_string(i) + "== NULL || !tuple_" + std::to_string(i) + "->isTrue()";
                        else
                            assert(false);
                        outfile << ind++ << "if(" << continueCondition << "){\n";
                    }else{
                        if(explainFalse){
                            if(predDefinedInPosProgram){
                                if(compileAddTupleToFactoryForExplainFalse(i, lit, componentPreds))
                                    redirectPropFalseTuples.push_back(i);
                            }
                        }
                        std::string continueOnlyWithTrueBody = !explainFalse ? " && tuple_" + std::to_string(i) + "->isTrue()" : "";
                        outfile << ind++ << "if(tuple_" << i <<" != NULL" << continueOnlyWithTrueBody << "){\n";
                        if(explainFalse){
                            outfile << ind <<"bool addedBodyLit_" << i << " = false;\n";
                            if(predDefinedInPosProgram){
                                outfile << ind ++ << "if(tuple_" << i <<" != NULL && tuple_" << i << "->isUnknown()){\n";
                                outfile << ind << "dummyTuplesInBody.insert(tuple_" << i <<"->getId());\n";
                                outfile << --ind <<"}\n";
                            }
                            outfile << ind++ << "if(tuple_" << i << "->isFalse() && !TupleFactory::getInstance().isLazyPropLevelZero(tuple_" << i << "->getId())){\n";
                            outfile << ind++ <<"if(!reasonSet.count(tuple_" << i << "->getId())){\n";
                            outfile << ind << "if(!TupleFactory::getInstance().isTupleFromGen(tuple_" << i << "->getId()) || s->levelFromPropagator(tuple_" << i << "->getId()) > 0) tupleReasons.push(Glucose::mkLit(tuple_" << i << "->getId(), false));\n";

                            outfile << ind << "reasonSet.insert(tuple_" << i << "->getId());\n";
                            outfile << ind << "if(s->levelFromPropagator(tuple_" << i << "->getId()) == s->currentLevel()) LazyPropagator::getInstance().switchIfNoCurrentLevelTupleFound(tupleReasons.size()-1, tupleReasons);\n";
                            outfile << --ind <<"}\n";
                            outfile << --ind <<"}\n";
                            //bound literal is true
                            outfile << ind++ <<"else{\n";
                            std::string addBodyLitCondition =  predDefinedInPosProgram ? "!TupleFactory::getInstance().isFact(tuple_" + std::to_string(i) + "->getId()) && !TupleFactory::getInstance().isTupleDummy(tuple_" + std::to_string(i) + "->getId()) ": "s->levelFromPropagator(tuple_" + std::to_string(i)+ "->getId()) > 0 || !s->isAssigned(tuple_" + std::to_string(i) + "->getId())";
                            outfile << ind++ << "if(" << addBodyLitCondition << ")\n";
                            outfile << ind << "addedBodyLit_" << i << " = LazyPropagator::getInstance().addBodyLiteral(tuple_" << i << "->getId(), !tupleNegated ? false : true);\n";
                            --ind;
                            closingPars++;
                            removeBodyLiteralsBlocksAndSymbols.emplace(std::make_pair(closingPars, i));
                            if(predDefinedInPosProgram)
                                removeDummyBlocksAndSymbols.emplace(std::make_pair(closingPars, i));                     
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
                    if(explainFalse) outfile << ind <<"bool addedBodyLit_" << i << " = false;\n";
                    for(unsigned k=0; k<lit->getAriety(); k++){
                        if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                            std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                            mapName+=std::to_string(k)+"_";
                            terms += (terms != "" ? ","+term : term);
                            boundIndices.insert(k);
                        }
                    }

                    outfile << ind << structType <<" tuples_"<<i<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";

                    if(explainFalse){
                        outfile << ind << structType << " tuplesU_"<<i<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";

                        outfile << ind << structType << " tuplesF_"<<i<<" = &"<<prefix<<"f"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                        outfile << ind++ << "for(auto i=tuplesF_"<<i<<"->begin(); i != tuplesF_"<<i<<"->end(); i++){\n";
                        outfile << ind++ <<"if(!reasonSet.count(*i)){\n";
                        outfile << ind << "if(!TupleFactory::getInstance().isTupleFromGen(*i) || s->levelFromPropagator(*i) > 0) tupleReasons.push(Glucose::mkLit(*i, false));\n";
                        outfile << ind << "reasonSet.insert(*i);\n";
                        outfile << ind << "if(s->levelFromPropagator(*i) == s->currentLevel()) LazyPropagator::getInstance().switchIfNoCurrentLevelTupleFound(tupleReasons.size()-1, tupleReasons);\n";
                        outfile << --ind <<"}\n";
                        outfile << --ind <<"}\n";
                        

                    }

                    if(!explainFalse)
                        outfile << ind++ << "for(auto i = tuples_"<<i<<"->begin(); i != tuples_"<<i<<"->end(); i++){\n";
                    else
                        outfile << ind++ << "for(auto i = tuplesU_"<<i<<"->begin(); i != tuples_"<<i<<"->end(); i++){\n";

                    closingPars++;
                    declaredTuples.push_back(i);
                    reasonTupleWithSign.push_back(std::make_pair(i, true));
                    if(!explainFalse)
                        outfile << ind << "Tuple* tuple_"<<i<<" = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                    else{
                        outfile << ind << "addedBodyLit_" << i << " = false;\n";
                        outfile << ind << "if(i == tuplesU_" << i << "->end()) i = tuples_" << i << "->begin();\n";
                        outfile << ind << "if(i == tuples_" << i << "->end()) break;\n";
                        outfile << ind << "Tuple* tuple_" << i << " = TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                        outfile << ind++ <<"if(s->levelFromPropagator(tuple_" << i << "->getId()) > 0 || !s->isAssigned(tuple_" << i << "->getId()))\n";
                        outfile << ind << "addedBodyLit_" << i << " = LazyPropagator::getInstance().addBodyLiteral(tuple_" << i << "->getId(), !tupleNegated ? false : true);\n";
                        --ind;
                        removeBodyLiteralsBlocksAndSymbols.emplace(std::make_pair(closingPars, i));
                    }
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
        if(i == numberOfFormulas -1){
            outfile << ind << "//Rule is firing;\n";
            //last tuple must be false when I am not doing propagation.s
            //I am not doing propagation in propagateToFalse redirections
            if(explainFalse){
                //recursive component explain false
                if(isRecursive){
                    if(formula->isLiteral()){
                        const aspc::Literal* lit = (const aspc::Literal*)formula;
                        bool predDefinedInPosProgram = positiveProgramHeadPredicates.count(lit->getPredicateName());
                        if(predDefinedInPosProgram){
                            outfile << ind++ <<"if(TupleFactory::getInstance().isTupleDummy(tuple_" << i << "->getId())){\n";
                            outfile << ind << "toExplain.push_back(tuple_" << i << ");\n";
                            outfile << ind << "toExplainUndefs.push_back(TupleSignSet());\n";
                            outfile << ind << "tupleToParent.emplace(std::make_pair(tuple_" << i << "->getId(), tuple_0->getId()));\n";
                            outfile << ind << "if(!tupleToChildren.count(tuple_0->getId())) tupleToChildren.emplace(std::make_pair(tuple_0->getId(), std::unordered_set<int>()));\n";
                            outfile << ind << "tupleToChildren.at(tuple_0->getId()).insert(tuple_" << i << "->getId());\n";
                            outfile << --ind <<"}\n";
                        }
                    }
                }
                std::pair<int, bool> lastTuple = reasonTupleWithSign.at(reasonTupleWithSign.size() -1);

                //redirect propagateToFalse towards components on which current tuple depends
                if(redirectPropFalseTuples.size() > 0)
                    outfile << ind << "int predicateId;\n";

                for(int toRedirectTupleIndex : redirectPropFalseTuples){
                    outfile << ind++ << "if(!tuple_" << toRedirectTupleIndex << "->isTrue()){\n";
                    outfile << ind << "predicateId = tuple_" << toRedirectTupleIndex << "->getPredicateName();\n";
                    outfile << ind << "canPropagate = LazyPropagator::getInstance().getPropagatorFromPredicateId(predicateId)->propagateToFalse(s, tuple_" << toRedirectTupleIndex << ", original, tupleReasons, reasonSet, false, false).first;\n";
                    outfile << ind << "if(!canPropagate) return std::make_pair(false, Glucose::CRef_Undef);\n";
                    outfile << --ind <<"}\n";
                }
                //save undefs added by redirections into lazy prop
                if(isRecursive && !compileAsExit){
                    outfile << ind << "if(dummyTuplesInBody.size() != 0) LazyPropagator::getInstance().storeBodyLiteralsFromTuple(tuple_0->getId(), toExplainUndefs.back());\n";
                }
                outfile << ind++ << "if(LazyPropagator::getInstance().getUndefsBodySize() != 0 && dummyTuplesInBody.size() == 0){\n";
                outfile << ind++ <<"if(TupleFactory::getInstance().isTupleFromInputInterface(original->getId()) && ! LazyPropagator::getInstance().isPredicateAlwaysToCheck(original->getPredicateName()))\n";
                outfile << ind <<"LazyPropagator::getInstance().addPossibleSupportsForTuple(original->getId());\n";
                --ind;
                outfile << ind++ <<"else\n"; //&& !LazyPropagator::getInstance().isPredicateAlwaysToCheck(original->getPredicateName())
                //cannot propagate lazyFalse to False but a possible support is found the original tuple that made this call 
                outfile << ind << "return std::make_pair(false, Glucose::CRef_Undef);\n";
                --ind;
                outfile << ind << "tupleReasons.clear();\n";
                outfile << ind << "LazyPropagator::getInstance().setPropagationDone(true);\n";
                outfile << ind << "return std::make_pair(false, Glucose::CRef_Undef);\n";
                outfile << --ind <<"}\n";
                
            }
        }
    }
    std::vector<aspc::Atom> head = rule.getHead();
    for(int index = 0; index < head.size(); index++){
        aspc::Atom* atom = &head[index];
        if(fixpointCompilation){
            outfile << ind << "Tuple* head_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";

            for(unsigned k=0; k<atom->getAriety(); k++){
                if(k>0) outfile << ",";
                outfile << (atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+atom->getTermAt(k)+"\")");
            }
            outfile << "}, AuxMapHandler::getInstance().get_"<<atom->getPredicateName()<<"(),false);\n";
        }
        //make propagation only if head is not a false tuple created in a propagateFalse chain
        if(explainFalse){
            outfile << ind << "Tuple* head_" << index << " = NULL;\n";
            outfile << ind << "head_" << index << " = TupleFactory::getInstance().find({";
            for (unsigned k = 0; k < atom->getAriety(); k++)
            {
                if (k > 0)
                    outfile << ",";
                outfile << (atom->isVariableTermAt(k) || isInteger(atom->getTermAt(k)) ? atom->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\"" + atom->getTermAt(k) + "\")");
            }
            outfile << "}, AuxMapHandler::getInstance().get_" << atom->getPredicateName() << "());\n";
            outfile << ind++ << "if(head_" << index << "== original && LazyPropagator::getInstance().getUndefsBodySize() == 0 && dummyTuplesInBody.size() == 0 && toClearLazyFalseTuples.size() == 0){\n";
            outfile << ind << "LazyPropagator::getInstance().setTruePropInPropFalse(true);\n";
        }
        outfile << ind << "bool tupleIsFromInputInterface = TupleFactory::getInstance().isTupleFromInputInterface(head_" << index << "->getId());\n";
        outfile << ind << "std::pair<const Tuple *, bool> insertResult;\n";
        outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId())){\n";
        if(fixpointCompilation){
            outfile << ind++ <<"if(head_" << index << "->isTrue() && !TupleFactory::getInstance().isPropagationFromLazyProp(head_" << index << "->getId())){\n";
            outfile << ind << "TupleFactory::getInstance().addCheckedTuple(head_" << index << "->getId());\n";
            outfile << ind << "PositiveProgramFactory::getInstance().removeToCheckTuple(head_" << index << "->getId());\n";
            outfile << ind << "PositiveProgramFactory::getInstance().removePossibleSupports(head_" << index << "->getId(), false);\n";
            outfile << --ind << "}\n";
            outfile << ind++ << "if(!LazyPropagator::getInstance().alreadyEnqueued(head_" << index << "->getId())){\n";
        }
        std::string isTupleTrue =  fixpointCompilation ? "&& !head_" + std::to_string(index) + "->isTrue()" : "";
        outfile << ind++ << "if(!s->currentLevel() == 0 " << isTupleTrue << "){\n";
        compileReasonAndSupportSaving(reasonTupleWithSign, index, "head_", fixpointCompilation);
        outfile << --ind << "}\n";
        if(fixpointCompilation){
            compileTrueInterfacePropagation(index, "head_", !compileAsExit && std::find(componentPreds.begin(), componentPreds.end(), atom->getPredicateName()) != componentPreds.end(), true, fixpointCompilation && starter == rule.getFormulas().size());
            compileTrueNonInterfacePropagation(index, "head_", !compileAsExit && std::find(componentPreds.begin(), componentPreds.end(), atom->getPredicateName()) != componentPreds.end(), true);
        }
        if(explainFalse){
            compileTrueInterfacePropagation(index, "head_", false, false, false);
            compileTrueNonInterfacePropagation(index, "head_", false, false);
        }
        
        outfile << --ind << "}\n";
        outfile << --ind << "}\n";
    }

    for (int i = closingPars; i > 0; --i) {
        if(explainFalse){
            if(removeBodyLiteralsBlocksAndSymbols.count(i)){
                if(!removeNegatedUndefBlocks.count(i))
                    outfile << ind << "if(addedBodyLit_" << removeBodyLiteralsBlocksAndSymbols[i] << ") LazyPropagator::getInstance().removeLastBodyLiteral(tuple_" << removeBodyLiteralsBlocksAndSymbols[i] << "->getId());\n";
                else{
                    outfile << ind <<"if(addedBodyLit_" << removeBodyLiteralsBlocksAndSymbols[i] << ") LazyPropagator::getInstance().removeLastBodyLiteral(tuple_" << removeBodyLiteralsBlocksAndSymbols[i] << "->getId());\n";
                    if(std::find(redirectPropFalseTuples.begin(), redirectPropFalseTuples.end(), removeBodyLiteralsBlocksAndSymbols[i])  != redirectPropFalseTuples.end()){
                        outfile << ind << "else if(!propFalse_" << removeBodyLiteralsBlocksAndSymbols[i] << ") LazyPropagator::getInstance().removeBodyLiteralsAddedByTuple(tuple_" << removeBodyLiteralsBlocksAndSymbols[i] << "->getId(), false);\n";
                    }
                    if(tupleFromPPIdx.count(removeBodyLiteralsBlocksAndSymbols[i])){
                        outfile << ind++ <<"if(!propFalse_" << removeBodyLiteralsBlocksAndSymbols[i] << " && !tuple_" << removeBodyLiteralsBlocksAndSymbols[i] << "->isTrue()){\n";
                        outfile << ind << "TupleFactory::getInstance().deleteLastTuple(tuple_" << removeBodyLiteralsBlocksAndSymbols[i] << "->getId());\n";
                        outfile << ind <<"toClearLazyFalseTuples.pop_back();\n";
                        outfile << --ind << "}\n";
                    }
                }
            }
        }
        if(removeDummyBlocksAndSymbols.count(i)){
            outfile << ind <<"dummyTuplesInBody.erase(tuple_" << removeDummyBlocksAndSymbols[i] << "->getId());\n";
        }
        outfile << --ind << "}//close par\n";
    }

    //just before closing rule scope
    outfile << ind++ << "for(unsigned i = 0; i < insertResults.size(); ++i){\n";
    outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResults[i]);\n";
    outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(insertResults[i].first->getId());\n";

    outfile << --ind <<"}\n";
    outfile << ind++ << "for(unsigned i = 0; i < propagations.size(); ++i){\n";
    outfile << ind << "bool isAssigned = s->isAssigned(propagations[i]);\n";
    outfile << ind << "bool isConflict = s->isConflictPropagation(propagations[i], false);\n";
    outfile << ind++ << "if(!isAssigned){\n";
    outfile << ind << "s->assignFromPropagators(Glucose::mkLit(propagations[i]));\n";
    outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(propagations[i]);\n";
    
    outfile << --ind << "}\n";
    outfile << ind++ << "else if(isConflict){\n";
    outfile << ind << "lits.clear();\n";
    outfile << ind << "s->addClause_(lits);\n";
    outfile << ind << "return std::make_pair(true, Glucose::CRef_PropConf);\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
    //propagated to true inside propFalse at level 0 -> cannot propagate passed tuple to false
    if(!fixpointCompilation)
        outfile << ind << "if(propagations.size() > 0) return std::make_pair(false, Glucose::CRef_Undef);\n";
    outfile << --ind << "}\n";
}

// if tuple is NULL, but it comes from a literal defined inside P.P.
// it should be generated since the predicate set of P.P. predicates might
// be partial
bool LazyPropagatorCompiler::compileAddTupleToFactoryForExplainFalse(unsigned i, const aspc::Literal* lit, const std::set<std::string>& componentPreds){
        bool toRedirect = true;
        outfile << ind++ << "if(tuple_" << i << " == NULL){\n";
        outfile << ind << "tuple_" << i << " = TupleFactory::getInstance().addNewDummyPropFalseTuple({";
        for(unsigned k=0; k<lit->getAriety(); k++){
            if(k>0) outfile << ",";
            outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
        }
        outfile << "}, AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
        if(componentPreds.count(lit->getPredicateName())){
            toRedirect = false;
        }
        outfile << --ind << "}\n";
        return toRedirect;
}
void LazyPropagatorCompiler::compileReasonAndSupportSaving(std::vector<std::pair<int, bool>>& declaredTuples, int index, std::string tuplePrefix, bool fixpoint){
    //when doing propagateToFalse and a new SP is found for an already-true tuple the method can stop
    if(!fixpoint){
        outfile << ind++ <<"if("<< tuplePrefix << index << "->isTrue()){\n";
        #ifdef COMPILE_DEBUG_PRINT
            outfile << ind <<"std::cout << \"Tuple \" << " << tuplePrefix << index << "->getId() << \" found a SP from lazy rules\\n\";\n";
        #endif
        outfile << ind << "TupleFactory::getInstance().addCheckedTuple(" << tuplePrefix << index << "->getId());\n";
        outfile << ind << "PositiveProgramFactory::getInstance().removeToCheckTuple(" << tuplePrefix << index << "->getId());\n";       
        outfile << ind << "PositiveProgramFactory::getInstance().removePossibleSupports(" << tuplePrefix << index << "->getId(), false);\n";
        outfile << ind << "return std::make_pair(false, Glucose::CRef_Undef);\n";
        outfile << --ind << "}\n";
    }

    outfile << ind <<"int indexCurrentLevelTuple = -1;\n";
    outfile << ind <<"bool isSATVar = head_" << index << "->getId() < s->nVars();\n";
    outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason =  !isSATVar || !s->isAssigned(head_"<< index << "->getId()) ? head_" << index << "->getReasonLits() : s->getReasonClause();\n";
    if(fixpoint)
        outfile << ind << "if(TupleFactory::getInstance().isPropagationFromLazyProp(head_" << index << "->getId())) PositiveProgramFactory::getInstance().clearTupleSupport(head_" << index << "->getId());\n";
    outfile << ind << "propagationReason.clear();\n";
    //add propagating literal
    outfile << ind << "propagationReason.push(Glucose::mkLit(head_" << index << "->getId(), false));\n";


    for(unsigned i = 0; i < declaredTuples.size(); ++i){
        if(declaredTuples.at(i).second){
            outfile << ind++ << "if(!TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId()) || s->levelFromPropagator(tuple_" << declaredTuples.at(i).first <<"->getId()) > 0){\n";
            outfile << ind++ <<"if(TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId()) && s->levelFromPropagator(tuple_" << declaredTuples.at(i).first << "->getId()) == s->currentLevel()){\n";
            outfile << ind << "indexCurrentLevelTuple = propagationReason.size();\n";
            outfile << --ind << "}\n";
            outfile << ind++ << "if(!TupleFactory::getInstance().isLazyPropLevelZero(tuple_" << declaredTuples.at(i).first <<"->getId())){\n";
            outfile << ind << "propagationReason.push(Glucose::mkLit(tuple_" << declaredTuples.at(i).first <<"->getId(), true));\n";
            outfile << ind << "PositiveProgramFactory::getInstance().addSupported(tuple_" << declaredTuples.at(i).first << "->getId(), "<< tuplePrefix << index << "->getId());\n";
            outfile << --ind <<"}\n";
            outfile << --ind <<"}\n";
        }
        else{
            //negated -> in propagateToFalse I have propFalse_t
            outfile << ind++ << "if(tuple_" << declaredTuples.at(i).first << "!= NULL){\n";
            outfile << ind++ << "if(!TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId()) || s->levelFromPropagator(tuple_" << declaredTuples.at(i).first <<"->getId()) > 0){\n";
            outfile << ind++ << "if(TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId())){\n";
            outfile << ind++ <<"if(s->levelFromPropagator(tuple_" << declaredTuples.at(i).first << "->getId()) == s->currentLevel()){\n";
            outfile << ind << "indexCurrentLevelTuple = propagationReason.size();\n";
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";
            outfile << ind++ << "if(!TupleFactory::getInstance().isLazyPropLevelZero(tuple_" << declaredTuples.at(i).first <<"->getId())){\n";
            outfile << ind << "propagationReason.push(Glucose::mkLit(tuple_" << declaredTuples.at(i).first <<"->getId(), false));\n";
            outfile << ind << "PositiveProgramFactory::getInstance().addSupported(tuple_" << declaredTuples.at(i).first << "->getId(), "<< tuplePrefix << index << "->getId());\n";
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";
        }
    }
    //DEBUG PRINT
    #ifdef COMPILE_DEBUG_PRINT
        outfile << ind <<"std::cout <<\"Clause for true prop: \\n\";\n";
        outfile << ind++ <<"for(int i = 0; i < propagationReason.size(); ++i){\n";
        outfile << ind << "std::cout << \"[\";\n";
        outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));\n";
        outfile << ind << "std::cout <<\", \"<<Glucose::sign(propagationReason[i]) << \"] \";\n";
        outfile << --ind << "}\n";
        outfile << ind << "std::cout <<std::endl;\n";
    #endif
    outfile << ind << "assert(propagationReason.size() >= 2 || s->currentLevel() == 0);\n";
    outfile << ind++ << "if(isSATVar && indexCurrentLevelTuple != -1){\n";
    //switch currentLevelLiteral with literal in second position
    outfile << ind << "Glucose::Lit temp = propagationReason[1];\n";
    outfile << ind << "propagationReason[1] = propagationReason[indexCurrentLevelTuple];\n";
    outfile << ind << "propagationReason[indexCurrentLevelTuple] = temp;\n";
    outfile << ind << "assert(s->levelFromPropagator(var(propagationReason[1])) == s->currentLevel());\n";
    outfile << --ind <<"}\n";
}

void LazyPropagatorCompiler:: compileTrueInterfacePropagation(int index, std::string tuplePrefix, bool pushIntoStack, bool fixpoint, bool levelZero){
    outfile << ind++ << "if(tupleIsFromInputInterface){\n";
    outfile << ind << "bool foundConflict = s->isConflictPropagation(" << tuplePrefix << index <<"->getId(), false);\n";
    outfile << ind << "bool assigned = s->isAssigned(" << tuplePrefix << index << "->getId());\n";
    if(levelZero){
        outfile << ind++ << "if(assigned){\n";
        outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(" << tuplePrefix << index << "->getId());\n";
        outfile << ind << "TupleFactory::getInstance().addCheckedTuple(" << tuplePrefix << index << "->getId());\n";
        outfile << ind << "PositiveProgramFactory::getInstance().removeToCheckTuple(" << tuplePrefix << index <<"->getId());\n";
        outfile << --ind << "}\n";
    }
    outfile << ind++ << "if(!assigned || foundConflict){\n";
    outfile << ind++ << "if(s->currentLevel() > 0){\n";
    outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(" << tuplePrefix << index << "->getId());\n";
    //explode reasonClause in such a way that when explain is called in solver reason is ready to be taken from glucose
    outfile << ind << "if(foundConflict) LazyPropagator::getInstance().explodeReasonLits(" << tuplePrefix << index << "->getId(), s->getReasonClause());\n";
    outfile << ind << "Glucose::CRef clause = s->externalPropagation(" << tuplePrefix << index << "->getId(), false);\n";
    outfile << ind << "LazyPropagator::getInstance().addEnqueued(" << tuplePrefix << index << "->getId());\n";
    if(!fixpoint)
        outfile << ind <<"LazyPropagator::getInstance().setPropagationDone(true);\n";
    if(fixpoint)
        outfile << ind << "generated = true;\n";
    outfile << ind++ << "if(clause != Glucose::CRef_Undef){\n";
    //no unroll and no propagate for conflictual lit
    outfile << ind << "PositiveProgramFactory::getInstance().updateToCheckDueToTuple(" << tuplePrefix << index << "->getId());\n";
    outfile << ind << "TupleFactory::getInstance().removePropagationFromLazyProp(" << tuplePrefix << index << "->getId());\n";
    if(fixpoint)
        outfile << ind << "return std::make_pair(generated, clause);\n";
        
    outfile << --ind <<"}\n";
    if(!fixpoint){
        outfile << ind << "TupleFactory::getInstance().addCheckedTuple(original->getId());\n";
        outfile << ind << "return std::make_pair(true, clause);\n";
    }
    outfile << --ind << "}\n";
    outfile << ind++ <<"else{\n";
    if(fixpoint){
        outfile << ind << "propagations.push_back(" << tuplePrefix << index<< "->getId());\n";
        outfile << ind << "TupleFactory::getInstance().addLazyPropLevelZero(" << tuplePrefix << index<< "->getId());\n";
        outfile << ind << "TupleFactory::getInstance().addCheckedTuple(" << tuplePrefix << index << "->getId());\n";
        outfile << ind << "PositiveProgramFactory::getInstance().removeToCheckTuple(" << tuplePrefix << index << "->getId());\n";
    }
    else
        outfile << ind << "if(makePropagation) propagations.push_back(" << tuplePrefix << index<< "->getId());\n";
    
    if(fixpoint)
        outfile << ind << "generated = true;\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler:: compileTrueNonInterfacePropagation(int index, std::string tuplePrefix, bool pushIntoStack, bool fixpoint){
    outfile << ind++ << "else{\n";
    outfile << ind++ << "if(" << tuplePrefix << index << "->isUnknown()){\n";
    outfile << ind << "if(s->currentLevel() == 0) TupleFactory::getInstance().addLazyPropLevelZero(" << tuplePrefix << index<< "->getId());\n";
    outfile << ind << "LazyPropagator::getInstance().addEnqueued(" << tuplePrefix << index << "->getId());\n";
    if(!fixpoint)
        outfile << ind <<"LazyPropagator::getInstance().setPropagationDone(true);\n";
    if(fixpoint)
        outfile << ind << "generated = true;\n";
    outfile << ind << "AuxMapHandler::getInstance().initTuple(" << tuplePrefix << index << ");\n";
    if(pushIntoStack){
        outfile << ind << "stack.push_back(" << tuplePrefix << index << "->getId());\n";
    }
    outfile << ind << "insertResult = " << tuplePrefix << index <<"->setStatus(TruthStatus::True);\n";

    outfile << ind << "insertResults.push_back(insertResult);\n";
    outfile << ind << "LazyPropagator::getInstance().attachWatched(" << tuplePrefix << index << "->getId());\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::openPropagatorFile(unsigned compID, std::set<std::string>& componentPredicateNames){

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
    outfile << ind << "#include \"../solver/AbstractLazyPropagator.h\"\n";
    outfile << ind << "#include \"../solver/PositiveProgramFactory.h\"\n";
    outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
    outfile << ind << "#include \"../datastructures/VectorAsSet.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

    outfile << ind << "//This component defines predicates: ";
    for(std::string pred : componentPredicateNames){
        outfile << pred << " ";
    }
    outfile << ind <<"\n";
    outfile << ind++ << "class " << className << ": public AbstractLazyPropagator{\n";
    outfile << ind << "std::vector<int> tuplesEmpty;\n";
    outfile << ind << "IndexedSet tuplesSetEmpty;\n";
    outfile << ind++ << "public:\n";
}

void LazyPropagatorCompiler::closePropagatorFile(){
    --ind;
    outfile << --ind << "};\n";
    outfile << ind << "#endif\n";
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

void LazyPropagatorCompiler::compileComponentWatched(std::vector<int>& scc, std::vector<unsigned>& rules){
    outfile << ind++ <<propagatorNames.back() << "(){\n";
    std::unordered_set<std::string> watchedPredicates;
    std::unordered_set<std::string> headPredicates;
    for(unsigned i = 0; i < rules.size(); ++i){
        const aspc::Rule& rule = program.getRule(rules[i]);
        for(const aspc::Formula* formula : rule.getFormulas()){
            if(formula->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)formula;
                if(!watchedPredicates.count(lit->getPredicateName())){
                    outfile << ind << "watchedPredicates.push_back(AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "());\n";
                    watchedPredicates.insert(lit->getPredicateName());
                }
            }
        }
        for(const aspc::Atom head: rule.getHead()){
            if(!headPredicates.count(head.getPredicateName())){
                outfile << ind << "headPredicates.push_back(AuxMapHandler::getInstance().get_" << head.getPredicateName() << "());\n";
                headPredicates.insert(head.getPredicateName());
            }
        }

    }
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileStopPropagateToFalse(){
    outfile << ind++ << "void stopPropagateToFalse(){\n";
    outfile << ind++ << "for(int i = toClearLazyFalseTuples.size()-1; i >= 0; --i){\n";
    outfile << ind << "TupleFactory::getInstance().deleteLastTuple(toClearLazyFalseTuples[i]->getId());\n";
    outfile << --ind << "}\n";
    outfile << ind << "toClearLazyFalseTuples.clear();\n";
    outfile << --ind << "}\n";
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
    outfile << ind << "Glucose::Solver* LazyPropagator::s = nullptr;\n";
    outfile << ind++ << "LazyPropagator::LazyPropagator(){\n";
    for(int i = 0; i < propagatorNames.size(); ++i){
        std::string className = propagatorNames[i];
        outfile << ind << "propagators.push_back(new " << className << "());\n";
        outfile << ind << "propagators.back()->setId(" << i << ");\n";
    }
    //copies are not a problem. This is executed once and watched predicates are supposed to be a few
    outfile << ind << "predicateToPropagator = std::unordered_map<int, int>();\n";
    outfile << ind << "for(unsigned i = 0; i < AuxMapHandler::getInstance().predicateCount(); ++i) watchedPredicateToPropagators.emplace(std::make_pair(i, std::vector<int>()));\n";

    outfile << ind++ << "for(int i = 0; i < propagators.size(); ++i){\n";
    outfile << ind << "tuplesByPropagator.push_back(std::vector<int>());\n";
    outfile << ind << "std::vector<int> watchedPredicates = propagators[i]->getWatchedPredicates();\n";
    outfile << ind << "for(unsigned t = 0; t < watchedPredicates.size(); ++t) watchedPredicateToPropagators[watchedPredicates[t]].push_back(propagators[i]->getId());\n";
    outfile << ind << "std::vector<int> predicatesDefinedByProp = propagators[i]->getHeadPredicates();\n";
    outfile << ind++ <<"for(int j = 0; j < predicatesDefinedByProp.size(); ++j){\n";
    outfile << ind << "predicateToPropagator.emplace(std::make_pair(predicatesDefinedByProp[j], propagators[i]->getId()));\n";
    outfile << ind << "predicatedDefinedByPositiveProgram.insert(predicatesDefinedByProp[j]);\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
    for(std::string predName : alwaysToCheckPredicates){
        outfile << ind << "alwaysToCheckPredicates.insert(AuxMapHandler::getInstance().get_" << predName << "());\n";
    }
    outfile << --ind << "}\n";



    outfile <<ind++ << "void LazyPropagator::findAlwaysToCheckTuples(){\n";
    unsigned tuplesVectorIndex = 0;
    for(std::string predName : alwaysToCheckPredicates){
        outfile << ind << "std::vector<int>* tuples_" << tuplesVectorIndex<< " = &AuxMapHandler::getInstance().get_u" << predName << "_()->getValuesVec({});\n";
        outfile << ind++ << "for(auto i = tuples_" << tuplesVectorIndex<< "->begin(); i != tuples_" << tuplesVectorIndex << "->end(); ++i){\n";
        outfile << ind << "alwaysToCheckTuples.insert(*i);\n";
        outfile << ind << "currentlyToCheckTuples.insert(*i);\n";
        outfile << --ind << "}\n";
        tuplesVectorIndex++;
    }
    outfile << --ind << "}\n";

    outfile <<ind++ << "void LazyPropagator::getAlwaysToCheckTuples(std::unordered_set<int>& toCheck){\n";
    outfile << ind <<"for(int id : currentlyToCheckTuples) toCheck.insert(id);\n";
    outfile << --ind << "}\n";
}