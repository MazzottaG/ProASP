#include "LazyPropagatorCompiler.h"

LazyPropagatorCompiler::LazyPropagatorCompiler(const aspc::Program& program, std::string& execPath, DataStructureCompiler* dc, const std::unordered_map<std::string, std::string>& predToStruct): program(program), execPath(execPath), auxMapCompiler(dc), predicateToStruct(predToStruct), ind(Indentation(0)){
    depManager.buildDependecyGraph(program);
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

    compileFixPointComputationLevelZero(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    compileFixPointComputation(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    compileExplainFalse(scc,rulesForComponent, componentPredicateNames, nonExitRules);
    //compileExplainTrue(scc, rulesForComponent, componentPredicateNames, nonExitRules);
    //compileCheckLiteralStatus(scc, rulesForComponent, componentPredicateNames, nonExitRules);
    //compileComponentWatched(scc, index);
    compileComponentWatched(scc, rulesForComponent);
    closePropagatorFile();
}

void LazyPropagatorCompiler::compileFixPointComputationLevelZero(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "bool computeFixpointLevelZero(Glucose::Solver* s, Glucose::vec<Glucose::Lit>& lits){\n";
    outfile << ind++ << "{\n";
    //std::cout <<"Orderings: \n";
    bool isRecursive = nonExitRules.size() > 0;
    outfile << ind << "std::vector<int> stack;\n";
    outfile << ind << "bool generated = false;\n";
    outfile << ind << "Glucose::CRef confl;\n";

    //exit rule compilation
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        //TODO exit rule compilation should not push inside the stack
        if(std::find(nonExitRules.begin(), nonExitRules.end(), ruleID) == nonExitRules.end())
            compileRuleByStarter(ruleID, rule, rule.getFormulas().size(), componentPredicateNames, isRecursive, true, false, false, false);

    }
    //nonExitRules by default starter
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        if(std::find(nonExitRules.begin(), nonExitRules.end(), ruleID) != nonExitRules.end())
            compileRuleByStarter(ruleID, rule, rule.getFormulas().size(), componentPredicateNames, isRecursive, true, false, false, false);

    }
    outfile << ind++ << "while(!stack.empty()){\n";
    outfile << ind << "Tuple* tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
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
                    compileRuleByStarter(ruleID, rule, formulaID, componentPredicateNames, isRecursive, true, false, false, false);
                    outfile << --ind <<"}\n";
                }
            }
            formulaID++;
        }
    }
    //compilation inside stack scope
    outfile << --ind << "}\n";

    //scc scope
    outfile << ind << "return generated;\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileFixPointComputation(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "bool computeFixpoint(Glucose::Solver* s, std::vector<int>& propagatedTuples, Glucose::CRef& confl, Glucose::vec<Glucose::Lit>& lits){\n";
    // outfile << ind <<"std::cout << \"to propagate tuples: \\n\";\n";
    // outfile << ind++<<"for(unsigned i = 0; i < propagatedTuples.size(); ++i){";
    // outfile << ind << "std::cout << propagatedTuples[i] <<\" \";\n";
    // outfile << --ind <<"}\n";

    outfile << ind++ << "{\n";
    //std::cout <<"Orderings: \n";
    bool isRecursive = nonExitRules.size() > 0;

    outfile << ind << "std::vector<int> stack = std::vector<int>(propagatedTuples.begin(), propagatedTuples.end());\n";
    //make a pre-fill of the stack
    if(isRecursive){
       for(std::string predName : componentPredicateNames){
            std::string prefix = "AuxMapHandler::getInstance().get_";
            std::string mapName = predName+"_";
            std::string predStruct = predicateToStruct[predName];
            std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";
            outfile << ind << structType <<" tuples_"<<predName<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({});\n";
            outfile << ind << "for(auto i=tuples_"<<predName<<"->begin(); i != tuples_"<<predName<<"->end(); i++) stack.push_back(*i);\n";
       }
    }
    outfile << ind << "bool generated = false;\n";

    outfile << ind++ << "while(!stack.empty()){\n";
    outfile << ind << "Tuple* tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
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
                compileRuleByStarter(ruleID, rule, formulaID, componentPredicateNames, isRecursive, true, false, false, false);
                outfile << --ind <<"}\n";
            }
            formulaID++;
        }
    }
    //compilation inside stack scope
    outfile << --ind << "}\n";

    //scc scope
    outfile << ind << "return generated;\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileCheckLiteralStatus(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "void checkLiteralStatus(Glucose::Solver* s, std::vector<std::pair<int, bool>> literals){\n";
    outfile << ind++ <<"while(!literals.empty()){\n";
    outfile << ind << "std::pair<int, bool> lit = literals.back();\n";
    outfile << ind << "literals.pop_back();\n";
    outfile << ind << "Tuple* tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(lit.first);\n";
    outfile << ind << "bool generated = false;\n";
    //check source pointer if present
    outfile << ind << "bool spFailed = false;\n";
    outfile << ind++ << "if(lit.second && tuple_0->getReason().size() > 0){\n";
    outfile << ind << "const Glucose::vec<Glucose::Lit>& reason = tuple_0->getReason();\n";
    outfile << ind++ << "for(unsigned i = 0; i < reason.size(); ++i){\n";
    outfile << ind << "int id = var(reason[i]);\n";
    outfile << ind << "if(!Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isTrue()) spFailed = true;\n";
    outfile << ind << "else if(Glucose::sign(reason[i]) && !TupleFactory::getInstance().getTupleFromInternalID(id)->isFalse()) spFailed = true;\n";
    //outfile << ind << "if(Glucose::toInt(reason[i]) > 0 && !TupleFactory::getInstance().getTupleFromInternalID(Glucose::toInt(reason[i]))->isTrue()) spFailed = True;\n";
    //outfile << ind << "else if(Glucose::toInt(reason[i]) < 0 && !TupleFactory::getInstance().getTupleFromInternalID(Glucose::toInt(reason[i]) * -1)->isFalse()) spFailed = True;\n";
    outfile << ind << "if(spFailed) break;\n";
    outfile << --ind << "}\n";
    outfile << ind << "if(!spFailed) continue;\n";
    outfile << --ind << "}\n";
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << rule.getHead().at(0).getPredicateName() <<"() && !generated){\n";
        //compile rule with head as starter. Only check for firing of the rule is needed, no generation, nor reasons
        compileRuleByStarter(ruleID, rule, -1, componentPredicateNames, nonExitRules.size() > 0, false, true, false, false);
        outfile << --ind <<"}\n";
    }
    outfile << ind++ << "if(generated && !lit.second){\n";
    outfile << ind << "//call explain true\n";
    //outfile << ind << "std::cout <<\"Tuple  \";\n";
    outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(lit.first));\n";
    //outfile << ind << "std::cout << \" was supposed to be false, but it was generated\\n\";\n";
    outfile << --ind <<"}\n";
    outfile << ind++ << "if(!generated && lit.second){\n";
    //outfile << ind << "std::cout <<\"Tuple  \";\n";
    outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(lit.first));\n";
    //outfile << ind << "std::cout<< \" was supposed to be true, but it was not generated\\n\";\n";
    outfile << ind << "//call explain false\n";
    outfile << --ind <<"}\n";

    outfile << --ind <<"}\n";
    outfile << --ind << "}\n";
}

//TODO refactor to use Compiled ExplainTrue
void LazyPropagatorCompiler::compileExplainTrue(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){

    outfile << ind++ << "void explainTrueLiteral(int id){\n";
    outfile << ind << "std::vector<int> toExplain;\n";
    outfile << ind << "std::unordered_set<int> tupleReasons;\n";
    outfile << ind << "toExplain.push_back(id);\n";
    outfile << ind++ << "while(!toExplain.empty()){\n";
    outfile << ind << "Tuple* tuple_0 = TupleFactory::getInstance().getTupleFromInternalID(toExplain.back());\n";
    outfile << ind << "toExplain.pop_back();\n";
    outfile << ind << "bool generated = false;\n";
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << rule.getHead().at(0).getPredicateName() <<"() && !generated){\n";
        compileRuleByStarter(ruleID, rule, -1, componentPredicateNames, nonExitRules.size() > 0, false, true, true, false);
        outfile << --ind <<"}\n";
    }
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
}

void LazyPropagatorCompiler::compileExplainFalse(std::vector<int>& scc, std::vector<unsigned>& rules, std::set<std::string>& componentPredicateNames, std::vector<unsigned>& nonExitRules){
    outfile << ind++ << "bool propagateToFalse(Glucose::Solver* s, Tuple* tuple, Tuple* original, bool sign, Glucose::vec<Glucose::Lit>& tupleReasons, Glucose::vec<Glucose::Lit>& lits, Glucose::CRef& confl, bool makePropagation){\n";
    outfile << ind << "std::vector<Tuple*> toExplain;\n";
    outfile << ind << "std::vector<int> toExplainSign;\n";
    outfile << ind << "toExplain.push_back(tuple);\n";
    outfile << ind << "toExplainSign.push_back(sign);\n";
    //add propagating tuple to reason
    outfile << ind++ << "if(makePropagation)\n";
    outfile << ind << "tupleReasons.push(Glucose::mkLit(tuple->getId(), true));\n";
    --ind;
    outfile << ind << "bool tupleIsDummy = false;\n";
    outfile << ind++ << "while(!toExplain.empty()){\n";
    outfile << ind << "bool tupleIsFromComp = false;\n";
    outfile << ind << "Tuple* tuple_0 = toExplain.back();\n";
    outfile << ind << "bool tupleSign = toExplainSign.back();\n";
    outfile << ind << "toExplain.pop_back();\n";
    outfile << ind << "tupleIsDummy = tuple_0->getId() == 0;\n";
    outfile << ind << "toExplainSign.pop_back();\n";

    //DEBUG PRINT
    outfile << ind <<"std::cout <<\"found tuple: \";\n";
    outfile << ind <<"AuxMapHandler::getInstance().printTuple(tuple_0);\n";
    outfile << ind <<"std::cout <<\" in to explain of propFalse \\n\";\n";
    outfile << ind++ << "if(!tupleIsDummy && !TupleFactory::getInstance().isTupleFromGen(tuple_0->getId())){\n";
    outfile << ind << "std::cout<< \"FROM fixpoint and true\\n\";\n";
    //negative
    // not a is false, then its reason is the reason why a is true.
    outfile << ind++ << "if(tupleSign){\n";
    outfile << ind << "Glucose::vec<Glucose::Lit> negatedFalseReasons;\n";
    outfile << ind << "LazyPropagator::getInstance().explainTrueLiteral(tuple_0->getId(), negatedFalseReasons);\n";
    outfile << ind << "for(unsigned l = 1; l < negatedFalseReasons.size(); ++l) tupleReasons.push(Glucose::mkLit(var(negatedFalseReasons[l]), Glucose::sign(negatedFalseReasons[l])));\n";
    outfile << --ind <<"}\n";
    outfile << ind << "else tupleReasons.push(Glucose::mkLit(tuple_0->getId(), tupleSign));\n";
    outfile << ind << "continue;\n";
    outfile << --ind <<"}\n";
    for(unsigned ruleID : rules){
        const aspc::Rule& rule = program.getRule(ruleID);
        outfile << ind++ <<"if(tuple_0->getPredicateName() == AuxMapHandler::getInstance().get_" << rule.getHead().at(0).getPredicateName() <<"()){\n";
        outfile << ind << "tupleIsFromComp = true;\n";
        compileRuleByStarter(ruleID, rule, -1, componentPredicateNames, nonExitRules.size() > 0, false, false, false, true);
        outfile << --ind <<"}\n";
    }
    // outfile << ind++ << "if(!tupleIsFromComp){\n";
    // outfile << ind << "int predicateId = tuple_0->getPredicateName();\n";
    // outfile << ind << "bool canPropagate = LazyPropagator::getInstance().getPropagatorFromPredicateId(predicateId)->propagateToFalse(s, tuple_0, tupleSign, tupleReasons, lits, confl, false);\n";

    // outfile << ind++ << "if(tupleIsDummy){\n";
    // outfile << ind << "delete tuple_0;\n";
    // outfile << --ind << "}\n";

    // outfile << ind++ << "if(!canPropagate)\n";
    // outfile <<ind << "return false;\n";
    // --ind;
    // outfile << --ind << "}\n";

    outfile << ind++ << "if(tupleIsDummy && tupleIsFromComp){\n";
    outfile << ind << "delete tuple_0;\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";

    outfile << ind++ <<"if(makePropagation){\n";
    outfile << ind <<"std::cout <<\"Propagating from propagate to false: \";\n";

    outfile << ind <<"std::cout <<\"Tuple Reason: \";\n";
    outfile << ind++ <<"for(unsigned i = 0; i<tupleReasons.size(); ++i){\n";
    outfile << ind <<"std::cout <<var(tupleReasons[i]) <<\" \";\n";
    outfile << ind-- << "}\n";
    outfile << ind << "std::cout <<\"Actual reason size: \"<< tupleReasons.size() <<\"\\n\";\n";

    outfile << ind << "assert(s->currentLevel() == 0 || tupleReasons.size() >= 2);\n";

    outfile << ind << "bool foundConflict = s->isConflictPropagation(tuple->getId(), true);\n";
    outfile << ind << "bool assigned = s->isAssigned(tuple->getId());\n";
    outfile << ind++ << "if(!assigned || foundConflict){\n";
    outfile << ind++ << "if(s->currentLevel() > 0){\n";
    //reorder reason s.t. solver invariant is respected
    outfile << ind << "int currentLevelTupleIndex = -1;\n";
    outfile << ind++ << "for(unsigned i = 0; i < tupleReasons.size(); ++i){\n";
    outfile << ind++ << "if(s->levelFromPropagator(var(tupleReasons[i])) == s->currentLevel()){\n";
    outfile << ind << "currentLevelTupleIndex = i;\n";
    outfile << ind << "break;\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
    outfile << ind << "assert(currentLevelTupleIndex != -1);\n";
    outfile << ind << "Glucose::Lit temp = tupleReasons[1];\n";
    outfile << ind << "tupleReasons[1] = tupleReasons[currentLevelTupleIndex];\n";
    outfile << ind << "tupleReasons[currentLevelTupleIndex] = temp;\n";


    outfile << ind << "Glucose::CRef clause = s->externalPropagation(tuple->getId(), true);\n";
    outfile << ind++ << "if(clause != Glucose::CRef_Undef){\n";
    outfile << ind << "confl = clause;\n";
    outfile << ind << "return true;\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
    outfile << ind++ <<"else{\n";
    outfile << ind++ << "if(!assigned){\n";
    outfile << ind << "s->assignFromPropagators(Glucose::mkLit(tuple->getId(), true));\n";

    outfile << ind << "return true;\n";
    outfile << --ind << "}\n";
    outfile << ind++ << "else if(foundConflict){\n";
    outfile << ind << "lits.clear();\n";
    outfile << ind << "s->addClause_(lits);\n";
    outfile << ind << "confl = Glucose::CRef_PropConf;\n";
    outfile << ind << "return true;\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
    outfile << ind << "else return true;\n";
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

void LazyPropagatorCompiler::compileRuleByStarter(unsigned id, const aspc::Rule& rule, int starter, const std::set<std::string>& componentPreds, bool isRecursive, bool fixpointCompilation, bool interruptAfterFirstFiring, bool explainTrue, bool explainFalse){
    //std::cout <<"compiling rule: ";
    //rule.print();
    //std::cout <<"\n";
    int closingPars = 0;
    outfile << ind++ << "{\n";

    const std::vector<const aspc::Formula*> formulas = rule.getFormulas();
    std::unordered_set<std::string> boundVars;
    std::vector<int> declaredTuples;
    std::vector<std::pair<int, bool>> reasonTupleWithSign;
    //when evaluating rule by started the zero tuple has been declared outside the compileRule
    if(starter != formulas.size()){
        declaredTuples.push_back(0);
    }
    if(fixpointCompilation){
        outfile << ind << "std::vector<std::pair<std::pair<const Tuple *, bool>, int>> insertResults;\n";
        outfile << ind << "std::vector<int> propagations;\n";
    }
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
                    //define boundTupleUndef
                    if(lit->isNegated()){
                        if(explainFalse){
                            //TODO check for multiple components
                            //this can not happen since it would mean that a predicate and its
                            //negation both appear inside the same component,
                            //but would imply that P.P. is not stratified.
                            //compileAddTupleToFactoryForExplainFalse(i, lit);
                            //closingPars++;

                            outfile << ind++ << "if(tuple_" << i <<" != NULL && tuple_" << i << "->isUndef()){\n";
                            outfile << ind <<"PositiveProgramFactory::getInstance().addPossibleSupportForTuple(original->getId(), tuple_" << i << "->getId());\n";
                            outfile << ind << "tupleReasons.clear();\n";
                            outfile << ind << "return false;\n";
                            outfile << --ind <<"}\n";
                            outfile << ind++ << "if(tuple_" << i <<" != NULL && tuple_" << i << "->isTrue()){\n";
                            outfile << ind << "if(TupleFactory::getInstance().isTupleFromGen(tuple_" << i << "->getId())) tupleReasons.push(Glucose::mkLit(tuple_" << i << "->getId(), false));\n";
                            //TODO CHECK WHEN P.P. PREDICATES CAN APPEAR NEGATED IN P.P.
                            // outfile << ind++ << "else{\n";
                            // outfile << ind << "toExplain.push_back(Glucose::mkLit(tuple_" << i << "->getId(), true));\n";
                            // outfile << ind << "toExplainDummies.push_back(tuple_" << i << "->getId());\n";
                            // outfile << --ind <<"}\n";
                            outfile << --ind <<"}\n";
                            //bound literal is true
                            outfile << ind++ <<"else{\n";
                            closingPars++;
                        }
                        // the ->isFalse should become ! ->isTrue since fixpoints of components are partial
                        std::string continueOnlyWithTrueBody = !explainFalse ? " || tuple_" + std::to_string(i) + "->isFalse()" : "";
                        outfile << ind++ << "if(tuple_" << i <<" == NULL" << continueOnlyWithTrueBody << "){\n";
                    }else{
                        if(explainFalse){
                            if(positiveProgramHeadPredicates.count(lit->getPredicateName())){
                                compileAddTupleToFactoryForExplainFalse(i, lit, componentPreds);
                                closingPars++;
                            }
                        }
                        std::string continueOnlyWithTrueBody = !explainFalse ? " && tuple_" + std::to_string(i) + "->isTrue()" : "";
                        outfile << ind++ << "if(tuple_" << i <<" != NULL" << continueOnlyWithTrueBody << "){\n";
                        if(explainFalse){
                            outfile << ind ++ << "if(tuple_" << i <<" != NULL && tuple_" << i << "->isUndef()){\n";
                            outfile << ind <<"PositiveProgramFactory::getInstance().addPossibleSupportForTuple(original->getId(), tuple_" << i << "->getId());\n";
                            outfile << ind << "tupleReasons.clear();\n";
                            outfile << ind << "return false;\n";
                            outfile << --ind <<"}\n";
                            outfile << ind++ << "if(tuple_" << i << "->isFalse()){\n";
                            outfile << ind << "if(TupleFactory::getInstance().isTupleFromGen(tuple_" << i << "->getId())) tupleReasons.push(Glucose::mkLit(tuple_" << i << "->getId(), true));\n";
                            outfile << ind++ << "else{\n";
                            outfile << ind << "toExplain.push_back(tuple_" << i << ");\n";
                            outfile << ind << "toExplainSign.push_back(false);\n";
                            outfile << --ind <<"}\n";
                            outfile << --ind <<"}\n";
                            //bound literal is true
                            outfile << ind++ <<"else{\n";
                            closingPars++;
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

                    std::string generationOnlyIf = interruptAfterFirstFiring ? "&& ! generated ": "";
                    //std::string explainTrueIf = explainTrue ? " && ! firingFound ": "";
                    //std::string explainFalseIf = explainFalse ? " && ! foundReason ": "";
                    outfile << ind << structType <<" tuples_"<<i<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";

                    if(explainFalse){
                        outfile << ind << structType << " tuplesU_"<<i<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                        outfile << ind++ << "if (tuplesU_" << i << "->size() > 0){\n";
                        outfile << ind <<"PositiveProgramFactory::getInstance().addPossibleSupportForTuple(original->getId(), *(tuplesU_" << i << "->begin()));\n";
                        outfile << ind << "tupleReasons.clear();\n";
                        outfile << ind << "return false;\n";
                        outfile << --ind << "}\n";
                        outfile << ind++ << "else{\n";

                        outfile << ind << structType << " tuplesF_"<<i<<" = &"<<prefix<<"f"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                        outfile << ind++ << "for(auto i=tuplesF_"<<i<<"->begin(); i != tuplesF_"<<i<<"->end(); i++){\n";
                        outfile << ind << "if(TupleFactory::getInstance().isTupleFromGen(*i)) tupleReasons.push(Glucose::mkLit(*i, true));\n";
                        outfile << ind++ << "else{\n";
                        outfile << ind << "toExplain.push_back(TupleFactory::getInstance().getTupleFromInternalID(*i));\n";
                        outfile << ind <<"toExplainSign.push_back(false);\n";
                        outfile << --ind <<"}\n";
                        outfile << --ind <<"}\n";
                        closingPars++;

                    }
                    outfile << ind++ << "for(auto i=tuples_"<<i<<"->begin(); i != tuples_"<<i<<"->end()" << generationOnlyIf << "; i++){\n";
                    if(explainFalse && positiveProgramHeadPredicates.count(lit->getPredicateName())){

                    }
                    closingPars++;
                    declaredTuples.push_back(i);
                    reasonTupleWithSign.push_back(std::make_pair(i, true));
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
        if(i == numberOfFormulas -1){
            outfile << ind << "//Rule is firing;\n";
            //last tuple must be false when I am not doing propagation.
            //I am not doing propagation in propagateToFalse redirections
            if(explainFalse){
                std::pair<int, bool> lastTuple = reasonTupleWithSign.at(reasonTupleWithSign.size() -1);
                //outfile << ind++ << "if(!makePropagation) ";
                outfile << ind <<"assert(false);\n";
                // if(lastTuple.second)
                //     outfile << ind <<"assert(tuple_" << lastTuple.first<< "->isFalse());\n";
                // else
                //     outfile << ind <<"assert(tuple_" << lastTuple.first<< "->isTrue());\n";
                // --ind;
                
                // outfile << ind <<"PositiveProgramFactory::getInstance().removeTrueSolverChoice(tuple_0->getId());\n";
                // outfile << ind << "tupleReasons.clear();\n";
                // outfile << ind << "return false;\n";
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
            outfile << ind << "bool tupleIsFromInputInterface = TupleFactory::getInstance().isTupleFromInputInterface(head_" << index << "->getId());\n";
            outfile << ind << "std::pair<const Tuple *, bool> insertResult;\n";
            outfile << ind++ << "if(!TupleFactory::getInstance().isFact(head_"<<index<<"->getId())){\n";

            outfile << ind++ << "if(!s->currentLevel() == 0 && !head_" << index << "->isTrue()){\n";
            outfile << ind <<"bool isSATVar = head_" << index << "->getId() < s->nVars();\n";
            outfile << ind << "Glucose::vec<Glucose::Lit>& propagationReason =  !isSATVar || !s->isAssigned(head_"<< index << "->getId()) ? head_" << index << "->getReasonLits() : s->getReasonClause();\n";
            outfile << ind << "propagationReason.clear();\n";
            //add propagating literal
            outfile << ind << "propagationReason.push(Glucose::mkLit(head_" << index << "->getId(), false));\n";
            compileReasonAndSupportSaving(reasonTupleWithSign, index, "head_");
            outfile << --ind << "}\n";
            outfile << ind++ << "if(tupleIsFromInputInterface){\n";
            outfile << ind << "bool foundConflict = s->isConflictPropagation(head_" << index <<"->getId(), false);\n";
            outfile << ind << "bool assigned = s->isAssigned(head_"<< index << "->getId());\n";
            outfile << ind++ << "if(!assigned || foundConflict){\n";
            outfile << ind++ << "if(s->currentLevel() > 0){\n";
            outfile << ind << "TupleFactory::getInstance().addPropagationFromLazyProp(head_" << index << "->getId());\n";
            outfile << ind << "if(foundConflict) LazyPropagator::getInstance().explainConflictualTrueLiteral(s, head_" << index << "->getId(), s->getReasonClause());\n";
            outfile << ind << "Glucose::CRef clause = s->externalPropagation(head_" << index << "->getId(), false);\n";
            outfile << ind << "generated = true;\n";
            outfile << ind++ << "if(clause != Glucose::CRef_Undef){\n";
            outfile << ind << "confl = clause;\n";
            outfile << ind << "LazyPropagator::getInstance().storeConflictualLiteral(head_" << index << "->getId());\n";
            outfile << ind << "return generated;\n";
            outfile << --ind <<"}\n";
            outfile << --ind << "}\n";
            outfile << ind++ <<"else{\n";

            outfile << ind << "propagations.push_back(head_" << index<< "->getId());\n";
            outfile << ind << "generated = true;\n";
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";

            outfile << --ind << "}\n";
            outfile << ind ++ << "else{\n";
            outfile << ind++ << "if(head_" << index << "->isUnknown()){\n";

            outfile << ind << "generated = true;\n";
            outfile << ind << "AuxMapHandler::getInstance().initTuple(head_" << index << ");\n";
            if(isRecursive){
                if(std::find(componentPreds.begin(), componentPreds.end(), atom->getPredicateName()) != componentPreds.end()){
                    outfile << ind << "stack.push_back(head_" << index << "->getId());\n";
                }
            }
            outfile << ind << "insertResult = head_" << index <<"->setStatus(TruthStatus::True);\n";

            outfile << ind << "insertResults.push_back(std::make_pair(insertResult, LazyPropagator::INSERT_AS_TRUE));\n";
            outfile << ind << "LazyPropagator::getInstance().attachWatched(head_" << index << "->getId());\n";
            outfile << --ind << "}\n";
            outfile << --ind << "}\n";
            outfile << ind << "PositiveProgramFactory::getInstance().removeToCheckTuple(head_" << index <<"->getId());\n";
            outfile << --ind << "}\n";
        }else{
            //head starter and explaining literal. Either true of false
            if(interruptAfterFirstFiring){
                    outfile << ind << "generated = true;\n";
            }
            if(explainTrue){
                //skip head starter (otherwise tuple will be reason of itself)
                for(unsigned t = 1; t < declaredTuples.size(); ++t){
                    bool negatedTuple = !formulas[ruleOrderingsByHead[id][0][t-1]]->isPositiveLiteral();
                    //negated tuples become reasons and should eventually be explained iff they were generated at some point
                    //otherwise they are just unfounded and no reason in needed for them
                    if(negatedTuple){
                        outfile << ind++ << "if(tuple_" << declaredTuples[t] << " != NULL){\n";
                    }
                    outfile << ind++ << "if(TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples[t] << "->getId()))\n";

                    if(!negatedTuple)
                        outfile << ind << "tupleReasons.insert(tuple_" << declaredTuples[t] << "->getId());\n";
                    else
                        outfile << ind << "tupleReasons.insert(tuple_" << declaredTuples[t] << "->getId() * -1);\n";
                    --ind;
                    outfile << ind << "else toExplain.push_back(tuple_" << declaredTuples[t] << "->getId());\n";
                    if(negatedTuple){
                        outfile << --ind << "}\n";
                    }
                }
            }
        }


    }
    for (int i = closingPars; i > 0; --i) {
        outfile << --ind << "}//close par\n";
    }
    //just before closing rule scope
    if(fixpointCompilation){
        outfile << ind++ << "for(unsigned i = 0; i < insertResults.size(); ++i){\n";
        outfile << ind++ << "if(insertResults[i].second == LazyPropagator::INSERT_AS_TRUE){\n";
        outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResults[i].first);\n";
        outfile << --ind <<"}\n";

        outfile << --ind <<"}\n";
        outfile << ind++ << "for(unsigned i = 0; i < propagations.size(); ++i){\n";
        outfile << ind << "bool isAssigned = s->isAssigned(propagations[i]);\n";
        outfile << ind << "bool isConflict = s->isConflictPropagation(propagations[i], false);\n";
        outfile << ind++ << "if(!isAssigned){\n";
        outfile << ind << "s->assignFromPropagators(Glucose::mkLit(propagations[i]));\n";

        outfile << --ind << "}\n";
        outfile << ind++ << "else if(isConflict){\n";
        outfile << ind << "lits.clear();\n";
        outfile << ind << "s->addClause_(lits);\n";
        outfile << ind << "confl = Glucose::CRef_PropConf;\n";
        outfile << ind << "return generated;\n";
        outfile << --ind << "}\n";
        outfile << --ind << "}\n";
    }
    outfile << --ind << "}\n";
}

// if tuple is NULL, but it comes from a literal defined inside P.P.
// it should be generated since the predicate set of P.P. predicates might
// be partial
void LazyPropagatorCompiler::compileAddTupleToFactoryForExplainFalse(unsigned i, const aspc::Literal* lit, const std::set<std::string>& componentPreds){
        outfile << ind++ << "if(tuple_" << i << " == NULL){\n";
        outfile << ind << "Tuple* tuple_" << i << " = new Tuple(AuxMapHandler::getInstance().get_" << lit->getPredicateName() << "(), {";
        for(unsigned k=0; k<lit->getAriety(); k++){
            if(k>0) outfile << ",";
            outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
        }
        outfile << "});\n";

        //outfile << ind++ << "if(!tupleIsFromComp){\n";
        if(componentPreds.count(lit->getPredicateName())){
            outfile << ind << "toExplain.push_back(tuple_" << i << ");\n";
            outfile << ind << "toExplainSign.push_back(false);\n";
        }
        else{
            outfile << ind << "int predicateId = tuple_" << i << "->getPredicateName();\n";
            outfile << ind << "bool canPropagate = LazyPropagator::getInstance().getPropagatorFromPredicateId(predicateId)->propagateToFalse(s, tuple_" << i << ", original, tupleSign, tupleReasons, lits, confl, false);\n";
            //outfile << ind <<"delete tuple_" << i << ";\n";
            outfile << ind << "if(!canPropagate) return false;\n";
        }
        //outfile << --ind << "}\n";


        outfile << --ind << "}\n";
        outfile << ind++ << "else{\n";
}
void LazyPropagatorCompiler::compileReasonAndSupportSaving(std::vector<std::pair<int, bool>>& declaredTuples, int index, std::string tuplePrefix){
    outfile << ind <<"int indexCurrentLevelTuple = -1;\n";
    for(unsigned i = 0; i < declaredTuples.size(); ++i){
        if(declaredTuples.at(i).second){
            outfile << ind++ <<"if(TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId()) && s->levelFromPropagator(tuple_" << declaredTuples.at(i).first << "->getId()) == s->currentLevel()){\n";
            outfile << ind << "indexCurrentLevelTuple = propagationReason.size();\n";
            outfile << --ind << "}\n";
            outfile << ind << "propagationReason.push(Glucose::mkLit(tuple_" << declaredTuples.at(i).first <<"->getId(), false));\n";
            outfile << ind << "PositiveProgramFactory::getInstance().addSupported(tuple_" << declaredTuples.at(i).first << "->getId(), "<< tuplePrefix << index << "->getId());\n";
        }
        else{
            outfile << ind++ << "if(tuple_" << declaredTuples.at(i).first << "!= NULL){\n";
            outfile << ind++ <<"if(TupleFactory::getInstance().isTupleFromGen(tuple_" << declaredTuples.at(i).first <<"->getId()) && s->levelFromPropagator(tuple_" << declaredTuples.at(i).first << "->getId()) == s->currentLevel()){\n";
            outfile << ind << "indexCurrentLevelTuple = propagationReason.size();\n";
            outfile << --ind << "}\n";
            outfile << ind << "propagationReason.push(Glucose::mkLit(tuple_" << declaredTuples.at(i).first <<"->getId(), true));\n";
            outfile << ind << "PositiveProgramFactory::getInstance().addSupported(tuple_" << declaredTuples.at(i).first << "->getId(), "<< tuplePrefix << index << "->getId());\n";
            outfile << --ind <<"}\n";
        }
    }
    //DEBUG PRINT
    // outfile << ind <<"std::cout <<\"Reason: \\n\";\n";
    // outfile << ind++ <<"for(int i = 0; i < propagationReason.size(); ++i){\n";
    // outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));\n";
    // outfile << ind << "std::cout <<\" \";\n";
    // outfile << --ind << "}\n";
    // outfile << ind << "std::cout <<std::endl;\n";

    outfile << ind << "assert(propagationReason.size() >= 2);\n";
    outfile << ind++ << "if(isSATVar && indexCurrentLevelTuple != -1){\n";
    outfile << ind << "assert(s->levelFromPropagator(var(propagationReason[indexCurrentLevelTuple])) == s->currentLevel());\n";
    //switch currentLevelLiteral with literal in second position
    outfile << ind << "Glucose::Lit temp = propagationReason[1];\n";
    outfile << ind << "propagationReason[1] = propagationReason[indexCurrentLevelTuple];\n";
    outfile << ind << "propagationReason[indexCurrentLevelTuple] = temp;\n";
    outfile << --ind <<"}\n";
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
    outfile << ind << "#include \"../solver/AbstractLazyPropagator.h\"\n";
    outfile << ind << "#include \"../solver/PositiveProgramFactory.h\"\n";
    outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
    outfile << ind << "#include \"../datastructures/VectorAsSet.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

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
        // for(unsigned i = 0; i < scc.size(); ++i){
        //     outfile << ind << "headPredicates.push_back(AuxMapHandler::getInstance().get_" << depManager.getPredicateName(scc[i]) << "());\n";
        //     headPredicates.insert(depManager.getPredicateName(scc[i]));
        // }
        for(const aspc::Atom head: rule.getHead()){
            if(!headPredicates.count(head.getPredicateName())){
                outfile << ind << "headPredicates.push_back(AuxMapHandler::getInstance().get_" << head.getPredicateName() << "());\n";
                headPredicates.insert(head.getPredicateName());
            }
        }

    }
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
    outfile << ind << "int LazyPropagator::INSERT_AS_UNDEF = 0;\n";
    outfile << ind << "int LazyPropagator::INSERT_AS_TRUE = 1;\n";
    //outfile << ind << "int LazyPropagator::UPDATE_TO_TRUE = 2;\n";
    outfile << ind++ << "LazyPropagator::LazyPropagator(){\n";
    //int propagatorId = 0;
    for(int i = 0; i < propagatorNames.size(); ++i){
        std::string className = propagatorNames[i];
        //std::string className="Rule_"+std::to_string(ruleId)+"_Propagator";
        outfile << ind << "propagators.push_back(new " << className << "());\n";
        outfile << ind << "propagators.back()->setId(" << i << ");\n";
        //outfile << ind << "propagators.back()->setId("<<propagatorId<<");\n";
        //propagatorId++;
    }
    //outfile << ind <<"//copies are not a problem. This is executed once and watched predicates are supposed to be a few\n";
    outfile << ind << "predicateToPropagator = std::unordered_map<int, int>();\n";
    outfile << ind << "for(unsigned i = 0; i < AuxMapHandler::getInstance().predicateCount(); ++i) watchedPredicateToPropagators.emplace(std::make_pair(i, std::vector<int>()));\n";

    outfile << ind++ << "for(int i = 0; i < propagators.size(); ++i){\n";
    outfile << ind << "tuplesByPropagator.push_back(std::vector<int>());\n";
    outfile << ind << "std::vector<int> watchedPredicates = propagators[i]->getWatchedPredicates();\n";
    outfile << ind << "for(unsigned t = 0; t < watchedPredicates.size(); ++t) watchedPredicateToPropagators[watchedPredicates[t]].push_back(propagators[i]->getId());\n";
    //outfile << ind << "watchedPredicateToPropagators.emplace(std::make_pair(propagators[i]->getId(), propagators[i]->getWatchedPredicates()));\n";
    outfile << ind << "std::vector<int> predicatesDefinedByProp = propagators[i]->getHeadPredicates();\n";
    outfile << ind++ <<"for(int j = 0; j < predicatesDefinedByProp.size(); ++j){\n";
    outfile << ind << "predicateToPropagator.emplace(std::make_pair(predicatesDefinedByProp[j], propagators[i]->getId()));\n";
    outfile << ind << "predicatedDefinedByPositiveProgram.insert(predicatesDefinedByProp[j]);\n";
    outfile << --ind << "}\n";

    outfile << --ind << "}\n";

    outfile << --ind << "}\n";
}