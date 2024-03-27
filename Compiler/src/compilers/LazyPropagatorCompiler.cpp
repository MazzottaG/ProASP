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
}

void LazyPropagatorCompiler::compileSCC(std::vector<int> scc, unsigned index){
    openPropagatorFile(index);
    compileComponentWatched(scc, index);
    closePropagatorFile();
}

// void LazyPropagatorCompiler::compileConstraints(){
//     unsigned index = 0;
//     for(const aspc::Rule& r: program.getRules()){
//         if(r.isConstraint()){ 
//             std::cout <<"Compiling Constraint with lazy propagators\n";
//             openPropagatorFile(false, index);
//             closePropagatorFile();
//             index++;

//         }
//     }
// }


void LazyPropagatorCompiler::openPropagatorFile(unsigned compID){

    ind = Indentation(0);
    std::string prefix = "Comp";
    std::string className = prefix +"_"+std::to_string(compID)+"_Propagator";
    std::string executorPath = execPath + "/../../glucose-4.2.1/sources/simp/propagators/"+className+".h";
    outfile =  std::ofstream(executorPath);
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
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

    outfile << ind++ << "class "<<className<<": public AbstractPropagator{\n";
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

// void LazyPropagatorCompiler::computePropagatorOrder(){
//     std::vector<std::vector<int>> sccs = depManager.getSCC();

// }