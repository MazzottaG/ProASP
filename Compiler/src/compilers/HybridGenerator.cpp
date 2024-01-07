#include "HybridGenerator.h"

void HybridGenerator::compileComponentRules(std::ofstream& outfile,Indentation& ind,unsigned starter,unsigned componentId,bool isRecursive,int ruleIndex){
}
void HybridGenerator::buildConstraintGrounder(int ruleId,std::string className,std::ofstream& outfile,Indentation& ind){
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
    std::cout << "Compiling constraint ";
    program.getRule(ruleId).print();
    outfile << ind << "class "<<className<<": public AbstractGenerator{\n";
    outfile << ++ind << "public:\n";
    ind++;
        outfile << ind++ << "void generate(Glucose::SimpSolver* solver)override {\n";
            outfile << ind << "std::vector<int> clause;\n";
            AbstractGeneratorCompiler* compiler = NULL;
            // std::cout << "Debug original predicates HybridGenerator_1";
            // for(std::string pred : originalPredicates){
            //     std::cout << pred << " ";
            // }
            // std::cout << std::endl;
            compiler = new GrounderGenCompiler(outfile,ind.getDepth(),&program.getRule(ruleId),predNames,predIds,predicateToStruct,prgRewriter->getAggregateGrounding(ruleId),originalPredicates);
            compiler->compileNoStarter(false);
            auto usedMaps = compiler->getUsedAuxMaps();
            for(auto maps : usedMaps){
                for(auto indices : maps.second)
                    auxMapCompiler->addAuxMap(maps.first,indices);
            } 
        #ifdef DEBUG_GEN
            outfile << ind << "std::cout << \"Generator "<<className<<"\"<<std::endl;\n";
        #endif
        outfile << --ind << "}\n";
        outfile << ind++ << "void printName()const {\n";
            outfile << ind << "std::cout << \"Generator "<<className<<"\"<<std::endl;\n";
        outfile << --ind << "}\n";
    ind--;
    outfile << --ind << "};\n";
    std::cout << "Compiled constraint"<<std::endl;
    
    outfile << ind << "#endif\n";
}
void HybridGenerator::buildComponentGenerator(int componentId,std::string className,std::ofstream& outfile,Indentation& ind){
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
            outfile << ind << "std::vector<Glucose::Lit> domainAtoms;\n";
    const auto& components = depHandler.getComponents(negDep);
    bool isRecursive = false; // components[componentId].size() > 1;
    // if(!isRecursive){
    for(std::string predicate : components[componentId]){
        // std::string predicate = *components[componentId].begin();
        for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
            aspc::Rule r = program.getRule(ruleIndex);
            const std::vector<const aspc::Formula*>& body = r.getFormulas();
            for(unsigned i = 0; i<body.size(); i++){
                if(body[i]->isLiteral() && body[i]->isPositiveLiteral()){
                    const aspc::Literal* lit = (const aspc::Literal*) body[i];
                    // if(predicate == lit->getPredicateName()){
                    if(components[componentId].count(lit->getPredicateName())){
                        isRecursive=true;
                        break;
                    }
                }
            }
            if(isRecursive) break;
        }                 
    }
    std::cout << "Compiling "<< (isRecursive ? "recursive ": "") << "component: {";
    for(const std::string& predicate: components[componentId])
        std::cout << predicate << " ";
    std::cout << "}"<<std::endl;
    
    if(isRecursive)
        outfile << ind << "std::vector<int> stack;\n";
    for(const std::string& predicate: components[componentId]){
        for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
            AbstractGeneratorCompiler* compiler = NULL;
            
            if(ruleLabel[ruleIndex] == Rewriter::GROUND_RULE){
                // std::cout << "Debug original predicates HybridGenerator_2";
                // for(std::string pred : originalPredicates){
                //     std::cout << pred << " ";
                // }
                // std::cout << std::endl;
                compiler = new GrounderGenCompiler(outfile,ind.getDepth(),&program.getRule(ruleIndex),predNames,predIds,predicateToStruct,prgRewriter->getAggregateGrounding(ruleIndex),originalPredicates);
            }
            else if(ruleLabel[ruleIndex] == Rewriter::TO_GENERATE){
                
                compiler = new AbstractGeneratorCompiler(outfile,ind.getDepth(),&program.getRule(ruleIndex),predNames,predIds,predicateToStruct,originalPredicates);
            }
            else{
                compiler = new DomainRuleCompiler(outfile,ind.getDepth(),&program.getRule(ruleIndex),predNames,predIds,predicateToStruct,originalPredicates);
            }
            compiler->compileNoStarter(isRecursive);
            auto usedMaps = compiler->getUsedAuxMaps();
            for(auto maps : usedMaps){
                for(auto indices : maps.second)
                    auxMapCompiler->addAuxMap(maps.first,indices);
            } 
        }
    }
    if(isRecursive){
        std::string sign = "Undef";
        outfile << ind++ << "while(!stack.empty()){\n";
            outfile << ind << "Tuple* starter = TupleFactory::getInstance().getTupleFromInternalID(stack.back());\n";
            outfile << ind << "stack.pop_back();\n";
            outfile << ind++ << "if(starter != NULL){\n";
            outfile << ind << "TruthStatus value = "<<sign<<";\n";
            std::string ifBody = "";
            for(const std::string& predicate: components[componentId]){
                for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                    if(ruleLabel[ruleIndex] == Rewriter::DOMAIN_RULE){
                        std::string sharedPredicate = program.getRule(ruleIndex).getHead()[0].getPredicateName();
                        if(ifBody != "") ifBody += " || ";
                        ifBody+="starter->getPredicateName() == AuxMapHandler::getInstance().get_"+sharedPredicate+"()";
                    }
                }
            }
            if(ifBody != ""){
                outfile << ind++ << "if("<<ifBody<<"){\n";
                    outfile << ind << "value = True;\n";
                outfile << --ind << "}\n";
            }
            outfile << ind << "const auto& insertResult = starter->setStatus(value);\n";
            outfile << ind++ << "if(insertResult.second){\n";
                #ifdef DEBUG_GEN
                outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(starter);\n";
                #endif
                outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(starter->getId());\n";
                if(ifBody == ""){
                    outfile << ind << "AuxMapHandler::getInstance().initTuple(starter);\n";
                    outfile << ind << "AuxMapHandler::getInstance().insert"<<sign<<"(insertResult);\n";
                }else{
                    outfile << ind++ << "if("<<ifBody<<"){\n";
                        outfile << ind << "AuxMapHandler::getInstance().initTuple(starter);\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
                        outfile << ind << "domainAtoms.push_back(Glucose::mkLit(starter->getId(),false));\n";
                    outfile << --ind << "}else{\n";
                        outfile << ind << "AuxMapHandler::getInstance().initTuple(starter);\n";
                        outfile << ind << "AuxMapHandler::getInstance().insert"<<sign<<"(insertResult);\n";
                    outfile << --ind << "}\n";
                }
                outfile << ind << "while (starter->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                // else outfile << ind << "extendedModel.push_back(starter->getId());\n";
            outfile << --ind << "}else continue;\n";
            for(const std::string& predicate: components[componentId]){
                for(unsigned ruleIndex : program.getRulesForPredicate(predicate)){
                    const aspc::Rule* rule = &program.getRule(ruleIndex);
                    AbstractGeneratorCompiler* compiler = NULL;
                    if(ruleLabel[ruleIndex] == Rewriter::GROUND_RULE)
                        compiler = new GrounderGenCompiler(outfile,ind.getDepth(),rule,predNames,predIds,predicateToStruct,prgRewriter->getAggregateGrounding(ruleIndex),originalPredicates);
                    else if(ruleLabel[ruleIndex] == Rewriter::TO_GENERATE)
                        compiler = new AbstractGeneratorCompiler(outfile,ind.getDepth(),rule,predNames,predIds,predicateToStruct,originalPredicates);
                    else{
                        compiler = new DomainRuleCompiler(outfile,ind.getDepth(),rule,predNames,predIds,predicateToStruct,originalPredicates);
                    }
                    compiler->compileFromStarter(isRecursive);

                    auto usedMaps = compiler->getUsedAuxMaps();
                    for(auto maps : usedMaps){
                        for(auto indices : maps.second)
                            auxMapCompiler->addAuxMap(maps.first,indices);
                    }
                }                
            }           
            outfile << --ind << "} else std::cout << \"Warning null tuple in generation stack\"<<std::endl;\n";
        outfile << --ind << "}\n";
    }

        #ifdef DEBUG_GEN
            outfile << ind << "std::cout << \"Generator "<<className<<"\"<<std::endl;\n";
        #endif
            outfile << ind << "Glucose::vec<Glucose::Lit> unitClause;\n";
            outfile << ind++ << "for(unsigned i = 0; i<domainAtoms.size(); i++){\n";
                outfile << ind << "unitClause.clear();\n";
                outfile << ind << "unitClause.push(domainAtoms[i]);\n";
                outfile << ind << "solver->addClause_(unitClause);\n";
            outfile << --ind << "}\n";
        outfile << --ind << "}\n";
        outfile << ind++ << "void printName()const {\n";
            outfile << ind << "std::cout << \"Generator "<<className<<"\"<<std::endl;\n";
        outfile << --ind << "}\n";
    ind--;
    outfile << --ind << "};\n";
    
    outfile << ind << "#endif\n";
    std::cout << "Compiled Component"<<std::endl;
    return;
}
void HybridGenerator::compile(){
    const auto& scc = depHandler.computeSCC(negDep);
    const auto& components = depHandler.getComponents(negDep);
    
    Indentation ind(0);
    std::string name = "Generator";
    std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/generators/"+name+".cc";

    std::ofstream outfile(executorPath);
    if(!outfile.is_open()){
        std::cout << "Error unable to open Generator file "<<executorPath<<std::endl;
        exit(180);
    } 

    outfile << ind << "#include \"../solver/"+name+".h\"\n\n";
    outfile << ind << "#include <map>\n\n";
    
    for(int componentId = components.size()-1; componentId >= 0; componentId--){
        std::string className="Comp_"+std::to_string(componentId)+"_Gen";
        outfile << ind << "#include \"../generators/"<<className<<".h\"\n\n";
    }
    for(int ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
        if(!program.getRule(ruleId).isConstraint()) continue;
        Indentation ind_gen(0);
        std::string className="Constr_"+std::to_string(ruleId)+"_Gen";
        outfile << ind << "#include \"../generators/"<<className<<".h\"\n\n";
    }
    outfile << ind++ << name << "::" << name << "(){\n";
        outfile << ind << "remappedId = NULL;\n";
    for(int componentId = components.size()-1; componentId >= 0; componentId--){
            Indentation ind_gen(0);
            std::string className_gen="Comp_"+std::to_string(componentId)+"_Gen";
            std::string executorPath_gen = executablePath + "/../../glucose-4.2.1/sources/simp/generators/"+className_gen+".h";
            std::ofstream outfile_gen(executorPath_gen);
            if(!outfile_gen.is_open()){
                std::cout << "Error unable to open "+className_gen+" file "<<executorPath_gen<<std::endl;
                exit(180);
            } 
            buildComponentGenerator(componentId,className_gen,outfile_gen,ind_gen);
            outfile_gen.close();
            std::string className="Comp_"+std::to_string(componentId)+"_Gen";
            outfile << ind << "generators.push_back(new "<<className<<"());\n";
            outfile << ind << "solvedByGenerator = " << (/*solvedByGenerator*/ false ? "true" : "false")<<";\n";
    }
    for(int ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
        if(!program.getRule(ruleId).isConstraint()) continue;
        Indentation ind_gen(0);
        std::string className_gen="Constr_"+std::to_string(ruleId)+"_Gen";
        std::string executorPath_gen = executablePath + "/../../glucose-4.2.1/sources/simp/generators/"+className_gen+".h";
        std::ofstream outfile_gen(executorPath_gen);
        if(!outfile_gen.is_open()){
            std::cout << "Error unable to open "+className_gen+" file "<<executorPath_gen<<std::endl;
            exit(180);
        } 
        buildConstraintGrounder(ruleId,className_gen,outfile_gen,ind_gen);
        outfile_gen.close();
        std::string className="Constr_"+std::to_string(ruleId)+"_Gen";
        outfile << ind << "generators.push_back(new "<<className<<"());\n";
    }
    outfile << --ind << "}\n";
    outfile << ind++ << "void "<<name<<"::computePossibleSums(){\n";

        for(const auto& aggrSetPred : sumAggregateIdData){
            std::vector<aspc::Atom> atoms;
            for(std::string atomstr : {aggrSetPred.first,aggrSetPred.second}){
                unsigned start=0;
                std::vector<std::string> terms;
                std::string predicate;
                for(unsigned i=0;i<atomstr.size();i++){
                    if(atomstr[i] == '@'){
                        if(start == 0)
                            predicate = atomstr.substr(start,i-start);
                        else
                            terms.push_back(atomstr.substr(start,i-start));
                        start=i+1;
                    }
                }
                if(start == 0)
                    predicate = atomstr;
                else
                    terms.push_back(atomstr.substr(start,atomstr.size()));
                atoms.push_back(aspc::Atom(predicate,terms));
            }
            aspc::Atom* aggId=&atoms[0];
            aspc::Atom* aggSet=&atoms[1];

            std::vector<unsigned> aggSetIndex;
            std::unordered_set<std::string> aggIdVars;
            aspc::Literal(false,*aggId).addVariablesToSet(aggIdVars);
            for(unsigned k = 0; k < aggSet->getAriety(); k++){
                if(aggSet->isVariableTermAt(k) && aggIdVars.count(aggSet->getTermAt(k))){
                    aggSetIndex.push_back(k);
                }
            }
            
            std::vector<unsigned> aggIdIndex;
            std::unordered_set<std::string> aggSetVars;
            aspc::Literal(false,*aggSet).addVariablesToSet(aggSetVars);
            for(unsigned k = 0; k < aggId->getAriety(); k++){
                if(aggId->isVariableTermAt(k) && aggSetVars.count(aggId->getTermAt(k))){
                    aggIdIndex.push_back(k);
                }
            }

            auxMapCompiler->addAuxMap(aggId->getPredicateName(),{});
            auxMapCompiler->addAuxMap(aggSet->getPredicateName(),aggSetIndex);

            outfile << ind++ << "{\n";
                outfile << ind << "const std::vector<int>* aggregateIds = &AuxMapHandler::getInstance().get_u"<<aggId->getPredicateName()<<"_()->getValuesVec({});\n";
                outfile << ind++ << "for(unsigned i=0;i<aggregateIds->size();i++){\n";
                    outfile << ind << "int it = aggregateIds->at(i);\n";
                    outfile << ind << "const Tuple* currentTuple = TupleFactory::getInstance().getTupleFromInternalID(it);\n";
                    outfile << ind << "const IndexedSet* aggrSetTuples = &AuxMapHandler::getInstance().get_u"<<aggSet->getPredicateName()<<"_";
                    for(unsigned k : aggSetIndex){
                        outfile << k << "_";
                    }
                    outfile << "()->getValuesSet({";
                    for(unsigned k : aggIdIndex){
                        outfile << "currentTuple->at("<<k<<")";
                        if(k != aggIdIndex.back()){
                            outfile << ",";
                        }
                    }
                    outfile << "});\n";
                    outfile << ind << "int& possSum = TupleFactory::getInstance().getPossibleSumForLit(it);\n";
                    outfile << ind++ << "for(auto itUndef=aggrSetTuples->begin(); itUndef!=aggrSetTuples->end(); itUndef++){\n";
                        // outfile << ind << "std::cout<<\"updating sum considering: \";TupleFactory::getInstance().getTupleFromInternalID(*itUndef)->print();\n";
                        outfile << ind << "possSum+=TupleFactory::getInstance().getTupleFromInternalID(*itUndef)->at("<<predicateToAggrIndex[aggSet->getPredicateName()]<<");\n";
                    outfile << --ind << "}\n";
                outfile << --ind << "}\n";
            outfile << --ind << "}\n";
        }

    outfile << --ind << "}\n";
    outfile << ind++ << "void "<<name<<"::reorderAggregateSets(){\n";
        bool foundAggrSet = false;
        for(auto& pair : predicateToStruct){
            if(pair.second != "Vec"){
                if(!foundAggrSet){
                    foundAggrSet=true;
                    outfile << ind++ << "if(remappedId != NULL) delete remappedId;\n";
                        outfile << ind-- << "remappedId = new std::unordered_map<int,int>();\n";
                    outfile << ind << "std::vector<int> ordered_ids;\n";
                    outfile << ind << "std::vector<int> tuplesIdOrdered;\n";
                    outfile << ind << "std::map<int, TupleLight*> idToTuples;\n";
                    outfile << ind << "int currentIdIndex=0;\n";
                }
                outfile << ind++ << "{\n";
                    outfile << ind << "TupleFactory::getInstance().setIndexForAggregateSet("<<predicateToAggrIndex[pair.first]<<",AuxMapHandler::getInstance().get_"<<pair.first<<"());\n";
                    // TODO: check what happens if two aggregate with one literal sums over two different terms
                    outfile<<ind<<"std::cout<<\"Ordering\"<<std::endl;\n";
                    auxMapCompiler->addAuxMap(pair.first,{});
                    outfile << ind << "IndexedSet* tuples = &AuxMapHandler::getInstance().get_u"<<pair.first<<"_()->getValuesSet({});\n"; 
                    outfile << ind << "ordered_ids.reserve(tuples->size());\n";
                    outfile << ind << "tuplesIdOrdered.reserve(tuples->size());\n";
                    outfile << ind++ << "while(!tuples->empty()){\n";
                        outfile << ind << "int id = *tuples->begin();\n";
                        outfile << ind << "tuplesIdOrdered.push_back(id);\n";
                        outfile << ind << "ordered_ids.push_back(id);\n";
                        outfile << ind << "idToTuples[id]=TupleFactory::getInstance().getTupleFromInternalID(id);\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(id);\n";
                        outfile << ind << "idToTuples[id]->setStatus(UNKNOWN);\n";
                    outfile << --ind << "}\n";
                    outfile << ind << "std::stable_sort(tuplesIdOrdered.begin(),tuplesIdOrdered.end(),&Generator::compTuple);\n";
                    outfile << ind++ << "for(int id: tuplesIdOrdered){\n";
                        outfile << ind << "TupleLight* t=idToTuples[id];\n";
                        outfile << ind << "remappedId->insert(std::make_pair(t->getId(),ordered_ids[currentIdIndex]));\n";
                        outfile << ind << "TupleFactory::getInstance().setId(t,ordered_ids[currentIdIndex++]);\n";
                        outfile << ind << "const auto& insertResult = t->setStatus(Undef);\n";
                        outfile << ind++ << "if (insertResult.second) {\n";
                            outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(t->getId());\n";
                            outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                        outfile << --ind << "}\n";

                    outfile << --ind << "}\n";
                    #ifdef TRACE_PROPAGATOR
                        outfile << ind++ << "for(int id :u"<<pair.first<<"_.getValuesSet({})){\n";
                            outfile << ind << "std::cout<<id<<\" \";TupleFactory::getInstance().getTupleFromInternalID(id)->print();\n";
                        outfile << --ind << "}\n";
                    #endif
                    outfile << ind << "ordered_ids.clear();\n";
                    outfile << ind << "tuplesIdOrdered.clear();\n";
                    outfile << ind << "idToTuples.clear();\n";
                    outfile << ind << "currentIdIndex=0;\n";
                outfile << --ind << "}\n";
            }
        }
    outfile << --ind << "}\n";
    outfile.close();

}