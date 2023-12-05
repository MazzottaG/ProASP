#include "DataStructureCompiler.h"

void DataStructureCompiler::printAuxMap()const{
    for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : auxMapNameForPredicate){
        for(const std::vector<unsigned>& indices : pair.second){
            std::cout << pair.first << "_";
            for(unsigned k : indices) std::cout << k << "_";
            std::cout << std::endl;
        }
    }
}
void DataStructureCompiler::addAuxMap(std::string predicate,std::vector<unsigned> terms){
    auxMapNameForPredicate[predicate].insert(terms);
}
void DataStructureCompiler::buildAuxMapHandler(std::string executablePath,const std::vector<std::string>& predNames,const std::unordered_map<std::string,std::string>& predicateToStruct){
    Indentation ind(0);
    std::string executorPath = executablePath + "/../../glucose-4.2.1/sources/simp/solver/AuxMapHandler.h";
    std::ofstream outfile(executorPath);
	if(!outfile.is_open()){
		std::cout << "Error unable to open AuxMapHandler file "<<executorPath<<std::endl;
		exit(180);
	} 
	outfile << ind << "#ifndef AUXMAPHANDLER_H\n";
    outfile << ind << "#define AUXMAPHANDLER_H\n";

    outfile << ind << "#include <vector>\n";
    outfile << ind << "#include \"../datastructures/AuxiliaryMapSmart.h\"\n";
    outfile << ind << "#include \"../utils/ConstantsManager.h\"\n";
    outfile << ind << "#include \"../datastructures/TupleFactory.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";
    
    outfile << ind++ << "class AuxMapHandler{\n";
        outfile << ind++ << "public:\n";
            outfile << ind++ << "static AuxMapHandler& getInstance(){\n";
                outfile << ind << "static AuxMapHandler instance;\n";
                outfile << ind << "return instance;\n";
            outfile << --ind << "}\n";
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE=indices.size()*CHAR_BIT*sizeof(int);
                    for(char sign : {'u','f','p'}){
                        outfile << ind << "AuxMap<"<<BITSETSIZE<<">* get_"<<sign << pair.first << "_";
                        for(unsigned k : indices) outfile << k << "_";
                        outfile << "(){return ";
                        outfile << "&"<<sign << pair.first << "_";
                        for(unsigned k : indices) outfile << k << "_";
                        outfile<<";}"<<std::endl;
                    }
                }
            }
            for(std::string pred : predNames){
                outfile << ind << "int get_"<< pred << "()const { return _"<<pred<<";}\n";
            }
            outfile << ind++ << "int getPredicateId(const std::string& predicateName) {\n";
                outfile << ind << "auto pair = predicateIds.emplace(predicateName,predicateNames.size());\n";
                outfile << ind++ << "if(pair.second){\n";
                    outfile << ind << "TupleFactory::getInstance().addPredicate();\n";
                    outfile << ind << "predicateNames.push_back(predicateName);\n";
                outfile << --ind << "}\n";
                outfile << ind << "return pair.first->second;\n";
            outfile << --ind << "}\n";
            outfile << ind << "std::string unmapPredicate(int predicateId)const {return predicateNames[predicateId];}\n";
            outfile << ind << "unsigned predicateCount()const {return predicateNames.size();}\n";
            for(auto pair : std::unordered_map<std::string,char>({{"Undef",'u'},{"True",'p'},{"False",'f'}})){
                outfile << ind++ << "void insert"<<pair.first<<"(const std::pair<const Tuple *, bool>& insertResult){\n";
                    bool firstIf=true;
                    const auto& auxMaps = getAuxMapNameForPredicate();
                    for(const std::string& predicate: predNames){
                        std::string printElse = !firstIf ? "else " : "";
                        auto it = auxMaps.find(predicate);
                        if(it!=auxMaps.end()){
                            auto itPredStruct = predicateToStruct.find(predicate);
                            std::string predStruct = itPredStruct == predicateToStruct.end() ? "" : itPredStruct->second;
                            outfile << ind++ << printElse << "if(insertResult.first->getPredicateName() == AuxMapHandler::getInstance().get_"<<predicate<<"()){\n";
                            for(const std::vector<unsigned>& indices : it->second){
                                outfile << ind << "AuxMapHandler::getInstance().get_"<<pair.second<< predicate << "_";
                                for(unsigned k :indices) outfile << k << "_";
                                outfile <<"()->insert2"<<predStruct<<"(*insertResult.first);\n";
                            }
                            outfile << --ind << "}\n";
                            firstIf=false;        
                        }
                    }
                outfile << --ind <<"}\n";
            }
            outfile << ind++ << "void printTuple(const Tuple* t){\n";
                // outfile << ind << "if(t->isFalse()) std::cout << \"not \";\n";
                // outfile << ind << "if(t->isUndef()) std::cout << \"undef \";\n";
                outfile << ind << "if(t->getPredicateName() == -1) {std::cout << t->getId(); return;}\n";
                outfile << ind << "std::cout << unmapPredicate(t->getPredicateName()) << \"(\";\n";
                outfile << ind++ << "for(int i=0;i<t->size();i++){\n";
                    outfile << ind << "if(i>0) std::cout << \",\";\n";
                    outfile << ind << "std::cout << ConstantsManager::getInstance().unmapConstant(t->at(i));\n";
                outfile << --ind << "}\n";
                outfile << ind << "std::cout << \") \";\n";
            outfile << --ind << "}\n";
            
        ind--;
        outfile << ind++ << "private:\n";
            outfile << ind++ << "AuxMapHandler()";
            bool first=true;
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE = indices.size()*CHAR_BIT*sizeof(int);
                    for(char sign : {'u','f','p'}){
                        outfile << (first ? ": " : ", ") << sign << pair.first << "_";
                        for(unsigned k : indices) outfile << k << "_";

                        outfile << "({";
                        for (unsigned k = 0; k < indices.size(); k++) {
                            if (k > 0) {
                                outfile << ",";
                            }
                            outfile << indices[k];
                        }
                        outfile << "})";
                        first=false;
                    }
                }
            }
            outfile << (first ? ": " : ", ") << "predicateNames({";
            first = true;
            for(const auto & pred : predNames){
                if(!first) outfile << ",";
                outfile << "\"" << pred << "\"";
                first=false;
            }
            outfile << "}){\n";
                for(unsigned predId=0;predId < predNames.size(); predId++){
                    outfile << ind << "predicateIds[\""<<predNames[predId]<<"\"]="<<predId<<";\n";
                }
                outfile << ind++ << "for(unsigned i=0;i<predicateCount();i++)\n";
			        outfile << ind-- << "TupleFactory::getInstance().addPredicate();\n";

            outfile << --ind <<"}\n";
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE=indices.size()*CHAR_BIT*sizeof(int);
                    for(char sign : {'u','f','p'}){
                        outfile << ind << "AuxMap<"<<BITSETSIZE<<"> "<< sign << pair.first << "_";
                        for(unsigned k : indices) outfile << k << "_";
                        outfile << ";"<<std::endl;
                    }
                }
            }
            for(unsigned k=0; k<predNames.size(); k++){
                outfile << ind << "int _"<<predNames[k] << " = " << k << ";\n";
            }
            outfile << ind << "std::vector<std::string> predicateNames;\n";
            outfile << ind << "std::unordered_map<std::string,unsigned> predicateIds;\n";
    ind--;
    outfile << --ind << "};\n";
    outfile << ind << "#endif\n";
    outfile.close();
}
std::pair<std::vector<std::vector<unsigned>>,std::vector<std::vector<unsigned>>> DataStructureCompiler::declarePropagatorDataStructure(const aspc::Rule& rule){
    std::cout << "Declaring structure for ";rule.print();
    // std::cout << "----------------------- Before watcher -----------------------"<<std::endl;
    // printAuxMap();
    // std::cout << "--------------------------------------------------------------"<<std::endl;
    
    // general order + ordering starting literal in the body + ordering from head atom + watched struct
    auto body = rule.getFormulas();
    auto head = rule.getHead();
    std::vector<unsigned> emptyIndices;

    if(!rule.isConstraint()){
        if(body.size() == 1 && body[0]->isLiteral()){
            auxMapNameForPredicate[((const aspc::Literal*)body[0])->getPredicateName()].insert(emptyIndices);
        }
    }
    {
        //declaring watcher structure
        if(!rule.isConstraint()){
            for(aspc::Atom h : head){
                auxMapNameForPredicate[h.getPredicateName()].insert(emptyIndices);
            }
        }else{
            for(const aspc::Formula* f : body){
                if(f->isLiteral()){
                    std::string predicate = ((const aspc::Literal*)f)->getPredicateName();
                    auxMapNameForPredicate[predicate].insert(emptyIndices);
                }
            }
        }
    }
    
    // std::cout << "----------------------- After watcher -----------------------"<<std::endl;
    // printAuxMap();
    // std::cout << "--------------------------------------------------------------"<<std::endl;
    
    std::vector<std::vector<unsigned>> orderByStartersHead;
    for(unsigned starter = 0; starter < head.size(); starter++){
        orderByStartersHead.push_back({});
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;

        aspc::Literal lit(false,head[starter]);
        lit.addVariablesToSet(boundVars);
        auxMapNameForPredicate[lit.getPredicateName()].insert(std::vector<unsigned>({}));
        unsigned selectedFormula=0;
        std::vector<unsigned>* currentOrdering=&orderByStartersHead.back();
        while (selectedFormula < body.size()){
            selectedFormula = body.size();
            bool notVisited = false;
            for(unsigned i=0; i<body.size(); i++){
                if(!visitedFormulas[i]){
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
                    auxMapNameForPredicate[literal->getPredicateName()].insert(boundIndices);
                    literal->addVariablesToSet(boundVars);
                }else{
                    if(currentFormula->isBoundedValueAssignment(boundVars)){
                        const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) currentFormula;
                        boundVars.insert(ineq->getAssignedVariable(boundVars));
                    }
                }
            }else if(notVisited){
                std::cout << "Error ordering rule ";rule.print();
                exit(180);
            }
        }
    }

    std::vector<std::vector<unsigned>> orderByStarters;
    for(unsigned starter = 0; starter <= body.size(); starter++){
        orderByStarters.push_back({});
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;
        if(starter < body.size()){
            //component empty means declare structure for rule propagators            
            const aspc::Formula* startingFormula = body[starter];
            if(!startingFormula->isLiteral()) continue;
            
            // starting formula is a positive literal
            const aspc::Literal* literal = (const aspc::Literal*) startingFormula;
            visitedFormulas[starter]=true;
            startingFormula->addVariablesToSet(boundVars);
        }
        unsigned selectedFormula=0;
        std::vector<unsigned>* currentOrdering=&orderByStarters.back();
        while (selectedFormula < body.size()){
            selectedFormula = body.size();
            bool notVisited = false;
            for(unsigned i=0; i<body.size(); i++){
                if(!visitedFormulas[i]){
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
                    auxMapNameForPredicate[literal->getPredicateName()].insert(boundIndices);
                    literal->addVariablesToSet(boundVars);
                }else{
                    if(currentFormula->isBoundedValueAssignment(boundVars)){
                        const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) currentFormula;
                        boundVars.insert(ineq->getAssignedVariable(boundVars));
                    }
                }
            }else if(notVisited){
                std::cout << "Error ordering rule ";rule.print();
                exit(180);
            }
        }
    }    
    return std::make_pair(orderByStarters,orderByStartersHead);
}
std::vector<unsigned> DataStructureCompiler::reorderSimpleBody(const std::vector<const aspc::Formula*>& body, std::unordered_set<std::string>& boundVars, int starter){
    // std::cout << "Computing order"<<std::endl;
    std::vector<bool> visitedFormulas(body.size(),false);
    if(starter >= 0) visitedFormulas[starter]=true;
    for(unsigned i=0; i<body.size(); i++){
        if(body[i]->containsAggregate())
            visitedFormulas[i]=true;
    }
    // std::cout << "Ignoring formulas ";
    // for(unsigned i=0; i<body.size(); i++){
    //     if(visitedFormulas[i])
    //         body[i]->print();
    // }
    // std::cout << std::endl;
    std::vector<unsigned> orderedFormulas;
    
    unsigned selectedFormula=0;
    while (selectedFormula < body.size()){
        selectedFormula = body.size();
        bool notVisited = false;
        for(unsigned i=0; i<body.size(); i++){
            if(!visitedFormulas[i]){
                notVisited=true;
                if(body[i]->isBoundedLiteral(boundVars) || body[i]->isBoundedRelation(boundVars) || body[i]->isBoundedValueAssignment(boundVars)){
                    selectedFormula=i;
                    break;
                }
                if(body[i]->isPositiveLiteral() && selectedFormula == body.size()) {
                    selectedFormula=i;
                }
            }
        }
        if(selectedFormula != body.size()){
            std::cout << selectedFormula<<" ";
            visitedFormulas[selectedFormula]=true;
            const aspc::Formula* currentFormula = body[selectedFormula];
            orderedFormulas.push_back(selectedFormula);

            if(currentFormula->isLiteral() && !currentFormula->isBoundedLiteral(boundVars)){
                const aspc::Literal* literal = (const aspc::Literal*) currentFormula;
                std::vector<unsigned> boundIndices;
                for(unsigned k = 0; k<literal->getAriety(); k++){
                    if(!literal->isVariableTermAt(k) || boundVars.count(literal->getTermAt(k))){
                        boundIndices.push_back(k);
                    }
                }
                auxMapNameForPredicate[literal->getPredicateName()].insert(boundIndices);
                literal->addVariablesToSet(boundVars);
            }else{
                if(currentFormula->isBoundedValueAssignment(boundVars)){
                    const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) currentFormula;
                    boundVars.insert(ineq->getAssignedVariable(boundVars));
                }
            }
        }else if(notVisited){
            std::cout << "Error ordering rule: loop in formula selection"<<std::endl;
            exit(180);
        }
    }
    return orderedFormulas;
}
std::pair<std::vector<std::vector<unsigned>>,std::vector<std::unordered_map<unsigned,std::vector<unsigned>>>> DataStructureCompiler::declareGeneratorDataStructure(const aspc::Rule& rule,const std::set<std::string>& component){
    std::cout << "Declaring structure for ";rule.print();
    // general order + ordering starting from positive literal in the same component
    auto body = rule.getFormulas();
    std::vector<std::vector<unsigned>> orderByStarters;
    std::vector<std::unordered_map<unsigned,std::vector<unsigned>>> aggregateOrderingByStarter;

    for(unsigned starter = 0; starter <= body.size(); starter++){
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;
        orderByStarters.push_back({});
        aggregateOrderingByStarter.push_back({});
        if(starter < body.size()){
            //component empty means declare structure for rule propagators            
            const aspc::Formula* startingFormula = body[starter];
            if(!startingFormula->isLiteral() || (!component.empty() && !startingFormula->isPositiveLiteral())) continue;
            
            // starting formula is a positive literal
            const aspc::Literal* literal = (const aspc::Literal*) startingFormula;

            if(!component.empty() && !component.count(literal->getPredicateName())) continue;
            
            // same component 
            visitedFormulas[starter]=true;
            startingFormula->addVariablesToSet(boundVars);
        }
        auto orderedFormulas = reorderSimpleBody(rule.getFormulas(),boundVars,starter<body.size() ? starter: -1);
        for(unsigned i=0; i<body.size(); i++){
            if(body[i]->containsAggregate()){
                const aspc::ArithmeticRelationWithAggregate* aggrRelation = (const aspc::ArithmeticRelationWithAggregate*) body[i];
                std::vector<const aspc::Formula*> aggrBody;
                for(const aspc::Literal& l : aggrRelation->getAggregate().getAggregateLiterals()){
                    aggrBody.push_back(&l);
                    if(!component.empty() && component.count(l.getPredicateName())!=0) {std::cout << "ERROR: Recursive aggregate found in non ground program"<<std::endl; exit(180);}
                }
                for(const aspc::ArithmeticRelation& rel : aggrRelation->getAggregate().getAggregateInequalities()){
                    aggrBody.push_back(&rel);
                }
                auto orderedAggregate = reorderSimpleBody(aggrBody,boundVars);
                // TODO: Add ordering strategy for aggregates
                aggregateOrderingByStarter.back()[i]=orderedAggregate;
                orderedFormulas.push_back(i);
            }
        }
        orderByStarters[starter]=orderedFormulas;
    }   
    return std::make_pair(orderByStarters,aggregateOrderingByStarter);
}

