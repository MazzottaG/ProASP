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
void DataStructureCompiler::buildAuxMapHandler(std::string executablePath,const std::vector<std::string>& predNames){
    Indentation ind(0);
    std::string executorPath = executablePath + "/../src/solver/AuxMapHandler.h";
    std::ofstream outfile(executorPath);
	if(!outfile.is_open()){
		std::cout << "Error unable to open AuxMapHandler file "<<executorPath<<std::endl;
		exit(180);
	} 
	outfile << ind << "#ifndef AUXMAPHANDLER_H\n";
    outfile << ind << "#define AUXMAPHANDLER_H\n";

    outfile << ind << "#include <vector>\n";
    outfile << ind << "#include \"../datastructures/TupleLight.h\"\n";
    outfile << ind << "#include \"../datastructures/AuxiliaryMapSmart.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";
    outfile << ind << "typedef std::vector<const Tuple* > Tuples;\n";
    
    outfile << ind++ << "class AuxMapHandler{\n";
        outfile << ind++ << "public:\n";
            outfile << ind++ << "static AuxMapHandler& getInstance(){\n";
                outfile << ind << "static AuxMapHandler instance;\n";
                outfile << ind << "return instance;\n";
            outfile << --ind << "}\n";
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE=indices.size()*CHAR_BIT*sizeof(int);
                    outfile << ind << "AuxMap<"<<BITSETSIZE<<">* get_u" << pair.first << "_";
                    for(unsigned k : indices) outfile << k << "_";
                    outfile << "(){return ";
                    outfile << "&u" << pair.first << "_";
                    for(unsigned k : indices) outfile << k << "_";
                    outfile<<";}"<<std::endl;
                }
            }
            for(std::string pred : predNames){
                outfile << ind << "int get_"<< pred << "()const { return _"<<pred<<";}\n";
            }
            outfile << ind << "std::string unmapPredicate(int predicateId)const {return predicateNames[predicateId];}\n";
            outfile << ind << "unsigned predicateCount()const {return predicateNames.size();}\n";
        ind--;
        outfile << ind++ << "private:\n";
            outfile << ind << "AuxMapHandler()";
            bool first=true;
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE = indices.size()*CHAR_BIT*sizeof(int);
                    outfile << (first ? ": " : ", ") << "u" << pair.first << "_";
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
            outfile << (first ? ": " : ", ") << "predicateNames({";
            first = true;
            for(const auto & pred : predNames){
                if(!first) outfile << ",";
                outfile << "\"" << pred << "\"";
                first=false;
            }
            outfile << "}){}\n";
            for(const std::pair<std::string,std::set<std::vector<unsigned>>>& pair : getAuxMapNameForPredicate()){
                for(const std::vector<unsigned>& indices : pair.second){
                    int BITSETSIZE=indices.size()*CHAR_BIT*sizeof(int);
                    outfile << ind << "AuxMap<"<<BITSETSIZE<<"> u" << pair.first << "_";
                    for(unsigned k : indices) outfile << k << "_";
                    outfile << ";"<<std::endl;
                }
            }
            for(unsigned k=0; k<predNames.size(); k++){
                outfile << ind << "int _"<<predNames[k] << " = " << k << ";\n";
            }
            outfile << ind << "std::vector<std::string> predicateNames;\n";
    ind--;
    outfile << --ind << "};\n";
    outfile << ind << "#endif\n";
    outfile.close();
}
std::pair<std::vector<std::vector<unsigned>>,std::vector<std::vector<unsigned>>> DataStructureCompiler::declarePropagatorDataStructure(const aspc::Rule& rule){
    std::cout << "Declaring structure for ";rule.print();
    
    // general order + ordering starting literal in the body + ordering from head atom
    auto body = rule.getFormulas();
    auto head = rule.getHead();
    std::vector<std::vector<unsigned>> orderByStartersHead;
    for(unsigned starter = 0; starter < head.size(); starter++){
        orderByStartersHead.push_back({});
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;

        aspc::Literal lit(false,head[starter]);
        lit.addVariablesToSet(boundVars);
        auxMapNameForPredicate[lit.getPredicateName()].insert({});

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
std::vector<std::vector<unsigned>> DataStructureCompiler::declareGeneratorDataStructure(const aspc::Rule& rule,const std::unordered_set<std::string>& component){
    std::cout << "Declaring structure for ";rule.print();
    // general order + ordering starting from positive literal in the same component
    auto body = rule.getFormulas();
    std::vector<std::vector<unsigned>> orderByStarters;
    for(unsigned starter = 0; starter <= body.size(); starter++){
        orderByStarters.push_back({});
        std::vector<bool> visitedFormulas(body.size(),false);
        std::unordered_set<std::string> boundVars;
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
    return orderByStarters;
}

