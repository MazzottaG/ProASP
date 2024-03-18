#include "LazyPropagatorCompiler.h"

LazyPropagatorCompiler::LazyPropagatorCompiler(const aspc::Program& program, std::string& execPath, DataStructureCompiler* dc, const std::unordered_map<std::string, std::string>& predToStruct): program(program), execPath(execPath), auxMapCompiler(dc), predicateToStruct(predToStruct), ind(Indentation(0)){
    depManager.buildDependecyGraph(program);
}

void LazyPropagatorCompiler::compile(){
    std::cout <<"Lazy compiler called\n";
    std::vector<std::vector<int>> sccs = depManager.getSCC();

    for(int i = sccs.size() -1; i >= 0; --i){
        compileSCC(sccs[i], i);
        std::cout <<"Compiling SCC with lazy propagators\n";
    }
    compileConstraints();
}

void LazyPropagatorCompiler::compileSCC(std::vector<int> scc, unsigned index){
    openPropagatorFile(true, index);
    closePropagatorFile();
}

void LazyPropagatorCompiler::compileConstraints(){
    unsigned index = 0;
    for(const aspc::Rule& r: program.getRules()){
        if(r.isConstraint()){ 
            std::cout <<"Compiling Constraint with lazy propagators\n";
            openPropagatorFile(false, index);
            closePropagatorFile();
            index++;

        }
    }
}


void LazyPropagatorCompiler::openPropagatorFile(bool component, unsigned id){

    ind = Indentation(0);//Indentation ind(0);
    std::string prefix = component ? "Comp" : "Rule_Lazy";
    std::string className = prefix +"_"+std::to_string(id)+"_Propagator";
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
    // outfile << ind << "#include \"../../core/Solver.h\"\n";
    outfile << ind << "typedef TupleLight Tuple;\n";
    outfile << ind << "template<size_t S>\n";
    outfile << ind << "using AuxMap = AuxiliaryMapSmart<S> ;\n";

    outfile << ind++ << "class "<<className<<": public AbstractPropagator{\n";
        outfile << ind << "std::vector<int> tuplesEmpty;\n";
        outfile << ind << "IndexedSet tuplesSetEmpty;\n";
        outfile << ind++ << "public:\n";
        outfile << ind << className << "(){}\n";
            //compileRuleLevelZero(ruleId,outfile,ind);
            //compileRuleFromStarter(ruleId,outfile,ind);
            //compileRuleWatcher(ruleId,outfile,ind);
}

void LazyPropagatorCompiler::closePropagatorFile(){
    --ind;
    outfile << --ind << "};\n";
    outfile << ind << "#endif\n";
}

// void LazyPropagatorCompiler::computePropagatorOrder(){
//     std::vector<std::vector<int>> sccs = depManager.getSCC();

// }