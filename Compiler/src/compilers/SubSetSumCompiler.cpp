#include "SubSetSumRuleCompiler.h"

void SubSetSumRuleCompiler::compileNoStarter(bool recursive){
    assert(!recursive);
    const aspc::Atom* head = &rule->getHead()[0];
    const aspc::Literal* aggregateSet = &rule->getBodyLiterals()[0];
    std::vector<std::string> shared(head->getTerms());
    std::string resultVar = shared.back();
    shared.pop_back();

    const aspc::ArithmeticRelation* var_function = &rule->getArithmeticRelations()[0];
    bool isCount = var_function->getRight().getTerm1() == "count";
    std::string aggrVar = var_function->getLeft().getTerm1();

    std::cout << "Compiling generator for SubSetSumRule "; rule->print();
    std::cout << "   SharedVars:";
    for(std::string v:shared) std::cout << " "<<v;
    std::cout << std::endl;
    std::cout << "   Aggregate Variable: "<<aggrVar<<std::endl;
    std::cout << "   Aggregate Function: "<<(isCount ? "#count": "#sum")<<std::endl;

    outfile << ind << "//starting subsetsum generation\n";
    outfile << ind << "IndexedSet* aggSetTuples = &AuxMapHandler::getInstance().get_p"<<aggregateSet->getPredicateName()<<"_()->getValuesSet({});\n";
    outfile << ind << "IndexedSet* aggSetTuplesU = &AuxMapHandler::getInstance().get_u"<<aggregateSet->getPredicateName()<<"_()->getValuesSet({});\n";
    usedAuxMap[aggregateSet->getPredicateName()].insert({});

    std::unordered_set<std::string> boundVars;
    unsigned closingPars=0;
    outfile << ind++ << "for(auto it = aggSetTuples->begin(); ; it++){\n";
        outfile << ind << "if(it == aggSetTuples->end()) it = aggSetTuplesU->begin();\n";
        outfile << ind << "if(it == aggSetTuplesU->end()) break;\n";
        outfile << ind << "Tuple* aggSet = TupleFactory::getInstance().getTupleFromInternalID(*it);\n";
        for(unsigned i=0; i<aggregateSet->getAriety(); i++){
            if(!aggregateSet->isVariableTermAt(i) || boundVars.count(aggregateSet->getTermAt(i))){
                outfile << ind++ << "if(aggSet->at("<<i<<") == "<<aggregateSet->getTermAt(i)<<"){\n";
                closingPars++;
            }else{
                outfile << ind << "int " << aggregateSet->getTermAt(i) << " = aggSet->at("<<i<<");\n";
                boundVars.insert(aggregateSet->getTermAt(i));
            }
        }
        std::vector<unsigned> boundIndices;
        std::string key = "";
        outfile << ind << "std::vector<int>* actualSums = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_";
            for(unsigned j = 0; j<shared.size(); j++){
                if(j>0) key += ",";
                key += shared[j];
                outfile << j <<"_"; 
                boundIndices.push_back(j);
            }
        outfile << "()->getValuesVec({"<<key<<"});\n";
        usedAuxMap[head->getPredicateName()].insert(boundIndices); 

        outfile << ind++ << "if(actualSums->size() == 0){\n";  
            outfile << ind << "Tuple* zeroSum = TupleFactory::getInstance().addNewInternalTuple({"<<key<<(key != "" ? "," : "")<<"0},AuxMapHandler::getInstance().get_"<<head->getPredicateName()<<"(),true);\n";
            outfile << ind << "auto initResult = zeroSum->setStatus(True);\n";
            outfile << ind++ << "if(initResult.second){\n";
                outfile << ind << "AuxMapHandler::getInstance().initTuple(zeroSum);\n";
                outfile << ind << "AuxMapHandler::getInstance().insertTrue(initResult);\n";
                outfile << ind << "while (zeroSum->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                outfile << ind << "domainAtoms.push_back(Glucose::mkLit(zeroSum->getId(),false));\n";
            outfile << --ind << "}\n";
            outfile << ind << "int initVal = "<<(isCount ? "1": aggrVar)<<";\n";
            outfile << ind << "Tuple* sum = TupleFactory::getInstance().addNewInternalTuple({"<<key<<(key != "" ? "," : "")<<"initVal},AuxMapHandler::getInstance().get_"<<head->getPredicateName()<<"(),true);\n";
            outfile << ind << "auto insertResult = sum->setStatus(True);\n";
            outfile << ind++ << "if(insertResult.second){\n";
                outfile << ind << "AuxMapHandler::getInstance().initTuple(sum);\n";
                outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
                outfile << ind << "while (sum->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                outfile << ind << "domainAtoms.push_back(Glucose::mkLit(sum->getId(),false));\n";
            outfile << --ind << "}\n";   
        outfile << --ind << "}else{\n"; 
        if(!isCount){
            outfile << ++ind << "std::vector<Tuple*> newSums;\n";
            outfile << ind++ << "for(unsigned i=0;i<actualSums->size();i++){\n";   
                outfile << ind << "int sumValue = TupleFactory::getInstance().getTupleFromInternalID(actualSums->at(i))->at("<<shared.size()<<");\n";
                outfile << ind << "Tuple* sum = TupleFactory::getInstance().addNewInternalTuple({"<<key<<(key != "" ? "," : "")<<"sumValue+"<<aggrVar<<"},AuxMapHandler::getInstance().get_"<<head->getPredicateName()<<"(),true);\n";
                outfile << ind << "auto insertResult = sum->setStatus(True);\n";
                outfile << ind++ << "if(insertResult.second){\n";
                    outfile << ind << "newSums.push_back(sum);\n";
                outfile << --ind << "}\n";   
            outfile << --ind << "}\n";  
            outfile << ind++ << "for(Tuple* sum : newSums){\n";
                outfile << ind << "AuxMapHandler::getInstance().initTuple(sum);\n";
                outfile << ind << "AuxMapHandler::getInstance().insertTrue(std::make_pair(sum,true));\n";
                outfile << ind << "while (sum->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                outfile << ind << "domainAtoms.push_back(Glucose::mkLit(sum->getId(),false));\n";
            outfile << --ind << "}\n";
        }else{
            outfile << ++ind << "int actualCount = actualSums->size();\n";
            outfile << ind << "Tuple* sum = TupleFactory::getInstance().addNewInternalTuple({"<<key<<(key != "" ? "," : "")<<"actualCount},AuxMapHandler::getInstance().get_"<<head->getPredicateName()<<"(),true);\n";
            outfile << ind << "auto insertResult = sum->setStatus(True);\n";
            outfile << ind++ << "if(insertResult.second){\n";
                outfile << ind << "AuxMapHandler::getInstance().initTuple(sum);\n";
                outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
                outfile << ind << "while (sum->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                outfile << ind << "domainAtoms.push_back(Glucose::mkLit(sum->getId(),false));\n";
            outfile << --ind << "}\n";   
        }
        outfile << --ind << "}\n";
          
    while (closingPars>0){
        closingPars--;
        outfile << --ind << "}\n";
    }
    outfile << --ind << "}\n";
//    outfile << ind << "std::vector<int>* generatedSums = &AuxMapHandler::getInstance().get_p"<<head->getPredicateName()<<"_()->getValuesVec({});\n";
//    usedAuxMap[head->getPredicateName()].insert({});
//    outfile << ind++ << "for(unsigned i=0;i<generatedSums->size();i++){\n";
//        outfile << ind << "AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(generatedSums->at(i)));\n";
//    outfile << --ind << "}\n";

}

