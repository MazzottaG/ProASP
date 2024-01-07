#include "DomainRuleCompiler.h"

void DomainRuleCompiler::printHeadDerivation(std::string tuplename){
    outfile << ind << "const auto& insertResult = "<<tuplename<<"->setStatus(True);\n";
    outfile << ind++ << "if(insertResult.second){\n";
        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList("<<tuplename<<"->getId());\n";
        outfile << ind << "AuxMapHandler::getInstance().initTuple("<<tuplename<<");\n";
        outfile << ind << "AuxMapHandler::getInstance().insertTrue(insertResult);\n";
        outfile << ind << "while ("<<tuplename<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
        outfile << ind << "domainAtoms.push_back(Glucose::mkLit("<<tuplename<<"->getId(),false));\n";
    outfile << --ind << "}\n";
    

}

