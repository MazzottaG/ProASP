#include <iostream>
#include "compilers/ProgramReader.h"
#include "compilers/GeneratorCompiler.h"
#include "compilers/HybridGenerator.h"
#include "compilers/PropagatorCompiler.h"
#include "datastructures/TupleFactory.h"
#include "rewriting/Rewriter.h"
#include "rewriting/Analyzer.h"
#include <fstream>
#include <climits>

int main(int argc, char *argv[])
{
	ProgramReader reader(argc,argv);
	Analyzer analyzer(reader.getInputProgram(),reader.getInputProgramLabel());

	aspc::Program eagerProgram(analyzer.getEager());
	std::vector<bool> eagerLabels(analyzer.getEagerLabel());
	std::vector<std::string> idToPredicate(analyzer.getIdToPredicate());
	std::unordered_map<std::string,unsigned> predicateToId(analyzer.getPredicateToId());

	reader.labelHybridRule(eagerProgram,eagerLabels,idToPredicate,predicateToId);
	int rulesSize=eagerProgram.getRulesSize();
	aspc::Program propagatorProgram;
	for(int ruleId=0; ruleId<rulesSize; ruleId++){
		if(!eagerLabels[ruleId])
			propagatorProgram.addRule(eagerProgram.getRule(ruleId));
	}
	Rewriter r(propagatorProgram,idToPredicate,predicateToId);
	
	r.reduceToSigleHeadForPredicate();
	r.computeCompletion();
	r.computeGlobalPredicates();

	std::cout<<"Single Head For Predicate Program\n";
	std::cout<<"-----\n";
	r.getSingleHeadProgram().print();
	std::cout<<"-----\n";
	std::cout<<"Generator Program\n";
	std::cout<<"-----\n";
	std::vector<bool> generatorRuleLabel(r.getGeneratorProgram().getRulesSize(),false);
	for(int ruleId=0; ruleId<eagerProgram.getRulesSize(); ruleId++){
		if(eagerLabels[ruleId]){
			r.addToGroundRule(eagerProgram.getRule(ruleId));
			generatorRuleLabel.push_back(true);
		}

	}
	r.getGeneratorProgram().print();
	std::cout<<"-----\n";
	std::cout<<"Propagator Program\n";
	std::cout<<"-----\n";
	r.getPropagatorsProgram().print();
	std::cout<<"-----\n";
	std::cout<<"Builder finished\n";
	std::string executablePathAndName = argv[0];
	std::string executablePath = executablePathAndName;
	for (int i = executablePath.size() - 1; i >= 0; i--) {
		if (executablePath[i] == '/') {
			executablePath = executablePath.substr(0, i);
			break;
		}
	}
	DataStructureCompiler dc;
	std::unordered_set<std::string> originalPredicates(reader.getOriginalPredicates());
	GeneratorCompiler datalogCompiler (analyzer.getDatalog(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"InstanceExpansion",true,"InstExp",false);
	datalogCompiler.compile();
	// GeneratorCompiler genCompiler (r.getGeneratorProgram(),executablePath,r.getPredicateNames(),r.getPredicateId(),&dc,true,originalPredicates,"Generator",false,"Comp",false);
	// genCompiler.compile();
	HybridGenerator genCompiler(r.getGeneratorProgram(), generatorRuleLabel, executablePath, r.getPredicateNames(), r.getPredicateId(), &dc,originalPredicates);
	genCompiler.compile();
	GeneratorCompiler lazyCompiler (analyzer.getLazy(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"ModelExpansion",true,"ModExp",true);
	lazyCompiler.compile();
	PropagatorCompiler propCompiler (r.getPropagatorsProgram(),executablePath,&dc);
	propCompiler.compile();
	dc.buildAuxMapHandler(executablePath,r.getPredicateNames());
}