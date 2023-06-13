#include <iostream>
#include "antlr4-runtime.h"
#include "parser/ASPCore2Lexer.h"
#include "parser/ASPCore2Parser.h"
#include "parser/ASPCore2CompileProgramListener.h"
#include "compilers/GeneratorCompiler.h"
#include "compilers/PropagatorCompiler.h"
#include "datastructures/TupleFactory.h"
#include "rewriting/Rewriter.h"
#include "rewriting/Analyzer.h"
#include <fstream>
#include <climits>

int main(int argc, char *argv[])
{
	std::string filename(argv[1]);
	antlr4::ANTLRFileStream input;
	ASPCore2CompileProgramListener listener;
	input.loadFromFile(filename);
	ASPCore2Lexer lexer (&input);
	antlr4::CommonTokenStream tokens(&lexer);
	ASPCore2Parser parser (&tokens);
	parser.addParseListener(&listener);
	parser.program();
	Analyzer analyzer(listener.getProgram());
	
	std::unordered_set<std::string> originalPredicates;
	listener.getProgram().findPredicates(originalPredicates);
	Rewriter r(analyzer.getEager(),analyzer.getIdToPredicate(),analyzer.getPredicateToId());

	r.reduceToSigleHeadForPredicate();
	r.computeCompletion();
	r.computeGlobalPredicates();

	std::cout<<"Single Head For Predicate Program\n";
	std::cout<<"-----\n";
	r.getSingleHeadProgram().print();
	std::cout<<"-----\n";
	std::cout<<"Generator Program\n";
	std::cout<<"-----\n";
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
	GeneratorCompiler datalogCompiler (analyzer.getDatalog(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"InstanceExpansion",true,"InstExp",false);
	datalogCompiler.compile();
	GeneratorCompiler genCompiler (r.getGeneratorProgram(),executablePath,r.getPredicateNames(),r.getPredicateId(),&dc,true,originalPredicates,"Generator",false,"Comp",false);
	genCompiler.compile();
	GeneratorCompiler lazyCompiler (analyzer.getLazy(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"ModelExpansion",true,"ModExp",true);
	lazyCompiler.compile();
	PropagatorCompiler propCompiler (r.getPropagatorsProgram(),executablePath,&dc);
	propCompiler.compile();
	dc.buildAuxMapHandler(executablePath,r.getPredicateNames());
}