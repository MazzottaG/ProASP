#include <iostream>
#include "antlr4-runtime.h"
#include "parser/ASPCore2Lexer.h"
#include "parser/ASPCore2Parser.h"
#include "parser/ASPCore2CompileProgramListener.h"
#include "compilers/GeneratorCompiler.h"
#include "compilers/PropagatorCompiler.h"
#include "datastructures/TupleFactory.h"
#include "rewriting/Rewriter.h"
#include <fstream>
#include <climits>

int main(int argc, char *argv[])
{
	#ifdef COMPILE_GENERATOR
		std::string filename(argv[1]);
		antlr4::ANTLRFileStream input;
		ASPCore2CompileProgramListener listener;
		input.loadFromFile(filename);
		ASPCore2Lexer lexer (&input);
		antlr4::CommonTokenStream tokens(&lexer);
		ASPCore2Parser parser (&tokens);
		parser.addParseListener(&listener);
		parser.program();
		Rewriter r(listener.getProgram(),listener.getPredicateNames(),listener.getPredicateIds());
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
		GeneratorCompiler genCompiler (r.getGeneratorProgram(),executablePath,r.getPredicateNames(),r.getPredicateId(),&dc,listener.getProgram().isStratified());
		genCompiler.compile();
		PropagatorCompiler propCompiler (r.getPropagatorsProgram(),executablePath,r.getPropagatorRuleLabeling(),&dc);
		propCompiler.compile();
		dc.buildAuxMapHandler(executablePath,r.getPredicateNames());
	#endif
	#ifdef RUN_GENERATOR
		for(unsigned i=0;i<AuxMapHandler::getInstance().predicateCount();i++) 
			TupleFactory::getInstance().addPredicate();
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({1,2},AuxMapHandler::getInstance().get_e());
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({2,3},AuxMapHandler::getInstance().get_e());
			t->setStatus(True);
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({1,4},AuxMapHandler::getInstance().get_e());
			t->setStatus(True);
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({4,5},AuxMapHandler::getInstance().get_e());
			t->setStatus(True);
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({3,6},AuxMapHandler::getInstance().get_e());
			t->setStatus(True);
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		{
			TupleLight* t = TupleFactory::getInstance().addNewInternalTuple({5,6},AuxMapHandler::getInstance().get_e());
			t->setStatus(True);
			AuxMapHandler::getInstance().get_pe_()->insert2Vec(*t);
			AuxMapHandler::getInstance().get_pe_0_()->insert2Vec(*t);
		}
		Generator gen;
		gen.generate();
		Propagator prop;
		prop.propagateAtLevel0();
	#endif
}