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
	r.rewriteAggregates();
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
	const aspc::Program* prgProp = &r.getPropagatorsProgram();
	const aspc::Program* prgGen = &r.getGeneratorProgram();
	const aspc::Program* prgLazy = &analyzer.getLazy();
	const aspc::Program* prgDatalog = &analyzer.getDatalog();
	std::unordered_map<std::string,std::string> predicateToStruct;
	std::unordered_map<std::string,unsigned> predicateToAggrIndex;
	std::unordered_map<std::string,std::string> aggrIdToAggrSet;
	for(unsigned ruleId = 0; ruleId<prgProp->getRulesSize(); ruleId++){
		const aspc::Rule* rule = &prgProp->getRule(ruleId);
		if(rule->containsAggregate() && rule->getArithmeticRelationsWithAggregate()[0].getAggregate().isSum()){
			const aspc::Atom* head = &rule->getHead()[0];
			const aspc::Literal* body = &rule->getArithmeticRelationsWithAggregate()[0].getAggregate().getAggregateLiterals()[0];
			std::string aggrIdTuple = head->getPredicateName();
			std::string aggrSetTuple = body->getPredicateName();
			for(unsigned k=0; k<head->getAriety(); k++){
				aggrIdTuple+="@"+head->getTermAt(k);
			}
			for(unsigned k=0; k<body->getAriety(); k++){
				aggrSetTuple+="@"+body->getTermAt(k);
			}

			aggrIdToAggrSet[aggrIdTuple]=aggrSetTuple;
		}
	}
	for(const aspc::Program* prg : {prgProp,prgGen,prgLazy,prgDatalog})
		for(unsigned ruleId = 0; ruleId<prg->getRulesSize(); ruleId++){
			const aspc::Rule* rule = &prg->getRule(ruleId);
			const std::vector<aspc::Atom>* head = &rule->getHead();
			for(unsigned id = 0; id<head->size(); id++){
				std::string predicate = head->at(id).getPredicateName();
				predicateToStruct.emplace(predicate,"Vec");
			}
			const std::vector<aspc::Literal>* body = &rule->getBodyLiterals();
			for(unsigned id = 0; id<body->size(); id++){
				std::string predicate = body->at(id).getPredicateName();
				predicateToStruct.emplace(predicate,"Vec");
			}
			const std::vector<aspc::ArithmeticRelationWithAggregate>* aggregates = &rule->getArithmeticRelationsWithAggregate();
			for(unsigned id = 0; id<aggregates->size(); id++){
				const aspc::ArithmeticRelationWithAggregate* aggregate = &aggregates->at(id);
				const std::vector<aspc::Literal>* aggregateBody = &aggregate->getAggregate().getAggregateLiterals();
				for(unsigned id1 = 0; id1<aggregateBody->size(); id1++){
					// WARNING: works with the assumption that only one literal appears in the aggregate body
					const aspc::Literal* lit = &aggregateBody->at(id1);
					std::string predicate = lit->getPredicateName();
					predicateToStruct[predicate]="Set";
					std::string aggrVar = aggregate->getAggregate().getAggregateVariables().at(0);
					for(unsigned k = 0; k < lit->getAriety();k++){
						if(lit->isVariableTermAt(k) && lit->getTermAt(k) == aggrVar){
							predicateToAggrIndex[predicate] = k;
							break;
						}
					}
				}
			}
		}
	std::cout << " %%%%%%%%%%%%%%% Pred to Struct %%%%%%%%%%%%%%% "<<std::endl;
	for(auto pair : predicateToStruct){
		std::cout << pair.first << " -> "<<pair.second<<std::endl;
	}
	std::cout << " %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% "<<std::endl;
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
	GeneratorCompiler datalogCompiler (analyzer.getDatalog(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"InstanceExpansion",true,"InstExp",false,predicateToStruct);
	datalogCompiler.compile();
	// GeneratorCompiler genCompiler (r.getGeneratorProgram(),executablePath,r.getPredicateNames(),r.getPredicateId(),&dc,true,originalPredicates,"Generator",false,"Comp",false);
	// genCompiler.compile();
	HybridGenerator genCompiler(r.getGeneratorProgram(), generatorRuleLabel, executablePath, r.getPredicateNames(), r.getPredicateId(), &dc,originalPredicates,predicateToStruct,predicateToAggrIndex,aggrIdToAggrSet);
	genCompiler.compile();
	GeneratorCompiler lazyCompiler (analyzer.getLazy(),executablePath,analyzer.getIdToPredicate(),analyzer.getPredicateToId(),&dc,true,originalPredicates,"ModelExpansion",true,"ModExp",true,predicateToStruct);
	lazyCompiler.compile();
	PropagatorCompiler propCompiler (r.getPropagatorsProgram(),executablePath,&dc,predicateToStruct);
	propCompiler.compile();
	dc.buildAuxMapHandler(executablePath,r.getPredicateNames(),predicateToStruct);
}