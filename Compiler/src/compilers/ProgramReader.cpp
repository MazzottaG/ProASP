#include "ProgramReader.h"

ProgramReader::ProgramReader(int argc, char *argv[]){
    // True -> toGroundRule
	// False -> toCompileRule
	
	label = false;
	unsigned programSize=0;
	for(int fileIndex = 1; fileIndex<3; fileIndex++){
		std::string filename(argv[fileIndex]);
		antlr4::ANTLRFileStream input;
		input.loadFromFile(filename);
		ASPCore2Lexer lexer (&input);
		antlr4::CommonTokenStream tokens(&lexer);
		ASPCore2Parser parser (&tokens);
		parser.addParseListener(&listener);
		parser.program();
		for(int i=programSize; i<listener.getProgram().getRulesSize(); i++){
			ruleLabel.push_back(label);
			if(listener.getProgram().getRule(i).isConstraint()) continue;

			for(aspc::Atom h : listener.getProgram().getRule(i).getHead()){
				if(label)
					toGroundPredicates.insert(h.getPredicateName());
				else propagatorPredicates.insert(h.getPredicateName());
			}
			if(label && listener.getProgram().getRule(i).containsAggregate()){
				std::cout << "Rules with aggregates cannot be grounded yet. Coming soon ..."<<std::endl;
				exit(180);
			}
		}
		programSize=listener.getProgram().getRulesSize();
		label=!label;
	}
	listener.getProgram().findPredicates(originalPredicates);
	std::cout << "%%%%%%%%%%%%%%%%%%%%%% Input Program %%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    listener.getProgram().print();
	std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
}

void ProgramReader::labelHybridRule(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId){
    for(std::string predicate : toGroundPredicates){
		if(propagatorPredicates.count(predicate)){
			int i=0;
			while(predicateToId.count(predicate+"_"+std::to_string(i))) i++;
			remapped_predicates.insert({predicate,predicate+"_"+std::to_string(i)});
			predicateToId[predicate+"_"+std::to_string(i)]=idToPredicate.size();
			idToPredicate.push_back(predicate+"_"+std::to_string(i));
		}
	}
	rewriteGroundingPredicate(program,currenLabel,idToPredicate,predicateToId);
	for(auto pair : remapped){
		std::vector<std::string> terms;
        for(int i=0;i<pair.second;i++)
            terms.push_back("X"+std::to_string(i));
        aspc::Rule rule(std::vector<aspc::Atom>({aspc::Atom(pair.first,terms)}),std::vector<aspc::Literal>({aspc::Literal(false,aspc::Atom(remapped_predicates[pair.first],terms))}),{},false);
        program.addRule(rule);
        currenLabel.push_back(true);
	}
}

void ProgramReader::rewriteGroundingPredicate(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPredicate,std::unordered_map<std::string,unsigned>& predicateToId){
    // rules not labeled as toGround should be rewritten
    for(auto pair : remapped_predicates){
        int ariety = -1;
        // std::cout << "Remapping "<<pair.first<<std::endl;
        for(int ruleId=0;ruleId<program.getRulesSize();ruleId++){
        if(!currenLabel[ruleId] && !program.getRule(ruleId).isConstraint()){
            // std::cout << "   Considering rule ";program.getRule(ruleId).print();
            int termsSize = program.rewriteHead(pair.first,ruleId,remapped_predicates);
            if(termsSize >=0){
            ariety=termsSize;
            // std::cout << "      Found ariety "<<termsSize<<std::endl;
            }
            
        }
        }
        // std::cout << pair.first << " remapped to "<<pair.second<<" ariety "<<ariety<<std::endl;
        if(ariety>=0){
            remapped.push_back({pair.first,ariety});
        }
    }
}

