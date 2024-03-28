#include "ProgramReader.h"

ProgramReader::ProgramReader(int argc, char *argv[]){
    // True -> toGroundRule
	// False -> toCompileRule
	// std::vector<std::string> files({"encoding.compile","encoding.ground"});

	label = false;
	fullGrounding=true;
	unsigned programSize=0;
    for(int fileIndex = 1; fileIndex<4; fileIndex++){
    // for(int fileIndex = 0; fileIndex<2; fileIndex++){
        std::string filename(argv[fileIndex]);
        antlr4::ANTLRFileStream input;
        input.loadFromFile(filename);
        ASPCore2Lexer lexer (&input);
        antlr4::CommonTokenStream tokens(&lexer);
        ASPCore2Parser parser (&tokens);
        if (fileIndex < 3){
            parser.addParseListener(&listener);
            parser.program();
            for(unsigned i=programSize; i<listener.getProgram().getRulesSize(); i++){
                if(!label) fullGrounding=false;
                ruleLabel.push_back(label);
                
                if(listener.getProgram().getRule(i).isConstraint()) continue;
                for(aspc::Atom h : listener.getProgram().getRule(i).getHead()){
                    if(label)
                        toGroundPredicates.insert(h.getPredicateName());
                    else propagatorPredicates.insert(h.getPredicateName());
                }
                
            }
            programSize=listener.getProgram().getRulesSize();
            label=!label;
        }else{
            parser.addParseListener(&specialListener);
            parser.program();
        }
	}
	listener.getProgram().findPredicates(originalPredicates);
    posCycleProgram = &specialListener.getProgram();
    //add also predicates of pos cycle program to original predicates so that theyn will 
    //be printed in the answer sets
    posCycleProgram->findPredicates(originalPredicates);
    if(posCyclePredsDefinedInProgram(listener.getProgram(), *posCycleProgram)){
        std::cout << "Predicated defined inside positive cycle program cannot be defined inside to-generate or to-compile program\n";
        exit(1);
    }
    //call rewriting and marking of rules
	std::cout << "%%%%%%%%%%%%%%%%%%%%%% "<<(fullGrounding ? "Full Grounding ": "")<<"Input Program %%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    listener.getProgram().print();
    std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    rewriteRuleForComponent(posCycleProgram->getHeadPredicates());
    std::cout << "%%%%%%%%%%%%%%%%%%%%%% "<<(fullGrounding ? "Full Grounding ": "")<<"Rewritten Input Program %%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    for(unsigned ruleId = 0; ruleId<rewrittenProgram.getRulesSize();ruleId++){
        std::cout << (rewrittenRuleLabel[ruleId] ? "Ground " : "Compile ");
        rewrittenProgram.getRule(ruleId).print();
    }
    std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    
    posCycleRewriter.rewrite(posCycleProgram, &constraintsPosP);
    //posCycleRewriter.re
    //check that constraints inside to-compile and to-ground program do not contain in the body
    //literals belonging to two distinct components of the scc of pos-cycle program
	posCycleRewriter.crossComponentPredicatesAppearInConstraintForProgram(getInputProgram());
    //mergePosCycleProgramAndInputProgram(posCycleRewriter.getGeneratorProgram()); 
    posCyclePropagatorProgram = &posCycleRewriter.getPropagatorProgram();
}

void ProgramReader::mergePosCycleProgramAndInputProgram(const aspc::Program& genProgramPosCycle){
    //add generator rules and constraints of PosCycleProgram to inputProgram(which is intended to be the rewritten program)
    for(const aspc::Rule& rule : genProgramPosCycle.getRules()){
        rewrittenProgram.addRule(rule);
        //consider all rules of posCycleProgram as to compile
        rewrittenRuleLabel.push_back(false);
    }
}

bool ProgramReader::posCyclePredsDefinedInProgram(const aspc::Program& program, const aspc::Program& posCycleProgram){
    for(const std::string& posCycleHeadPredicate : posCycleProgram.getHeadPredicates()){
        const std::set<std::string>& programHeadPredicates = program.getHeadPredicates();
        if(std::find(programHeadPredicates.begin(), programHeadPredicates.end(), posCycleHeadPredicate) != programHeadPredicates.end()){
            return true;
        }
    }
    return false;
}

void ProgramReader::labelHybridRule(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& idToPred,std::unordered_map<std::string,unsigned>& predToId){
    for(std::string predicate : toGroundPredicates){
		if(propagatorPredicates.count(predicate)){
			int i=0;
			while(predToId.count(predicate+"__"+std::to_string(i))) i++;
			remapped_predicates.insert({predicate,predicate+"__"+std::to_string(i)});
            predToId[predicate+"__"+std::to_string(i)]=idToPred.size();
            idToPred.push_back(predicate+"__"+std::to_string(i));
		}
	}
	rewriteGroundingPredicate(program,currenLabel,idToPred,predToId);
	for(auto pair : remapped){
		std::vector<std::string> terms;
        for(int i=0;i<pair.second;i++)
            terms.push_back("X"+std::to_string(i));
        aspc::Rule rule(std::vector<aspc::Atom>({aspc::Atom(pair.first,terms)}),std::vector<aspc::Literal>({aspc::Literal(false,aspc::Atom(remapped_predicates[pair.first],terms))}),{},false);
        program.addRule(rule);
        currenLabel.push_back(true);
	}
}

void ProgramReader::rewriteGroundingPredicate(aspc::Program& program, std::vector<bool>& currenLabel,std::vector<std::string>& ,std::unordered_map<std::string,unsigned>& ){
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
void ProgramReader::rewriteRuleForComponent(std::set<std::string> predsDefInPosProgram){
    aspc::Program inputProgram (listener.getProgram());
    dependencyManager.buildDependecyGraph(inputProgram);
    auto components = dependencyManager.getSCC();
    std::unordered_set<unsigned> remappedRule;
    for(int component_id = components.size()-1;component_id>=0;component_id--){
        auto pair = dependencyManager.checkComponent(inputProgram,component_id);

        if(pair.second) {
            for(auto ruleData : pair.first) {
                rewrittenProgram.addRule(ruleData.first);
                rewrittenRuleLabel.push_back(ruleLabel[ruleData.second]);
                remappedRule.insert(ruleData.second);
            }
        }
    }
    bool first=true;
    for(unsigned  ruleId = 0; ruleId < inputProgram.getRulesSize(); ruleId++){
        const aspc::Rule* r = &inputProgram.getRule((ruleId));
        if(r->isConstraint() || !remappedRule.count(ruleId)){
            if(first)
                std::cout << "No variable renaming applied for:"<<std::endl;
            first= false;
            std::cout << "   ";
            r->print();
            rewrittenProgram.addRule(*r);
            //if constraint contains predicates defined in positive program, then it must be compiled(cannot be grounded)
            bool mustCompile=false;
            if(r->isConstraint()){
                for(const aspc::Literal& lit : r->getBodyLiterals()){
                    if(predsDefInPosProgram.count(lit.getPredicateName())){
                        mustCompile = true;
                    }
                }
            }
            if(mustCompile){
                rewrittenRuleLabel.push_back(false);
                //add constraints from to-compile and to-ground such that 
                //PosCycleRewriter can create generator rules from constraints 
                constraintsPosP.addRule(*r);
            }
            else
                rewrittenRuleLabel.push_back(ruleLabel[ruleId]);
        }
    }
}
