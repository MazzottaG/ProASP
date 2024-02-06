#include "ProgramReader.h"

ProgramReader::ProgramReader(int argc, char *argv[]){
    // True -> toGroundRule
	// False -> toCompileRule
	// std::vector<std::string> files({"encoding.compile","encoding.ground"});

	label = false;
	fullGrounding=true;
	unsigned programSize=0;
    for(int fileIndex = 1; fileIndex<3; fileIndex++){
    // for(int fileIndex = 0; fileIndex<2; fileIndex++){
		std::string filename(argv[fileIndex]);
		antlr4::ANTLRFileStream input;
		input.loadFromFile(filename);
		ASPCore2Lexer lexer (&input);
		antlr4::CommonTokenStream tokens(&lexer);
		ASPCore2Parser parser (&tokens);
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
	}
	listener.getProgram().findPredicates(originalPredicates);
	std::cout << "%%%%%%%%%%%%%%%%%%%%%% "<<(fullGrounding ? "Full Grounding ": "")<<"Input Program %%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    listener.getProgram().print();
	std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    rewriteRuleForComponent();
    std::cout << "%%%%%%%%%%%%%%%%%%%%%% "<<(fullGrounding ? "Full Grounding ": "")<<"Rewritten Input Program %%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
    for(unsigned ruleId = 0; ruleId<rewrittenProgram.getRulesSize();ruleId++){
        std::cout << (rewrittenRuleLabel[ruleId] ? "Ground " : "Compile ");
        rewrittenProgram.getRule(ruleId).print();
    }
    std::cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%" <<std::endl;
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
void ProgramReader::rewriteRuleForComponent(){
    aspc::Program inputProgram (listener.getProgram());
    dependencyManager.buildDependecyGraph(inputProgram);
    auto components = dependencyManager.getSCC();
    std::unordered_set<unsigned> remappedRule;
    for(int component_id = components.size()-1;component_id>=0;component_id--){
        std::cout << "Checking component:";
        for(int pred : components[component_id]) std::cout << " " << dependencyManager.getPredicateName(pred);
        std::cout << std::endl;
        bool rewrite = components[component_id].size() == 2;

        if(rewrite){
            std::string pred_1 = dependencyManager.getPredicateName(components[component_id][0]);
            std::string pred_2 = dependencyManager.getPredicateName(components[component_id][1]);
            auto rules_p1 = inputProgram.getRulesForPredicate(pred_1);
            auto rules_p2 = inputProgram.getRulesForPredicate(pred_2);
            if(rules_p1.size()!=1 || rules_p2.size()!=1)
                rewrite= false;
            else{
                const aspc::Rule* r_p1 = &inputProgram.getRule(rules_p1[0]);
                const aspc::Rule* r_p2 = &inputProgram.getRule(rules_p2[0]);

                if(r_p1->getHead()[0].getAriety() != r_p2->getHead()[0].getAriety())
                    rewrite=false;
                else if(r_p1->containsAggregate() || r_p2->containsAggregate())
                    rewrite=false;
                else if(r_p1->getFormulas().size() != r_p2->getFormulas().size())
                    rewrite=false;
                else{
                    std::vector<std::unordered_map<std::string,int>> predicate_occurrences;
                    for(const aspc::Rule* rule : {r_p1,r_p2}){
                        std::string searchPred = rule->getHead()[0].getPredicateName() == pred_1 ? pred_2 : pred_1;
                        int count = 0;
                        predicate_occurrences.push_back(std::unordered_map<std::string,int>());
                        for(const aspc::Literal& literal: rule->getBodyLiterals()){
                            if(literal.getPredicateName() == searchPred){
                                if(literal.isPositiveLiteral()) { rewrite = false; break;}
                                if(++count > 1) {rewrite = false; break;}
                            }
                            if(literal.getPredicateName() == pred_1 || literal.getPredicateName() == pred_2 || literal.isNegated())
                                continue;
                            auto it = predicate_occurrences.back().find(literal.getPredicateName());
                            if(it == predicate_occurrences.back().end())
                                predicate_occurrences.back()[literal.getPredicateName()]=1;
                            else
                                predicate_occurrences.back()[literal.getPredicateName()]=it->second+1;
                        }
                        if(!rewrite || count == 0){rewrite = false; break;}
                    }
                    for(unsigned i=0; i<predicate_occurrences.size() && rewrite; i++){
                        for(unsigned j=0; j<predicate_occurrences.size() && rewrite; j++) {
                            if(i!=j){
                                for(auto pair:predicate_occurrences[i])
                                    if(predicate_occurrences[j][pair.first]!=pair.second)
                                        rewrite = false;
                            }
                        }
                    }
                }
                if(rewrite){
                    auto pair = getVariableMapping(r_p1,r_p2);
                    if(pair.second){
                        if(r_p1->cloneWithRenamedVariables(pair.first).equalBodyExpect(*r_p2,{pred_1,pred_2})){
                            std::cout << "Variable renaming applied for:"<<std::endl;
                            std::cout << "   ";r_p1->print();
                            std::cout << "   ";r_p2->print();

                            std::vector<aspc::Literal> lits;
                            for(const aspc::Literal& lit : r_p2->getBodyLiterals()){
                                if(lit.getPredicateName() == pred_1 || lit.getPredicateName() == pred_2) continue;
                                lits.push_back(lit);
                            }
                            aspc::Literal not_head_r_p2 (true,r_p2->getHead()[0]);
                            aspc::Atom head_clone_r_p1 (pred_1,r_p2->getHead()[0].getTerms());

                            lits.push_back(not_head_r_p2);
                            aspc::Rule clone_r_p1({head_clone_r_p1},lits,r_p2->getArithmeticRelations(),false);
                            std::cout << "Otained rules:"<<std::endl;
                            std::cout << "   ";clone_r_p1.print();
                            std::cout << "   ";r_p2->print();
                            rewrittenProgram.addRule(clone_r_p1);
                            rewrittenRuleLabel.push_back(ruleLabel[rules_p1[0]]);
                            rewrittenProgram.addRule(*r_p2);
                            rewrittenRuleLabel.push_back(ruleLabel[rules_p2[0]]);
                            remappedRule.insert(rules_p1[0]);
                            remappedRule.insert(rules_p2[0]);
                        }
                    }else{
                        rewrite=false;
                    }
                }
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
            rewrittenRuleLabel.push_back(ruleLabel[ruleId]);
        }
    }
}
std::pair<std::unordered_map<std::string,std::string>,bool> ProgramReader::getVariableMapping(const aspc::Rule* r1,const aspc::Rule* r2)const{
    std::unordered_map<std::string,std::string> variableMapping;
    bool foundMapping = true;
    std::vector<std::unordered_map<std::string,std::multiset<int>>> ruleVariableMapping;
    std::unordered_set<std::string> component({r1->getHead()[0].getPredicateName(),r2->getHead()[0].getPredicateName()});

    std::unordered_map<std::string,int> indexMapping;
    std::vector<std::string> indices;

    std::string pred_prefix = "h_"+r1->getHead()[0].getPredicateName()+"_"+r2->getHead()[0].getPredicateName();
    for(const aspc::Rule* rule : {r1,r2}){
        ruleVariableMapping.push_back({});
        for(const aspc::Literal& literal : rule->getBodyLiterals()){
            if(!literal.isNegated()){
                for(unsigned k=0;k<literal.getAriety();k++){
                    if(literal.isVariableTermAt(k)){
                        std::string index = literal.getPredicateName()+"_"+std::to_string(k);
                        auto it = indexMapping.find(index);
                        int indexId=-1;
                        if(it == indexMapping.end()){
                            indexId=indices.size();
                            indexMapping[index]=indices.size();
                            indices.push_back(index);
                        }else indexId = it->second;

                        ruleVariableMapping.back()[literal.getTermAt(k)].insert(indexId);
                    }
                }
            }
        }
        aspc::Atom head_atom(rule->getHead()[0]);
        for(unsigned k=0;k<head_atom.getAriety();k++){
            if(head_atom.isVariableTermAt(k)){
                std::string index = pred_prefix+"_"+std::to_string(k);
                auto it = indexMapping.find(index);
                int indexId=-1;
                if(it == indexMapping.end()){
                    indexId=indices.size();
                    indexMapping[index]=indices.size();
                    indices.push_back(index);
                }else indexId = it->second;

                ruleVariableMapping.back()[head_atom.getTermAt(k)].insert(indexId);
            }
        }
        //std::cout << "Rule variable mapping computed"<<std::endl;
    }
    std::map<std::vector<int>,std::vector<std::vector<std::string>>> indicesToVariable;
    for(unsigned rule_index = 0; rule_index<ruleVariableMapping.size(); rule_index++){
        /*std::cout << "rule "<<rule_index<<" ";
        if(rule_index == 0) r1->print();
        else r2->print();*/

        for(auto pair : ruleVariableMapping[rule_index]){
            std::string variable = pair.first;
            std::vector<int> foundIndices(pair.second.begin(),pair.second.end());
            /*std::cout << "  "<<variable << "-> {";
            for(int i: foundIndices) std::cout << " "<<indices[i];
            std::cout << "}\n";*/
            auto it = indicesToVariable.find(foundIndices);
            if(it == indicesToVariable.end()){
                indicesToVariable[foundIndices]=std::vector<std::vector<std::string>>({{},{}});
            }
            indicesToVariable[foundIndices][rule_index].push_back(variable);
        }
    }
    for(auto pair: indicesToVariable){
        if(pair.second[0].size()!=1 || pair.second[1].size()!=1){
            return std::make_pair(variableMapping,false);
        }
        variableMapping[pair.second[0][0]]=pair.second[1][0];
        /*
        std::cout << "      {";
        for(int i : pair.first) std::cout << " " << indices[i];
        std::cout << "} -> [";
        for(int i=0;i<pair.second.size();i++){
            if(i>0) std::cout << ", ";
            std::cout << "[";
            for(int j=0;j<pair.second[i].size();j++){
                if(j>0) std::cout << ", ";
                std::cout << pair.second[i][j];
            }
            std::cout << "]";
        }
        std::cout << "]"<<std::endl;
        */

    }
    return std::make_pair(variableMapping,true);
}