#include "ChoiceRewriter.h"

std::string ChoiceRewriter::CHOICE_SET_ATOM_NAME = "ChSet_";
std::string ChoiceRewriter::GENERIC_VARIABLE_NAME = "V_";
std::string ChoiceRewriter::CHOICE_OPTION_SPECIFIER = "--choice";
std::string ChoiceRewriter::CHOICE_OPTION_REWRITE = "--choice-rewrite";
std::string ChoiceRewriter::NEG_PREDICATE_PREFIX = "N_";
// std::unordered_map<std::string, CompileChoiceOption> ChoiceRewriter::CHOICE_COMPILE_OPTIONS = {{"ground_normals", CompileChoiceOption::GROUND_NORMALS}, {"ground_constraints", CompileChoiceOption::GROUND_CONSTRAINTS}, {"compile_constraints", CompileChoiceOption::COMPILE_CONSTRAINTS}, {"compile_normals", CompileChoiceOption::COMPILE_NORMALS}};

std::unordered_map<std::string, CompileChoiceOption> ChoiceRewriter::CHOICE_COMPILE_OPTIONS = {{"compile_all", CompileChoiceOption::COMPILE_ALL}, {"compile_normals", CompileChoiceOption::COMPILE_NORMALS}, {"compile_constraints", CompileChoiceOption::COMPILE_CONSTRAINTS}, {"ground_all", CompileChoiceOption::GROUND_ALL}};

ChoiceRewriter::ChoiceRewriter(){
    newFirstRuleIndex = 0;
    newFirstChoiceRuleIndex = 0;

}

void ChoiceRewriter::setCompileChoiceOption(CompileChoiceOption option){
    compileChoiceOption = option;
}

void ChoiceRewriter::setRewriteOption(bool rewrite){
    removeChoices = rewrite;
}

CompileChoiceOption ChoiceRewriter::getCompileChoiceOption() const{
    return compileChoiceOption;
}

bool ChoiceRewriter::toGroundNormalRules(bool currentProgramLabel) const{
    // if(compileChoiceOption == CompileChoiceOption::NO_OPTION || compileChoiceOption == CompileChoiceOption::GROUND_CONSTRAINTS || compileChoiceOption == CompileChoiceOption::COMPILE_CONSTRAINTS)
    //     return currentProgramLabel;
    // else if(compileChoiceOption == CompileChoiceOption::GROUND_NORMALS)
    //     return true;
    // else if(compileChoiceOption == CompileChoiceOption::COMPILE_NORMALS)
    //     return false;
    // assert(false);
    if(compileChoiceOption == CompileChoiceOption::NO_OPTION)
        return currentProgramLabel;
    else if(compileChoiceOption == CompileChoiceOption::COMPILE_NORMALS || compileChoiceOption == CompileChoiceOption::COMPILE_ALL)
        return false;
    else
        return true;
}

bool ChoiceRewriter::toGroundChoiceConstraints(bool currentProgramLabel) const{
    // if(compileChoiceOption == CompileChoiceOption::NO_OPTION || compileChoiceOption == CompileChoiceOption::GROUND_NORMALS || compileChoiceOption == CompileChoiceOption::COMPILE_NORMALS)
    //     return currentProgramLabel;
    // else if(compileChoiceOption == CompileChoiceOption::GROUND_CONSTRAINTS)
    //     return true;
    // else if(compileChoiceOption == CompileChoiceOption::COMPILE_CONSTRAINTS)
    //     return false;
    // assert(false);
    if(compileChoiceOption == CompileChoiceOption::NO_OPTION)
        return currentProgramLabel;
    else if(compileChoiceOption == CompileChoiceOption::COMPILE_CONSTRAINTS || compileChoiceOption == CompileChoiceOption::COMPILE_ALL)
        return false;
    else
        return true;
}

void ChoiceRewriter::rewriteChoiceRules(const aspc::Program& program, bool toGround){
    //copy predicates defined in choice even though the new prorgam does not contain choices
    //used for labelling
    for(auto pred : program.getPredicatesDefinedInChoices()){
        rewrittenProgram.addPredicateDefinedInChoiceRule(pred);
    }

    for(unsigned i = newFirstRuleIndex; i < program.getRulesSize(); ++i){
        const aspc::Rule& rule = program.getRule(i);
        rewrittenProgram.addRule(rule);
        ruleLabels.push_back(toGround);
    }

    for(unsigned i = newFirstChoiceRuleIndex; i < program.getChoiceRulesSize(); ++i){
        const aspc::ChoiceRule& rule = program.getChoiceRule(i);
        //rewrite
        std::cout << "Rewriting choice rule: ";
        rule.print();

        //find all literals in body
        std::vector<aspc::Literal> bodyLits;
        for(const aspc::Literal& lit : rule.getBodyLiterals())
            bodyLits.push_back(lit);

        //find all arithmetic relations in body
        std::vector<aspc::ArithmeticRelation> bodyRels;
        for(const aspc::ArithmeticRelation& rel : rule.getArithmeticRelations())
            bodyRels.push_back(rel);

        //find all literals and arithmetic relations for each choiceElement
        //body lits and body rels for rules after rewriting will be
        //the union of those in the body of the coice and the ones in the body of the choice element
        std::vector<std::vector<aspc::ArithmeticRelation>> bodyRelsByElement;
        std::vector<std::vector<aspc::Literal>> bodyLitsByElement;
        //find what are the predicates in the heads of the choice
        std::unordered_set<std::string> predicatesInChoiceHead;
        for(unsigned j = 0; j < rule.getHead().size(); ++j){
            const aspc::ChoiceElement& elem = rule.getHead().at(j);
            predicatesInChoiceHead.insert(rule.getHead().at(j).getAtom().getPredicateName());
            bodyRelsByElement.push_back(std::vector<aspc::ArithmeticRelation>(bodyRels.begin(), bodyRels.end()));
            bodyLitsByElement.push_back(std::vector<aspc::Literal>(bodyLits.begin(), bodyLits.end()));

            for(const aspc::Literal& lit : elem.getBodyLiterals()){
                bodyLitsByElement.at(j).push_back(lit);
            }
            for(const aspc::ArithmeticRelation& rel : elem.getArithmeticRelations())
                bodyRelsByElement.at(j).push_back(rel);
            //add normal rule for choice
            if(removeChoices){
                aspc::Atom headAtom1 = aspc::Atom(elem.getAtom().getPredicateName(), elem.getAtom().getTerms());
                aspc::Literal negBodyLit1 = aspc::Literal(true, aspc::Atom(NEG_PREDICATE_PREFIX + elem.getAtom().getPredicateName(), elem.getAtom().getTerms()));
                std::vector<aspc::Literal> currentBodyLits1 = std::vector<aspc::Literal>(bodyLitsByElement.back().begin(), bodyLitsByElement.back().end());
                currentBodyLits1.push_back(negBodyLit1);
                rewrittenProgram.addRule(aspc::Rule({headAtom1}, currentBodyLits1, bodyRelsByElement.back(), true));
                ruleLabels.push_back(toGroundNormalRules(toGround));

                aspc::Atom headAtom2 = aspc::Atom(NEG_PREDICATE_PREFIX + elem.getAtom().getPredicateName(), elem.getAtom().getTerms());
                std::vector<aspc::Literal> currentBodyLits2 = std::vector<aspc::Literal>(bodyLitsByElement.back().begin(), bodyLitsByElement.back().end());
                aspc::Literal negBodyLit2 = aspc::Literal(true, aspc::Atom(elem.getAtom().getPredicateName(), elem.getAtom().getTerms()));
                currentBodyLits2.push_back(negBodyLit2);
                rewrittenProgram.addRule(aspc::Rule({headAtom2}, currentBodyLits2, bodyRelsByElement.back(), true));
                ruleLabels.push_back(toGroundNormalRules(toGround));
            }else{
                rewrittenProgram.addRule(aspc::Rule({elem.getAtom()}, bodyLitsByElement.back(), bodyRelsByElement.back(), true));
                ruleLabels.push_back(toGroundNormalRules(toGround));
            }

        }
        //if there is at least one guard, add choiceSet and constraints with aggregate
        if(rule.getLeftGuard().getTerm1() != "" || rule.getRightGuard().getTerm1() != ""){
            //Construct choice set
            std::unordered_set<std::string> bodyVarsSet;
            //find choice body vars
            for(const aspc::Formula* f : rule.getFormulas()){
                f->addVariablesToSet(bodyVarsSet);
            }

            //find choice element head variables
            std::vector<std::vector<std::string>> choiceElemHeadVars;
            for(const aspc::ChoiceElement& elem : rule.getHead()){
                //add all head variables
                std::unordered_set<std::string> choiceElemHeadVarsSet;
                for(unsigned j = 0; j < elem.getAtom().getTermsSize(); ++j)
                    if(elem.getAtom().isVariableTermAt(j))
                        choiceElemHeadVarsSet.insert(elem.getAtom().getTermAt(j));
                choiceElemHeadVars.push_back(std::vector<std::string>(choiceElemHeadVarsSet.begin(), choiceElemHeadVarsSet.end()));
            }

            //compute choiceSet arity as the maximum number of varisbles in choiceElemHeadVars
            unsigned maxArity = 0;
            for(unsigned j = 0; j < choiceElemHeadVars.size(); ++j){
                if(choiceElemHeadVars.at(j).size() > maxArity)
                    maxArity = choiceElemHeadVars.at(j).size();
            }
            //padding is the difference between the max arity and minimum arity plus the term needed for representing the predicate
            unsigned choiceSetLitArity = bodyVarsSet.size() + maxArity;

            //if more than one predicate is defined in the choice, then a predicate term is required
            if(predicatesInChoiceHead.size() > 1) choiceSetLitArity++;

            std::vector<std::string> sharedBodyVars(bodyVarsSet.begin(), bodyVarsSet.end());
            //build chset rules
            std::vector<std::string> bodyVars;

            //find body vars to be added to choiceSetAtom
            for(std::string var: sharedBodyVars){
                bodyVars.push_back(var);
            }
            if(rule.getHead().size() > 1){
                for(unsigned j = 0; j < rule.getHead().size(); ++j){
                    const aspc::ChoiceElement& elem = rule.getHead().at(j);
                    std::vector<std::string> choiceSetVars(bodyVars.begin(), bodyVars.end());
                    for(unsigned k = 0; k < choiceElemHeadVars.at(j).size(); ++k)
                        choiceSetVars.push_back(choiceElemHeadVars.at(j).at(k));

                    //fill literal terms with a constant
                    for(unsigned k = choiceSetVars.size(); k < choiceSetLitArity-1; ++k){
                        choiceSetVars.push_back("1");
                    }

                    if(predicatesInChoiceHead.size() > 1){
                        choiceSetVars.push_back(elem.getAtom().getPredicateName());
                    }
                    //construct and add rule defining choice set
                    std::vector<aspc::Literal> bodyLitsForElement (bodyLits.begin(), bodyLits.end());
                    bodyLitsForElement.push_back(aspc::Literal(false, elem.getAtom()));
                    
                    //add body lits and body rels of choice elem
                    for(const aspc::Literal& lit : elem.getBodyLiterals()){
                        bodyLitsForElement.push_back(lit);
                    }
                    
                    std::vector<aspc::ArithmeticRelation> ruleBodyAndChoiceElemBodyRels(bodyRels.begin(), bodyRels.end());
                    for(const aspc::ArithmeticRelation& rel : elem.getArithmeticRelations()){
                        ruleBodyAndChoiceElemBodyRels.push_back(rel);
                    }

                    aspc::Atom choiceSetRuleHead(ChoiceRewriter::CHOICE_SET_ATOM_NAME + std::to_string(i), choiceSetVars);
                    //add normal rule from choice defining choiceSet
                    rewrittenProgram.addRule(aspc::Rule({choiceSetRuleHead}, bodyLitsForElement, ruleBodyAndChoiceElemBodyRels, false));
                    ruleLabels.push_back(toGroundNormalRules(toGround));

                }
            }
            for(unsigned k = 0; k < 2; ++k){
                const aspc::ArithmeticExpression& guard = k == 0 ? rule.getLeftGuard() : rule.getRightGuard();
                aspc::ComparisonType guardComparisonType = k == 0 ? rule.getLeftGuardComparisonType() : rule.getRightGuardComparisonType();
                aspc::ComparisonType aggrComparison;
                if((k == 0 && guard.getTerm1() == "") || ((k == 1 && guard.getTerm1() == "")))
                    continue;
                if(k == 0 && guard.getTerm1() != ""){
                    if(guardComparisonType == aspc::ComparisonType::LT)
                        aggrComparison = aspc::ComparisonType::LTE;
                    else if(guardComparisonType == aspc::ComparisonType::LTE)
                        aggrComparison = aspc::ComparisonType::LT;
                    else if(guardComparisonType == aspc::ComparisonType::GT)
                        aggrComparison = aspc::ComparisonType::GTE;
                    else if(guardComparisonType == aspc::ComparisonType::GTE)
                        aggrComparison = aspc::ComparisonType::GT;
                    else if (guardComparisonType == aspc::ComparisonType::EQ)
                        aggrComparison = aspc::ComparisonType::NE;
                    else if (guardComparisonType == aspc::ComparisonType::NE)
                        aggrComparison = aspc::ComparisonType::EQ;
                }

                if(k == 1 && guard.getTerm1() != ""){
                    if(guardComparisonType == aspc::ComparisonType::GT)
                        aggrComparison = aspc::ComparisonType::LTE;
                    else if(guardComparisonType == aspc::ComparisonType::GTE)
                        aggrComparison = aspc::ComparisonType::LT;
                    else if(guardComparisonType == aspc::ComparisonType::LT)
                        aggrComparison = aspc::ComparisonType::GTE;
                    else if(guardComparisonType == aspc::ComparisonType::LTE)
                        aggrComparison = aspc::ComparisonType::GT;
                    else if (guardComparisonType == aspc::ComparisonType::EQ)
                        aggrComparison = aspc::ComparisonType::NE;
                    else if (guardComparisonType == aspc::ComparisonType::NE)
                        aggrComparison = aspc::ComparisonType::EQ;
                }

                std::vector<std::string> aggregationVars;
                //if only one choice element in choice there is no corresponding choice set declared and the body of the count
                //aggregate becomes the choice element head in conjunction with the choice element body
                std::vector<aspc::Literal> aggBodyLits;
                std::vector<aspc::ArithmeticRelation> aggregateInequalities;
                if(rule.getHead().size() == 1){
                    for(aspc::ArithmeticRelation rel : rule.getHead().at(0).getArithmeticRelations())
                        aggregateInequalities.push_back(rel);
                    
                    aggBodyLits.push_back(aspc::Literal(false, rule.getHead().at(0).getAtom()));

                    for(aspc::Literal lit : rule.getHead().at(0).getBodyLiterals())
                        aggBodyLits.push_back(lit);

                    for(unsigned k = 0; k < rule.getHead().at(0).getAtom().getTermsSize(); ++k){
                        if(rule.getHead().at(0).getAtom().isVariableTermAt(k)){
                            aggregationVars.push_back(rule.getHead().at(0).getAtom().getTermAt(k));
                        }
                    }

                }else{
                    //construct and add constraints with count aggregate
                    std::vector<std::string> constraintChoiceSetVariables(sharedBodyVars.begin(), sharedBodyVars.end());
                    
                    unsigned originalConstraintChoiceSetVariables = constraintChoiceSetVariables.size();
                    for(unsigned k = originalConstraintChoiceSetVariables; k < choiceSetLitArity; ++k){
                        constraintChoiceSetVariables.push_back(ChoiceRewriter::GENERIC_VARIABLE_NAME + std::to_string(k - originalConstraintChoiceSetVariables));
                        aggregationVars.push_back(ChoiceRewriter::GENERIC_VARIABLE_NAME + std::to_string(k - originalConstraintChoiceSetVariables));
                    }
                    aspc::Literal aggLiteral(false, aspc::Atom(ChoiceRewriter::CHOICE_SET_ATOM_NAME + std::to_string(i), constraintChoiceSetVariables));
                    aggBodyLits.push_back(aggLiteral);
                }

                aspc::Aggregate bodyAggregate(aggBodyLits, aggregateInequalities, aggregationVars, "#count");
                aspc::ArithmeticRelationWithAggregate aggrRelation(false, guard, bodyAggregate, aggrComparison, false);
                //add constraints from choice rules
                rewrittenProgram.addRule(aspc::Rule({}, rule.getBodyLiterals(), rule.getArithmeticRelations(), {aggrRelation}, false));
                ruleLabels.push_back(toGroundChoiceConstraints(toGround));
            }
        }
    }

    newFirstRuleIndex = program.getRulesSize();
    newFirstChoiceRuleIndex = program.getChoiceRulesSize();
}


const aspc::Program& ChoiceRewriter::getRewrittenProgram() const{
    return rewrittenProgram;
}

std::vector<bool> ChoiceRewriter::getRuleLabels() const{
    return ruleLabels;
}