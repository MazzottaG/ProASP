
// Generated from ASPCore2.g4 by ANTLR 4.10

#ifndef ASPCORE2COMPILEPROGRAMLISTENER_H
#define ASPCORE2COMPILEPROGRAMLISTENER_H


#include "antlr4-runtime.h"
#include "../parser/ASPCore2BaseListener.h"
#include "../parser/ASPCore2Parser.h"
#include "../language/Program.h"
#include "../utils/GraphWithTarjanAlgorithm.h"

/**
 * This class provides an empty implementation of ASPCore2Listener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  ASPCore2CompileProgramListener : public ASPCore2BaseListener {
  private:
    static std::set<int> watchedTerminalTypes;
    static std::set<int> forbiddenTerminalTypes;

    std::vector<std::string> terminals;
    std::vector<aspc::Atom> buildingAtoms;
    std::vector<bool> buildingAtomsPolarity;
    std::vector<aspc::ArithmeticRelation> buildingRels;
    std::vector<aspc::ArithmeticExpression> buildingExpression;
    std::vector<aspc::ArithmeticRelationWithAggregate> buildingAggregates;
    aspc::ComparisonType aggrComparison;
    aspc::ArithmeticExpression guard;
    bool lowerGuard;
    bool upperGuard;
    bool equalAggregate;
    
    aspc::Program program;
    std::vector<aspc::Atom> head;
    std::unordered_set<std::string> headVars;
    std::vector<aspc::Literal> bodyLiterals;
    std::unordered_set<std::string> positiveBodyVars;
    std::unordered_set<std::string> negativeBodyVars;
    GraphWithTarjanAlgorithm dg;
    GraphWithTarjanAlgorithm pdg;

    std::unordered_map<std::string,unsigned> predicateId;
    std::vector<std::string> predicateNames;
    std::vector<std::string> freshvariables;
    
    bool addedAtom;
    int atomStart;
    bool naf;
    int expNestingLevel;
    int factorNestingLevel;
    int lastTerminalSize;
    int factorStartIndex;

    bool readingAggregate;
    int aggregateStartIndex;
    int guardStartIndex;
    bool isGuardExpression;
    int aggrBodyLiteralStart;
    int aggrBodyIneqsStart;
    bool nafAggregate;

public:
  virtual void enterProgram(ASPCore2Parser::ProgramContext * /*ctx*/) override { 
      naf=false;
      atomStart=-1;
      expNestingLevel = -1;
      factorNestingLevel = -1;
      lastTerminalSize = -1;
      factorStartIndex = -1;
      readingAggregate=false;
      aggregateStartIndex=-1;
      guardStartIndex=-1;
  }
  
  bool checkTight(){
    bool tight = true;
    auto scc = pdg.SCC();
    for(int component = scc.size()-1; component>=0; component--){
        if(scc[component].size() > 1){
            tight=false;
            break;
        }
        if(tight && scc[component].size() == 1){
            int currentPredId = scc[component][0];
            if(program.isHeadPredicate(predicateNames[currentPredId])){
              auto rules = program.getRulesForPredicate(predicateNames[currentPredId]);
              for(unsigned ruleIndex: rules){
                const aspc::Rule* rule = &program.getRule(ruleIndex);
                    const std::vector<aspc::Literal>& body = rule->getBodyLiterals();
                  for(int i=0;i<body.size();i++){
                    if(!body[i].isNegated() && predicateNames[currentPredId] == body[i].getPredicateName()){
                        tight=false;
                        break;
                    }
                  }
                  if(!tight) break;                    
              }
            }
        }
        if(!tight) break;                    
    }
    return tight;
  }
  void addPredicate(std::string predicate){
    if(!predicateId.count(predicate)){
      predicateId[predicate]=predicateNames.size();
      predicateNames.push_back(predicate);
    }
  }
  
  bool checkStratified(){
    bool stratified = true;
    auto scc = dg.SCC();
    for(int component = scc.size()-1; component>=0; component--){
      std::unordered_set<int> componentSet;
      componentSet.insert(scc[component].begin(),scc[component].end());
      for(int currentPredId : scc[component]){
        if(!program.isHeadPredicate(predicateNames[currentPredId])) continue;
        for(int ruleIndex: program.getRulesForPredicate(predicateNames[currentPredId])){
          const aspc::Rule* rule = &program.getRule(ruleIndex);
          const std::vector<aspc::Literal>& body = rule->getBodyLiterals();
          for(int i=0;i<body.size();i++){
            if(body[i].isNegated() && componentSet.count(predicateId[body[i].getPredicateName()]) != 0){
              stratified=false;
              break;
            }
          }
          if(!stratified) break;                    
        }
      }
      if(!stratified) break;                    
    }
    return stratified;
  }
  
  const aspc::Program& getProgram()const {return program;} 
  const std::vector<std::string>& getPredicateNames()const {return predicateNames;} 
  const std::unordered_map<std::string,unsigned>& getPredicateIds()const {return predicateId;} 
  
  virtual void exitProgram(ASPCore2Parser::ProgramContext * /*ctx*/) override { 
    std::cout << "Program built"<<std::endl;
    program.setTight(checkTight());
    std::cout << "Tight: " << (program.isTight() ? "Yes" : "No") << std::endl;
    program.setStratified(checkStratified());
    std::cout << "Stratified: " << (program.isStratified() ? "Yes" : "No") << std::endl;
    program.print();
  }

  virtual void enterRule_(ASPCore2Parser::Rule_Context * /*ctx*/) override { }
  virtual void exitRule_(ASPCore2Parser::Rule_Context * /*ctx*/) override { }

  virtual void enterSimple_rule(ASPCore2Parser::Simple_ruleContext * /*ctx*/) override { 
    // program.newRule();
    // currentRule = program.lastRule();
    freshvariables.clear();
  }
  virtual void exitSimple_rule(ASPCore2Parser::Simple_ruleContext * /*ctx*/) override {
    // std::cout << "Found Body Literals: ";
    // for(aspc::Literal body : bodyLiterals) body.print(); 
    // std::cout << std::endl;
    // std::cout << "Found Body Inequality: ";
    // for(aspc::ArithmeticRelation body : buildingRels) body.print(); 
    // std::cout << std::endl;
    // std::cout << "Found Body Aggregates: ";
    // for(aspc::ArithmeticRelationWithAggregate body : buildingAggregates) body.print(); 
    // std::cout << std::endl;
    aspc::Rule rule(head,bodyLiterals,buildingRels,buildingAggregates,false,false);
    bool safe = true;
    for(int i=0;i<buildingRels.size();i++){
      if(!buildingRels[i].isBoundedRelation(positiveBodyVars)){
        safe=false;
      }
    }
    if(safe)
      for(std::unordered_set<std::string> vars : {negativeBodyVars,headVars}){
        for(std::string var : vars){
          if(!positiveBodyVars.count(var)){
            safe=false;
            break;
          }
        }
        if(!safe) break;
      }
    if(!safe){
      std::cout << "Safety Error :";rule.print();
      exit(180);
    }
    addDependencies(rule);    
    program.addRule(rule);
    buildingAtoms.clear();
    buildingExpression.clear();
    buildingRels.clear();
    buildingAggregates.clear();
    head.clear();
    buildingAtomsPolarity.clear();
    bodyLiterals.clear();
    std::cout << "parsed rule ";rule.print();
  }
  void addDependencies(aspc::Rule& r) {
    if(!r.isConstraint()){
      std::vector<unsigned> headPredicateId;
      for(const aspc::Atom& a : r.getHead()){
        headPredicateId.push_back(predicateId[a.getPredicateName()]);
      }
      for(const aspc::Literal& literal : r.getBodyLiterals()){
        unsigned predId = predicateId[literal.getAtom().getPredicateName()];
        for(unsigned i=0;i<headPredicateId.size();i++){
          if(!literal.isNegated()) pdg.addEdge(predId,headPredicateId[i]);
          dg.addEdge(predId,headPredicateId[i]);
        }
      }
    }
  }
  virtual void enterHead(ASPCore2Parser::HeadContext * /*ctx*/) override { 
    buildingAtoms.clear();
    buildingExpression.clear();
    buildingRels.clear();
    head.clear();

  }
  virtual void exitHead(ASPCore2Parser::HeadContext * /*ctx*/) override { 
    if(buildingAtoms.size() > 1){
      std::cout << "Disjunctive rules not supported yet"<<std::endl;
      exit(180);
    }
    for(int i=0; i<buildingAtoms.size();i++){
      head.push_back(aspc::Atom(buildingAtoms[i]));
      aspc::Literal(false,head.back()).addVariablesToSet(headVars);
    }
  }

  virtual void enterBody(ASPCore2Parser::BodyContext * /*ctx*/) override { 
    buildingAtoms.clear();
    buildingAtomsPolarity.clear();
    buildingExpression.clear();
    bodyLiterals.clear();
  }
  virtual void exitBody(ASPCore2Parser::BodyContext * /*ctx*/) override { 
    for(int i=0; i<buildingAtoms.size();i++){
      bodyLiterals.push_back(aspc::Literal(buildingAtomsPolarity[i],buildingAtoms[i]));
      bodyLiterals.back().addVariablesToSet(buildingAtomsPolarity[i] ? negativeBodyVars : positiveBodyVars);
    }
    unsigned size=0;
    do{
      size=positiveBodyVars.size();
      for(int i=0;i<buildingRels.size();i++){
        if(buildingRels[i].isBoundedValueAssignment(positiveBodyVars)){
          positiveBodyVars.insert(buildingRels[i].getAssignedVariable(positiveBodyVars));
        }
      }
      for(int i=0;i<buildingAggregates.size();i++){
        if(buildingAggregates[i].isBoundedValueAssignment(positiveBodyVars)){
          positiveBodyVars.insert(buildingAggregates[i].getAssignedVariable(positiveBodyVars));
        }
      }
    }while (size!=positiveBodyVars.size());
  }

  virtual void enterWeight_at_levels(ASPCore2Parser::Weight_at_levelsContext * /*ctx*/) override { }
  virtual void exitWeight_at_levels(ASPCore2Parser::Weight_at_levelsContext * /*ctx*/) override { }

  virtual void enterLevels_and_terms(ASPCore2Parser::Levels_and_termsContext * /*ctx*/) override { }
  virtual void exitLevels_and_terms(ASPCore2Parser::Levels_and_termsContext * /*ctx*/) override { }

  virtual void enterDisjunction(ASPCore2Parser::DisjunctionContext * /*ctx*/) override {
    
  }
  virtual void exitDisjunction(ASPCore2Parser::DisjunctionContext * /*ctx*/) override { 
    
  }

  virtual void enterConjunction(ASPCore2Parser::ConjunctionContext * /*ctx*/) override {
  }
  virtual void exitConjunction(ASPCore2Parser::ConjunctionContext * /*ctx*/) override { 
  }

  virtual void enterChoice_atom(ASPCore2Parser::Choice_atomContext * /*ctx*/) override { }
  virtual void exitChoice_atom(ASPCore2Parser::Choice_atomContext * /*ctx*/) override { }

  virtual void enterLower_guard(ASPCore2Parser::Lower_guardContext * /*ctx*/) override { }
  virtual void exitLower_guard(ASPCore2Parser::Lower_guardContext * /*ctx*/) override { }

  virtual void enterUpper_guard(ASPCore2Parser::Upper_guardContext * /*ctx*/) override { }
  virtual void exitUpper_guard(ASPCore2Parser::Upper_guardContext * /*ctx*/) override { }

  virtual void enterChoice_elements(ASPCore2Parser::Choice_elementsContext * /*ctx*/) override { }
  virtual void exitChoice_elements(ASPCore2Parser::Choice_elementsContext * /*ctx*/) override { }

  virtual void enterChoice_element(ASPCore2Parser::Choice_elementContext * /*ctx*/) override { }
  virtual void exitChoice_element(ASPCore2Parser::Choice_elementContext * /*ctx*/) override { }

  virtual void enterChoice_element_atom(ASPCore2Parser::Choice_element_atomContext * /*ctx*/) override { }
  virtual void exitChoice_element_atom(ASPCore2Parser::Choice_element_atomContext * /*ctx*/) override { }

  virtual void enterChoice_elements_literals(ASPCore2Parser::Choice_elements_literalsContext * /*ctx*/) override { }
  virtual void exitChoice_elements_literals(ASPCore2Parser::Choice_elements_literalsContext * /*ctx*/) override { }

  virtual void enterNaf_literals(ASPCore2Parser::Naf_literalsContext * /*ctx*/) override { }
  virtual void exitNaf_literals(ASPCore2Parser::Naf_literalsContext * /*ctx*/) override { }

  virtual void enterNaf_literal(ASPCore2Parser::Naf_literalContext * /*ctx*/) override {
    naf=false;
  }
  virtual void exitNaf_literal(ASPCore2Parser::Naf_literalContext * /*ctx*/) override {
    if(addedAtom){
      if(naf) std::cout<<"Found negated literal"<<std::endl;
      buildingAtomsPolarity.push_back(naf);
    }
    addedAtom=false;
  }

  virtual void enterNaf_literal_aggregate(ASPCore2Parser::Naf_literal_aggregateContext * /*ctx*/) override { 
    std::cout << "Found naf literal aggregate"<<std::endl;
    naf=false;
    nafAggregate=false;
  }
  virtual void exitNaf_literal_aggregate(ASPCore2Parser::Naf_literal_aggregateContext * /*ctx*/) override {
  }

  virtual void enterExistential_atom(ASPCore2Parser::Existential_atomContext * /*ctx*/) override { }
  virtual void exitExistential_atom(ASPCore2Parser::Existential_atomContext * /*ctx*/) override { }

  virtual void enterClassic_literal(ASPCore2Parser::Classic_literalContext * /*ctx*/) override { }
  virtual void exitClassic_literal(ASPCore2Parser::Classic_literalContext * /*ctx*/) override { 
    
  }

  virtual void enterAtom(ASPCore2Parser::AtomContext * /*ctx*/) override { 
    atomStart=terminals.size();
  }
  virtual void exitAtom(ASPCore2Parser::AtomContext * /*ctx*/) override {
    for(int i=0;i<buildingExpression.size();i++){
      std::cout << buildingExpression[i].getStringRep() << std::endl;
    }
    std::cout << "------------"<<std::endl;
    if(terminals.size() > atomStart){
      std::string predicateName = terminals[atomStart];
      auto it = predicateId.emplace(predicateName,predicateNames.size());
      if(it.second){
        predicateNames.push_back(predicateName);
        dg.addNode(it.first->second);
        pdg.addNode(it.first->second);
      }
      std::vector<std::string> terms;
      int expTermId=0;
      for(int i = atomStart+1; i < terminals.size(); i++){
        if(terminals[i]==""){
          aspc::ArithmeticExpression* exp = &buildingExpression[expTermId];
          if(exp->isSingleTerm()){
            terms.push_back(exp->getTerm1());
            expTermId++;
            continue;
          }
          std::string freshVar = "E_"+std::to_string(freshvariables.size());
          freshvariables.push_back(freshVar); 
          terms.push_back(freshVar);
          buildingRels.push_back(aspc::ArithmeticRelation(aspc::ArithmeticExpression(freshVar),buildingExpression[expTermId],aspc::EQ));
          expTermId++;
        }else{
          terms.push_back(terminals[i]);
        }
      }
      aspc::Atom a(predicateName,terms);
      buildingAtoms.push_back(a);
      buildingExpression.clear();
      addedAtom=true;
      while(terminals.size() > atomStart) terminals.pop_back();

    }else{
      std::cout << "WARNING: Unable to build atom"<<std::endl;
    }
  }

  virtual void enterExtAtom(ASPCore2Parser::ExtAtomContext * /*ctx*/) override { }
  virtual void exitExtAtom(ASPCore2Parser::ExtAtomContext * /*ctx*/) override { }

  virtual void enterExtSemicol(ASPCore2Parser::ExtSemicolContext * /*ctx*/) override { }
  virtual void exitExtSemicol(ASPCore2Parser::ExtSemicolContext * /*ctx*/) override { }

  virtual void enterTerms(ASPCore2Parser::TermsContext * /*ctx*/) override { }
  virtual void exitTerms(ASPCore2Parser::TermsContext * /*ctx*/) override { }

  virtual void enterBasic_terms(ASPCore2Parser::Basic_termsContext * /*ctx*/) override { }
  virtual void exitBasic_terms(ASPCore2Parser::Basic_termsContext * /*fctx*/) override { }

  virtual void enterBuiltin_atom(ASPCore2Parser::Builtin_atomContext * /*ctx*/) override { }
  virtual void exitBuiltin_atom(ASPCore2Parser::Builtin_atomContext * /*ctx*/) override {
    if(terminals.size() < 3){
      std::cout << "WARNING: Unable to read builtin atom"<<std::endl;
      std::cout << "Remaining symbols"<<std::endl;
      for(const std::string& s: terminals){
        std::cout << " " << s; 
      }
      std::cout <<std::endl;
      // std::cout << "Remaining arithOps:"<<std::endl;
      // for(const CompilableArithOp& s: arithOps){
      //   std::cout << " ";
      //   s.print();
      // }
      // std::cout <<std::endl;
      exit(180);
    }
    unsigned size = terminals.size();

    aspc::ArithmeticExpression right = terminals.back() == "" ? buildingExpression.back() : aspc::ArithmeticExpression(terminals.back());
    if(terminals.back() == ""){
      buildingExpression.pop_back();
    }

    aspc::ArithmeticExpression left = terminals[size-3] == "" ? buildingExpression.back() : aspc::ArithmeticExpression(terminals[size-3]);
    if(terminals[size-3] == ""){
      buildingExpression.pop_back();
    }

    buildingRels.push_back(aspc::ArithmeticRelation(left,right,aspc::ArithmeticRelation::string2ComparisonType[terminals[size-2]]));
    terminals.pop_back();
    terminals.pop_back();
    terminals.pop_back();
    
  }

  virtual void enterCompareop(ASPCore2Parser::CompareopContext * /*ctx*/) override { }
  virtual void exitCompareop(ASPCore2Parser::CompareopContext * /*ctx*/) override { }

  virtual void enterBinop(ASPCore2Parser::BinopContext * /*ctx*/) override { }
  virtual void exitBinop(ASPCore2Parser::BinopContext * /*ctx*/) override { }

  virtual void enterArithop1(ASPCore2Parser::Arithop1Context * /*ctx*/) override { }
  virtual void exitArithop1(ASPCore2Parser::Arithop1Context * /*ctx*/) override { }

  virtual void enterArithop2(ASPCore2Parser::Arithop2Context * /*ctx*/) override { }
  virtual void exitArithop2(ASPCore2Parser::Arithop2Context * /*ctx*/) override { }

  virtual void enterTerm_(ASPCore2Parser::Term_Context * /*ctx*/) override { }
  virtual void exitTerm_(ASPCore2Parser::Term_Context * /*ctx*/) override { }

  virtual void enterTerm__(ASPCore2Parser::Term__Context * /*ctx*/) override { }
  virtual void exitTerm__(ASPCore2Parser::Term__Context * /*ctx*/) override { }

  virtual void enterTerm(ASPCore2Parser::TermContext * /*ctx*/) override { }
  virtual void exitTerm(ASPCore2Parser::TermContext * /*ctx*/) override { }

  virtual void enterExpr(ASPCore2Parser::ExprContext * /*ctx*/) override {
    if(guardStartIndex > 0) isGuardExpression=true;
    expNestingLevel++;
    if(expNestingLevel>1){
      std::cout << "Error parsing expression: accepted format X+Y where X and Y are either symbolic or numberic terms"<<std::endl;
      exit(180);
    }
    if(expNestingLevel == 0){
      lastTerminalSize = terminals.size();
    }
  }
  virtual void exitExpr(ASPCore2Parser::ExprContext * /*ctx*/) override { 
      expNestingLevel--;
      if(expNestingLevel < 0){
        int expLength = terminals.size()-lastTerminalSize;
        if(expLength != 1 && expLength != 3) {std::cout << "Error parsing expression"<<std::endl; exit(180);}
        if(expLength == 1){
          if(terminals.back() != ""){
            aspc::ArithmeticExpression exp(terminals.back());
            buildingExpression.push_back(exp);
            terminals.back()="";
          }
        }else{
          // if(terminals[lastTerminalSize] == "" || terminals[lastTerminalSize+2] == ""){
          //   std::cout << "Nested sum or multiplication not allowed"<<std::endl;
          //   exit(180);
          // }
          assert(terminals[lastTerminalSize] == "" && terminals[lastTerminalSize+2] == "");
          assert(buildingExpression.back().isSingleTerm() && buildingExpression[buildingExpression.size()-2].isSingleTerm());
          aspc::ArithmeticExpression exp(buildingExpression[buildingExpression.size()-2].getTerm1(),buildingExpression.back().getTerm1(),terminals[lastTerminalSize+1][0]);
          terminals.resize(lastTerminalSize);
          terminals.push_back("");
          buildingExpression.resize(buildingExpression.size()-2);
          buildingExpression.push_back(exp);
        }
      }
  }

  virtual void enterFactor(ASPCore2Parser::FactorContext * /*ctx*/) override {
    factorNestingLevel++;
    if(factorNestingLevel == 0) factorStartIndex = terminals.size();
    if(factorNestingLevel > 1) {
      std::cout << "No nested factor supported"<<std::endl;
      exit(180);
    }
  }
  virtual void exitFactor(ASPCore2Parser::FactorContext * /*ctx*/) override { 
    // for(int i=0;i<factorNestingLevel;i++) std::cout << "   ";
    // std::cout << "Exiting factor "<< factorNestingLevel-- <<std::endl;
    factorNestingLevel--;
    if(factorNestingLevel < 0){
        assert(factorStartIndex >= 0);
        int expLength = terminals.size()-factorStartIndex;
        if(expLength != 1 && expLength != 3) {std::cout << "Error parsing factor: found factor with length "<<expLength<<std::endl; exit(180);}
        if(expLength == 1){
          aspc::ArithmeticExpression exp(terminals.back());
          buildingExpression.push_back(exp);
          terminals.back()="";
          // std::cout << "Found factor "<<exp.getTerm1() <<std::endl;
        }else{
          aspc::ArithmeticExpression exp(terminals[lastTerminalSize],terminals[lastTerminalSize+2],terminals[lastTerminalSize+1][0]);
          // std::cout << "Found factor "<<exp.getTerm1();
          // if(!exp.isSingleTerm())
          //   std::cout << exp.getOperation();
          // std::cout << (!exp.isSingleTerm() ? exp.getTerm2() : "") <<std::endl;
          terminals.resize(factorStartIndex);
          terminals.push_back("");
          buildingExpression.push_back(exp);
        }
      }
  }

  virtual void enterBasic_term(ASPCore2Parser::Basic_termContext * /*ctx*/) override { }
  virtual void exitBasic_term(ASPCore2Parser::Basic_termContext * /*ctx*/) override { }

  virtual void enterGround_term(ASPCore2Parser::Ground_termContext * /*ctx*/) override { }
  virtual void exitGround_term(ASPCore2Parser::Ground_termContext * /*ctx*/) override { }

  virtual void enterVariable_term(ASPCore2Parser::Variable_termContext * /*ctx*/) override { }
  virtual void exitVariable_term(ASPCore2Parser::Variable_termContext * /*ctx*/) override { }

  virtual void enterFunctional_term(ASPCore2Parser::Functional_termContext * /*ctx*/) override { }
  virtual void exitFunctional_term(ASPCore2Parser::Functional_termContext * /*ctx*/) override { }

  virtual void enterVars(ASPCore2Parser::VarsContext * /*ctx*/) override { }
  virtual void exitVars(ASPCore2Parser::VarsContext * /*ctx*/) override { }

  virtual void enterIdentifier(ASPCore2Parser::IdentifierContext * /*ctx*/) override { }
  virtual void exitIdentifier(ASPCore2Parser::IdentifierContext * /*ctx*/) override { }

  virtual void enterDirective(ASPCore2Parser::DirectiveContext * /*ctx*/) override { }
  virtual void exitDirective(ASPCore2Parser::DirectiveContext * /*ctx*/) override { }

  virtual void enterQuery(ASPCore2Parser::QueryContext * /*ctx*/) override { }
  virtual void exitQuery(ASPCore2Parser::QueryContext * /*ctx*/) override { }

  virtual void enterLower_guard_compare_aggregate(ASPCore2Parser::Lower_guard_compare_aggregateContext * /*ctx*/) override { }
  virtual void exitLower_guard_compare_aggregate(ASPCore2Parser::Lower_guard_compare_aggregateContext * /*ctx*/) override {
    std::cout << "Terminals stack:";
    for(std::string t : terminals) std::cout << " " << t;
    std::cout << std::endl;
    std::cout << "Exiting from lower_guard_compare_aggregate"<<std::endl;
    lowerGuard=true;

  }

  virtual void enterUpper_guard_compare_aggregate(ASPCore2Parser::Upper_guard_compare_aggregateContext * /*ctx*/) override { }
  virtual void exitUpper_guard_compare_aggregate(ASPCore2Parser::Upper_guard_compare_aggregateContext * /*ctx*/) override { 
    std::cout << "Terminals stack:";
    for(std::string t : terminals) std::cout << " " << t;
    std::cout << std::endl;
    std::cout << "Exiting from upper_guard_compare_aggregate"<<std::endl;
    upperGuard=true;
  }

  virtual void enterCompare_aggregate(ASPCore2Parser::Compare_aggregateContext * /*ctx*/) override { 
    lowerGuard=false;
    upperGuard=false;
    equalAggregate=true;
  }
  virtual void exitCompare_aggregate(ASPCore2Parser::Compare_aggregateContext * /*ctx*/) override { }

  virtual void enterLower_guard_leftward_left_aggregate(ASPCore2Parser::Lower_guard_leftward_left_aggregateContext * /*ctx*/) override { }
  virtual void exitLower_guard_leftward_left_aggregate(ASPCore2Parser::Lower_guard_leftward_left_aggregateContext * /*ctx*/) override { }

  virtual void enterLeftward_left_aggregate(ASPCore2Parser::Leftward_left_aggregateContext * /*ctx*/) override { }
  virtual void exitLeftward_left_aggregate(ASPCore2Parser::Leftward_left_aggregateContext * /*ctx*/) override { }

  virtual void enterLeft_aggregate(ASPCore2Parser::Left_aggregateContext * /*ctx*/) override { std::cout << "Error: leftward not supported yet. Coming soon ..."<<std::endl; exit(180); }
  virtual void exitLeft_aggregate(ASPCore2Parser::Left_aggregateContext * /*ctx*/) override { }

  virtual void enterLower_guard_rightward_left_aggregate(ASPCore2Parser::Lower_guard_rightward_left_aggregateContext * /*ctx*/) override { }
  virtual void exitLower_guard_rightward_left_aggregate(ASPCore2Parser::Lower_guard_rightward_left_aggregateContext * /*ctx*/) override { }

  virtual void enterRightward_left_aggregate(ASPCore2Parser::Rightward_left_aggregateContext * /*ctx*/) override { }
  virtual void exitRightward_left_aggregate(ASPCore2Parser::Rightward_left_aggregateContext * /*ctx*/) override { }

  void startGuard(){
    guardStartIndex=terminals.size(); 
    isGuardExpression=false;
    std::cout << "start reading guard"<<std::endl;
  }
  void endGuard(){
    aggrComparison = aspc::ArithmeticRelation::string2ComparisonType[terminals[guardStartIndex]];
    if(isGuardExpression) {
      aspc::ArithmeticExpression* exp = &buildingExpression.back();
      std::cout << "Found expression guard ";
      guard.copy(exp);
      buildingExpression.pop_back();
      std::cout << guard.getStringRep();
    }else{
      // terminals should be of the form ...... operator guard
      assert(terminals.size()-guardStartIndex == 2);
      aspc::ArithmeticExpression exp(terminals.back());
      std::cout << "Found term guard ";
      guard.copy(&exp);
      std::cout << guard.getStringRep();
    }
    while(terminals.size()>guardStartIndex) terminals.pop_back();
    std::cout << std::endl;
    guardStartIndex=-1;
  }
  virtual void enterUpper_guard_leftward_right_aggregate(ASPCore2Parser::Upper_guard_leftward_right_aggregateContext * /*ctx*/) override { 
    startGuard(); 
  }
  virtual void exitUpper_guard_leftward_right_aggregate(ASPCore2Parser::Upper_guard_leftward_right_aggregateContext * /*ctx*/) override { 
    endGuard();
  }

  virtual void enterUpper_guard_rightward_right_aggregate(ASPCore2Parser::Upper_guard_rightward_right_aggregateContext * /*ctx*/) override { 
    startGuard();
  }
  virtual void exitUpper_guard_rightward_right_aggregate(ASPCore2Parser::Upper_guard_rightward_right_aggregateContext * /*ctx*/) override { 
    endGuard();
  }

  virtual void enterRight_aggregate(ASPCore2Parser::Right_aggregateContext * /*ctx*/) override { }
  virtual void exitRight_aggregate(ASPCore2Parser::Right_aggregateContext * /*ctx*/) override { }

  virtual void enterAggregate_atom(ASPCore2Parser::Aggregate_atomContext * /*ctx*/) override {
    readingAggregate = true;
    aggrBodyLiteralStart = buildingAtoms.size();
    aggrBodyIneqsStart = buildingRels.size();
    aggregateStartIndex = terminals.size();
    equalAggregate=false;
    std::cout << "Literals starts from id "<<aggrBodyLiteralStart<<std::endl;
  }
  virtual void exitAggregate_atom(ASPCore2Parser::Aggregate_atomContext * /*ctx*/) override { 
    readingAggregate = false;
    if(equalAggregate){
      if(terminals.back() == "")
        guard = buildingExpression.back();
      else guard = aspc::ArithmeticExpression(terminals.back());
      terminals.pop_back();

      aggrComparison = aspc::ArithmeticRelation::string2ComparisonType[terminals.back()];
      terminals.pop_back();
    }
    std::vector<std::string> variables;
    for(int i=aggregateStartIndex+1; i<terminals.size(); i++){
      variables.push_back(terminals[i]);
    }
    while (terminals.size() > aggregateStartIndex+1) terminals.pop_back();

    std::vector<aspc::Literal> literals;
    for(int i=aggrBodyLiteralStart; i<buildingAtoms.size();i++){
      literals.push_back(aspc::Literal(buildingAtomsPolarity[i],buildingAtoms[i]));
    }
    while(buildingAtoms.size() > aggrBodyLiteralStart) {buildingAtoms.pop_back(); buildingAtomsPolarity.pop_back();}
    
    std::vector<aspc::ArithmeticRelation> ineqs;
    for(int i=aggrBodyIneqsStart; i<buildingRels.size();i++){
      ineqs.push_back(aspc::ArithmeticRelation(buildingRels[i]));
    }
    while(buildingRels.size() > aggrBodyIneqsStart) buildingRels.pop_back();
    aspc::Aggregate aggregate(literals,ineqs, variables, terminals[aggregateStartIndex]);
    terminals.pop_back();
    buildingAggregates.push_back(aspc::ArithmeticRelationWithAggregate (false,guard,aggregate,aggrComparison,nafAggregate));

    std::cout << "Parsed aggregates ";
    buildingAggregates.back().print();
    aggregateStartIndex=-1;
    aggrBodyLiteralStart=-1;
    aggrBodyIneqsStart=-1;
    std::cout << std::endl;
  }

  virtual void enterLeftwardop(ASPCore2Parser::LeftwardopContext * /*ctx*/) override { }
  virtual void exitLeftwardop(ASPCore2Parser::LeftwardopContext * /*ctx*/) override { }

  virtual void enterRightwardop(ASPCore2Parser::RightwardopContext * /*ctx*/) override { }
  virtual void exitRightwardop(ASPCore2Parser::RightwardopContext * /*ctx*/) override { }

  virtual void enterAggregate(ASPCore2Parser::AggregateContext * /*ctx*/) override { }
  virtual void exitAggregate(ASPCore2Parser::AggregateContext * /*ctx*/) override { }

  virtual void enterAggregate_elements(ASPCore2Parser::Aggregate_elementsContext * /*ctx*/) override { }
  virtual void exitAggregate_elements(ASPCore2Parser::Aggregate_elementsContext * /*ctx*/) override { }

  virtual void enterAggregate_element(ASPCore2Parser::Aggregate_elementContext * /*ctx*/) override { }
  virtual void exitAggregate_element(ASPCore2Parser::Aggregate_elementContext * /*ctx*/) override { }

  virtual void enterAggregate_function(ASPCore2Parser::Aggregate_functionContext * /*ctx*/) override { }
  virtual void exitAggregate_function(ASPCore2Parser::Aggregate_functionContext * /*ctx*/) override { }

  virtual void enterAnnotation_global(ASPCore2Parser::Annotation_globalContext * /*ctx*/) override { }
  virtual void exitAnnotation_global(ASPCore2Parser::Annotation_globalContext * /*ctx*/) override { }

  virtual void enterAnnotations_rule(ASPCore2Parser::Annotations_ruleContext * /*ctx*/) override { }
  virtual void exitAnnotations_rule(ASPCore2Parser::Annotations_ruleContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule(ASPCore2Parser::Annotation_ruleContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule(ASPCore2Parser::Annotation_ruleContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_to_decompose(ASPCore2Parser::Annotation_rule_to_decomposeContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_to_decompose(ASPCore2Parser::Annotation_rule_to_decomposeContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_to_not_decompose(ASPCore2Parser::Annotation_rule_to_not_decomposeContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_to_not_decompose(ASPCore2Parser::Annotation_rule_to_not_decomposeContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_ordering(ASPCore2Parser::Annotation_rule_orderingContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_ordering(ASPCore2Parser::Annotation_rule_orderingContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_ordering(ASPCore2Parser::Annotation_global_orderingContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_ordering(ASPCore2Parser::Annotation_global_orderingContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_extatom_conversion(ASPCore2Parser::Annotation_global_extatom_conversionContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_extatom_conversion(ASPCore2Parser::Annotation_global_extatom_conversionContext * /*ctx*/) override { }

  virtual void enterAnnotation_extpredicate(ASPCore2Parser::Annotation_extpredicateContext * /*ctx*/) override { }
  virtual void exitAnnotation_extpredicate(ASPCore2Parser::Annotation_extpredicateContext * /*ctx*/) override { }

  virtual void enterExtatom_conv_types(ASPCore2Parser::Extatom_conv_typesContext * /*ctx*/) override { }
  virtual void exitExtatom_conv_types(ASPCore2Parser::Extatom_conv_typesContext * /*ctx*/) override { }

  virtual void enterExtatom_conv_type(ASPCore2Parser::Extatom_conv_typeContext * /*ctx*/) override { }
  virtual void exitExtatom_conv_type(ASPCore2Parser::Extatom_conv_typeContext * /*ctx*/) override { }

  virtual void enterRule_ordering_type(ASPCore2Parser::Rule_ordering_typeContext * /*ctx*/) override { }
  virtual void exitRule_ordering_type(ASPCore2Parser::Rule_ordering_typeContext * /*ctx*/) override { }

  virtual void enterGlobal_ordering_type(ASPCore2Parser::Global_ordering_typeContext * /*ctx*/) override { }
  virtual void exitGlobal_ordering_type(ASPCore2Parser::Global_ordering_typeContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_atom_indexed(ASPCore2Parser::Annotation_rule_atom_indexedContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_atom_indexed(ASPCore2Parser::Annotation_rule_atom_indexedContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_atom_indexed(ASPCore2Parser::Annotation_global_atom_indexedContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_atom_indexed(ASPCore2Parser::Annotation_global_atom_indexedContext * /*ctx*/) override { }

  virtual void enterRule_indexing_arguments(ASPCore2Parser::Rule_indexing_argumentsContext * /*ctx*/) override { }
  virtual void exitRule_indexing_arguments(ASPCore2Parser::Rule_indexing_argumentsContext * /*ctx*/) override { }

  virtual void enterRule_naf_literal_annotation(ASPCore2Parser::Rule_naf_literal_annotationContext * /*ctx*/) override { }
  virtual void exitRule_naf_literal_annotation(ASPCore2Parser::Rule_naf_literal_annotationContext * /*ctx*/) override { }

  virtual void enterGlobal_indexing_arguments(ASPCore2Parser::Global_indexing_argumentsContext * /*ctx*/) override { }
  virtual void exitGlobal_indexing_arguments(ASPCore2Parser::Global_indexing_argumentsContext * /*ctx*/) override { }

  virtual void enterGlobal_naf_literal_annotation(ASPCore2Parser::Global_naf_literal_annotationContext * /*ctx*/) override { }
  virtual void exitGlobal_naf_literal_annotation(ASPCore2Parser::Global_naf_literal_annotationContext * /*ctx*/) override { }

  virtual void enterRule_atom_annotation_before(ASPCore2Parser::Rule_atom_annotation_beforeContext * /*ctx*/) override { }
  virtual void exitRule_atom_annotation_before(ASPCore2Parser::Rule_atom_annotation_beforeContext * /*ctx*/) override { }

  virtual void enterGlobal_atom_annotation_before(ASPCore2Parser::Global_atom_annotation_beforeContext * /*ctx*/) override { }
  virtual void exitGlobal_atom_annotation_before(ASPCore2Parser::Global_atom_annotation_beforeContext * /*ctx*/) override { }

  virtual void enterRule_atom_annotation_after(ASPCore2Parser::Rule_atom_annotation_afterContext * /*ctx*/) override { }
  virtual void exitRule_atom_annotation_after(ASPCore2Parser::Rule_atom_annotation_afterContext * /*ctx*/) override { }

  virtual void enterGlobal_atom_annotation_after(ASPCore2Parser::Global_atom_annotation_afterContext * /*ctx*/) override { }
  virtual void exitGlobal_atom_annotation_after(ASPCore2Parser::Global_atom_annotation_afterContext * /*ctx*/) override { }

  virtual void enterRule_atoms_annotation_before(ASPCore2Parser::Rule_atoms_annotation_beforeContext * /*ctx*/) override { }
  virtual void exitRule_atoms_annotation_before(ASPCore2Parser::Rule_atoms_annotation_beforeContext * /*ctx*/) override { }

  virtual void enterGlobal_atoms_annotation_before(ASPCore2Parser::Global_atoms_annotation_beforeContext * /*ctx*/) override { }
  virtual void exitGlobal_atoms_annotation_before(ASPCore2Parser::Global_atoms_annotation_beforeContext * /*ctx*/) override { }

  virtual void enterRule_atoms_annotation_after(ASPCore2Parser::Rule_atoms_annotation_afterContext * /*ctx*/) override { }
  virtual void exitRule_atoms_annotation_after(ASPCore2Parser::Rule_atoms_annotation_afterContext * /*ctx*/) override { }

  virtual void enterGlobal_atoms_annotation_after(ASPCore2Parser::Global_atoms_annotation_afterContext * /*ctx*/) override { }
  virtual void exitGlobal_atoms_annotation_after(ASPCore2Parser::Global_atoms_annotation_afterContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_partial_order_begin(ASPCore2Parser::Annotation_rule_partial_order_beginContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_partial_order_begin(ASPCore2Parser::Annotation_rule_partial_order_beginContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_partial_order_begin(ASPCore2Parser::Annotation_global_partial_order_beginContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_partial_order_begin(ASPCore2Parser::Annotation_global_partial_order_beginContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_partial_order(ASPCore2Parser::Annotation_rule_partial_orderContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_partial_order(ASPCore2Parser::Annotation_rule_partial_orderContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_partial_order(ASPCore2Parser::Annotation_global_partial_orderContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_partial_order(ASPCore2Parser::Annotation_global_partial_orderContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_projection(ASPCore2Parser::Annotation_rule_projectionContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_projection(ASPCore2Parser::Annotation_rule_projectionContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_projection_value(ASPCore2Parser::Annotation_rule_projection_valueContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_projection_value(ASPCore2Parser::Annotation_rule_projection_valueContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_rewriting_arith(ASPCore2Parser::Annotation_rule_rewriting_arithContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_rewriting_arith(ASPCore2Parser::Annotation_rule_rewriting_arithContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_align_substitutions(ASPCore2Parser::Annotation_rule_align_substitutionsContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_align_substitutions(ASPCore2Parser::Annotation_rule_align_substitutionsContext * /*ctx*/) override { }

  virtual void enterAnnotation_rule_look_ahead(ASPCore2Parser::Annotation_rule_look_aheadContext * /*ctx*/) override { }
  virtual void exitAnnotation_rule_look_ahead(ASPCore2Parser::Annotation_rule_look_aheadContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_wasp_propagator(ASPCore2Parser::Annotation_global_wasp_propagatorContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_wasp_propagator(ASPCore2Parser::Annotation_global_wasp_propagatorContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_wasp_propagator_begin(ASPCore2Parser::Annotation_global_wasp_propagator_beginContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_wasp_propagator_begin(ASPCore2Parser::Annotation_global_wasp_propagator_beginContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_wasp_heuristic(ASPCore2Parser::Annotation_global_wasp_heuristicContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_wasp_heuristic(ASPCore2Parser::Annotation_global_wasp_heuristicContext * /*ctx*/) override { }

  virtual void enterAnnotation_global_wasp_heuristic_begin(ASPCore2Parser::Annotation_global_wasp_heuristic_beginContext * /*ctx*/) override { }
  virtual void exitAnnotation_global_wasp_heuristic_begin(ASPCore2Parser::Annotation_global_wasp_heuristic_beginContext * /*ctx*/) override { }

  virtual void enterHeuristic_python_file(ASPCore2Parser::Heuristic_python_fileContext * /*ctx*/) override { }
  virtual void exitHeuristic_python_file(ASPCore2Parser::Heuristic_python_fileContext * /*ctx*/) override { }

  virtual void enterAggregate_element_heuristic(ASPCore2Parser::Aggregate_element_heuristicContext * /*ctx*/) override { }
  virtual void exitAggregate_element_heuristic(ASPCore2Parser::Aggregate_element_heuristicContext * /*ctx*/) override { }

  virtual void enterAggregate_elements_heuristic(ASPCore2Parser::Aggregate_elements_heuristicContext * /*ctx*/) override { }
  virtual void exitAggregate_elements_heuristic(ASPCore2Parser::Aggregate_elements_heuristicContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * node) override { 
      if(forbiddenTerminalTypes.count(node->getSymbol()->getType()) != 0){
        std::cout << "Symbol not supported "<< node->getText() << std::endl;
        exit(180);
      }
      if(watchedTerminalTypes.count(node->getSymbol()->getType()) != 0)
        terminals.push_back(node->getText());
      if(node->getSymbol()->getType() == ASPCore2Parser::NAF){
        std::cout << "Found negation"<<std::endl;
        naf=true;
      }
      if(node->getSymbol()->getType() == ASPCore2Parser::AGGR_COUNT || node->getSymbol()->getType() == ASPCore2Parser::AGGR_SUM){
        std::cout << "reading function "<<node->getText()<<std::endl;
        nafAggregate = naf;
      }
      std::cout << "Terminals stack:";
      for(std::string t : terminals) std::cout << " " << t;
      std::cout << std::endl;
  }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { std::cout << "Parsing tree error node"<<std::endl; exit(180);}

};

#endif