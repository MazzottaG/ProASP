/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
/*
 *
 *  Copyright 2016 Bernardo Cuteri, Francesco Ricca.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

#include "Rule.h"
#include "ArithmeticExpression.h"
#include <iostream>
#include <cassert>
#include <algorithm>

using namespace std;

unsigned aspc::Rule::rulesCounter = 0;
unsigned aspc::Rule::rulesCounterRewriting = 0;
string aspc::Rule::inequalityStrings[] = {">=", "<=", ">", "<", "!=", "=="};

aspc::Rule::Rule(const vector<aspc::Atom> & head, const vector<aspc::Literal> & body, const vector<aspc::ArithmeticRelation> & arithmeticRelations, const vector<aspc::ArithmeticRelationWithAggregate> & arithmeticRelationsWithAggregate,bool rewriting) : head(head), bodyLiterals(body), arithmeticRelations(arithmeticRelations),arithmeticRelationsWithAggregate(arithmeticRelationsWithAggregate),supportAtom(-1) {
    if(rewriting == 0)
        ruleId = rulesCounterRewriting++;
    else
        ruleId = rulesCounter++;
}
aspc::Rule::Rule(const vector<aspc::Atom> & head, const vector<aspc::Literal> & body, const vector<aspc::ArithmeticRelation> & arithmeticRelations, const vector<aspc::ArithmeticRelationWithAggregate> & arithmeticRelationsWithAggregate) : head(head), bodyLiterals(body), ruleId(rulesCounter), arithmeticRelations(arithmeticRelations),arithmeticRelationsWithAggregate(arithmeticRelationsWithAggregate),supportAtom(-1) {
    rulesCounter++;
}

void aspc::Rule::addSharedVars(std::unordered_set<std::string>& bodyVariables,std::vector<std::string>& terms,std::unordered_set<std::string>&distinctTerms,const aspc::ArithmeticRelationWithAggregate* aggr,bool checkGuard) const{
    for(const aspc::Literal& l:aggr->getAggregate().getAggregateLiterals()){
        for(unsigned i=0; i<l.getAriety(); i++){
            std::string v = l.getTermAt(i);
            if(l.isVariableTermAt(i) && bodyVariables.count(v)!=0 && distinctTerms.count(v)==0){
                distinctTerms.insert(v);
                terms.push_back(v);
            }
        }
    }
    for(const aspc::ArithmeticRelation& l:aggr->getAggregate().getAggregateInequalities()){
        
        for(std::string v : l.getLeft().getAllTerms()){
            if(isVariable(v) && bodyVariables.count(v)!=0 && distinctTerms.count(v)==0){
                distinctTerms.insert(v);
                terms.push_back(v);
            }
        }
        
        for(std::string v : l.getRight().getAllTerms()){
            if(isVariable(v) && bodyVariables.count(v)!=0 && distinctTerms.count(v)==0){
                distinctTerms.insert(v);
                terms.push_back(v);
            }
        }
    }
    if(checkGuard){
        for(std::string v : aggr->getGuard().getAllTerms()){
            if(isVariable(v) && bodyVariables.count(v)!=0 && distinctTerms.count(v)==0){
                distinctTerms.insert(v);
                terms.push_back(v);
            }
        }
    }
    
}

void aspc::Rule::addBodyVars(std::unordered_set<std::string>& bodyVars)const{
    for(const aspc::Literal& lit : getBodyLiterals()){
        lit.addVariablesToSet(bodyVars);
    }
    bool added = true;
    while(added){
        added=false;
        for(const aspc::Formula* f : getFormulas()){
            if(!f->isLiteral() && !f->containsAggregate()){
                const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)f;
                if(ineq->isBoundedValueAssignment(bodyVars)){
                    bodyVars.insert(ineq->getAssignedVariable(bodyVars));
                    added=true;
                }
            }
        }
    }
    return;
}
aspc::Rule::Rule(const vector<Atom>& head, const vector<Literal> & body, const vector<aspc::ArithmeticRelation>& arithmeticRelations, bool) : Rule(head, body, arithmeticRelations,std::vector<aspc::ArithmeticRelationWithAggregate>()) {
    //    if(true) {
    //        std::random_shuffle(bodyLiterals.begin(), bodyLiterals.end());
    //        
    //    }
    supportAtom=-1;
    for (unsigned i = 0; i < bodyLiterals.size(); i++) {
        formulas.push_back(new Literal(bodyLiterals.at(i)));

    }
    for (unsigned i = 0; i < arithmeticRelations.size(); i++) {
        formulas.push_back(new ArithmeticRelation(arithmeticRelations[i]));
    }



}
aspc::Rule::Rule(const std::vector<aspc::Atom> & head, const std::vector<aspc::Literal> & body, const std::vector<ArithmeticRelation> & inequalities,const std::vector<ArithmeticRelationWithAggregate> & inequalitiesWithAggregate, bool, bool rewriting): Rule(head, body, inequalities,inequalitiesWithAggregate,rewriting){
    
    
    supportAtom=-1;
    for (unsigned i = 0; i < bodyLiterals.size(); i++) {
        formulas.push_back(new Literal(bodyLiterals.at(i)));

    }
    for (unsigned i = 0; i < arithmeticRelations.size(); i++) {
        formulas.push_back(new ArithmeticRelation(arithmeticRelations[i]));
    }
    
    for (unsigned i = 0; i < arithmeticRelationsWithAggregate.size(); i++) {
        aggregateLiterals.insert(std::pair<unsigned,std::vector<Literal*>>(formulas.size(),std::vector<Literal*>()));
        for(unsigned j = 0; j< arithmeticRelationsWithAggregate[i].getAggregate().getAggregateLiterals().size();j++){
            aggregateLiterals[formulas.size()].push_back(new aspc::Literal(arithmeticRelationsWithAggregate[i].getAggregate().getAggregateLiterals()[j]));
        }
        arithmeticRelationsWithAggregate[i].setFormulaIndex(formulas.size());
        formulas.push_back(new ArithmeticRelationWithAggregate(arithmeticRelationsWithAggregate[i]));
        ((ArithmeticRelationWithAggregate*)formulas.back())->computeJoinTupleName();
        //((ArithmeticRelationWithAggregate*)formulas[formulas.size()-1])->setFormulaIndex(formulas.size()-1);
    }

}


bool aspc::Rule::equalBodyExpect(const aspc::Rule& other,const std::unordered_set<std::string>& forbidden){
    if(bodyLiterals.size()!=other.bodyLiterals.size()) return false;
    if(arithmeticRelations.size() != other.arithmeticRelations.size()) return false;
    //TODO: Add Aggregates
    //TODO: Add check on duplicated literals or ineqs
    // We assume no duplicated literals or ineqs
    for(const aspc::Literal& lit : bodyLiterals){
        if(forbidden.count(lit.getPredicateName())) continue;
        bool found = false;
        for(const aspc::Literal& lit1 : other.bodyLiterals){
            if(lit == lit1){found = true; break;}
        }
        if(!found) return false;
    }
    for(const aspc::ArithmeticRelation& ineq : arithmeticRelations){
        bool found = false;
        for(const aspc::ArithmeticRelation& ineq1 : other.arithmeticRelations){
            if(ineq == ineq1){found = true; break;}
        }
        if(!found) return false;
    }
    return true;
}
aspc::Rule::Rule(const Rule& other) :
head(other.head), bodyLiterals(other.bodyLiterals), ruleId(other.ruleId), arithmeticRelations(other.arithmeticRelations),arithmeticRelationsWithAggregate(other.arithmeticRelationsWithAggregate), orderedBodyByStarters(other.orderedBodyByStarters), orderedBodyIndexesByStarters(other.orderedBodyIndexesByStarters) {
    for (unsigned i = 0; i < bodyLiterals.size(); i++) {
        formulas.push_back(new Literal(bodyLiterals.at(i)));

    }
    for (unsigned i = 0; i < arithmeticRelations.size(); i++) {
        formulas.push_back(new ArithmeticRelation(arithmeticRelations[i]));
    }
    for (unsigned i = 0; i < arithmeticRelationsWithAggregate.size(); i++) {
        aggregateLiterals.insert(std::pair<unsigned,std::vector<Literal*>>(formulas.size(),std::vector<Literal*>()));
        for(unsigned j = 0; j< arithmeticRelationsWithAggregate[i].getAggregate().getAggregateLiterals().size();j++){
            aggregateLiterals[formulas.size()].push_back(new aspc::Literal(arithmeticRelationsWithAggregate[i].getAggregate().getAggregateLiterals()[j]));
        }
        formulas.push_back(new ArithmeticRelationWithAggregate(arithmeticRelationsWithAggregate[i]));
    }
    supportAtom=other.supportAtom;
}

aspc::Rule::~Rule() {

    for (const Formula* f : formulas) {
        delete f;
    }
    for (std::pair<unsigned,std::vector<aspc::Literal*>> pair:aggregateLiterals){
        for(aspc::Literal* l : pair.second){
            delete l;
        }
    }
}

const vector<aspc::Literal> & aspc::Rule::getBodyLiterals() const {
    return bodyLiterals;
}

const vector<aspc::Atom> & aspc::Rule::getHead() const {
    return head;
}

RuleType aspc::Rule::getType() const {
    if (head.empty()) {
        return CONSTRAINT;
    }
    return GENERATIVE_RULE;
}

unsigned aspc::Rule::getRuleId() const {
    return ruleId;
}

unsigned aspc::Rule::getBodySize() const {
    return formulas.size();
}
void aspc::Rule::addBodyLiteral(aspc::Literal l){
    bodyLiterals.push_back(aspc::Literal(l));
    formulas.push_back(new aspc::Literal(l));
}
vector<map<unsigned, pair<unsigned, unsigned> > > aspc::Rule::getJoinIndicesWithJoinOrder(const vector<unsigned>& order) const {
    vector<map<unsigned, pair<unsigned, unsigned> > > result(order.size() - 1);
    unsigned orderSize = order.size();
    //for all other atom X (in order)
    for (unsigned i = 0; i < orderSize - 1; i++) {
        unsigned o_i = order[i + 1];
        //for all term T1 in X
        if (formulas[o_i]->isLiteral()) {
            Literal *literal = (Literal *) formulas[o_i];
            for (unsigned t1 = 0; t1 < literal->getAriety(); t1++) {
                //for all atom Y preceding X in the join
                for (unsigned j = 0; j <= i; j++) {
                    unsigned o_j = order[j];
                    //for all term T2 in Y
                    if (formulas[o_j]->isLiteral()) {
                        Literal *literal2 = (Literal *) formulas[o_j];
                        for (unsigned t2 = 0; t2 < literal2->getAriety(); t2++) {
                            if (!literal2->isNegated() && literal->isVariableTermAt(t1) && literal->getTermAt(t1) == literal2->getTermAt(t2)) {
                                pair<unsigned, unsigned> toAdd(j, t2);
                                result[i][t1] = toAdd;
                            }
                        }
                    }
                }
            }
        }
    }
    return result;
}

map<unsigned, pair<unsigned, unsigned> > aspc::Rule::getBodyToHeadVariablesMap() const {
    //TODO handle disjunction, j can only be 0 
    map<unsigned, pair<unsigned, unsigned> > resultMap;
    const Atom & headAtom = head.front();
    for (unsigned t1 = 0; t1 < headAtom.getAriety(); t1++) {
        if (headAtom.isVariableTermAt(t1)) {
            for (unsigned i = 0; i < formulas.size(); i++) {
                if (formulas[i]->isLiteral()) {
                    Literal* bodyLiteral = (Literal*) formulas[i];
                    if (!bodyLiteral->isNegated()) {
                        for (unsigned t2 = 0; t2 < bodyLiteral->getAriety(); t2++) {
                            if (bodyLiteral->getTermAt(t2) == headAtom.getTermAt(t1)) {
                                pair<unsigned, unsigned> toAddPair(i, t2);
                                resultMap[t1] = toAddPair;
                            }
                        }
                    }
                }
            }
        }
    }
    return resultMap;
}
void aspc::Rule::updateJoinTupleName(unsigned int formulaIndex,std::string joinTupleName){
    ((aspc::ArithmeticRelationWithAggregate*) formulas[formulaIndex])->setJoinTupleName(joinTupleName);
    for(aspc::ArithmeticRelationWithAggregate& ar : arithmeticRelationsWithAggregate){
        if(ar.getFormulaIndex() == formulaIndex)
            ar.setJoinTupleName(joinTupleName);
    }
}
const vector<aspc::ArithmeticRelation> & aspc::Rule::getArithmeticRelations() const {
    return arithmeticRelations;
}

const vector<aspc::ArithmeticRelationWithAggregate> & aspc::Rule::getArithmeticRelationsWithAggregate() const {
    return arithmeticRelationsWithAggregate;
}
void aspc::Rule::print() const {
    for (const Atom & atom : head) {
        atom.print();
        std::cout << " ";
    }
    std::cout << ":-";
    for (const Formula* f : formulas) {
        f->print();
        cout << " ";
    }
    cout << endl;
    //    for (const aspc::Literal & literal : bodyLiterals) {
    //        literal.print();
    //        cout << " ";
    //    }
    //    for (const ArithmeticRelation & arithmeticRelation : arithmeticRelations) {
    //        arithmeticRelation.print();
    //        cout << " ";
    //    }
    //    cout << "\n";
}

bool aspc::Rule::containsNegation() const {
    for (unsigned i = 0; i < bodyLiterals.size(); i++) {
        if (bodyLiterals[i].isNegated()) {
            return true;
        }
    }
    return false;
}
bool aspc::Rule::containsAggregate() const{
    return !arithmeticRelationsWithAggregate.empty();
}
        
bool aspc::Rule::containsLiteral() const{
    return !bodyLiterals.empty();
}

bool aspc::Rule::isConstraint() const {
    return getType() == CONSTRAINT;
}

void aspc::Rule::bodyReordering() {
    vector<unsigned> starters;
    for (unsigned i = 0; i < formulas.size(); i++) {
        if (formulas[i]->isPositiveLiteral()) {
            starters.push_back(i);
            break;
        }
    }
    //needed for eager
    // if (isConstraint()) {
        starters.push_back(formulas.size());
    // }
    bodyReordering(starters);
}
/*
std::string getFresh(const std::unordered_set<std::string>& forbidden,unsigned& index){
    std::string remapped_var = "X_"+std::to_string(index);
    while(forbidden.count(remapped_var) == 1){
        index++;
        remapped_var = "X_"+std::to_string(index);
    }
    return remapped_var;
}
*/
aspc::Rule aspc::Rule::cloneWithRenamedVariables(const std::unordered_map<std::string,std::string>& mapping) const{
    std::vector<aspc::Atom> remappedHead;
    if(!isConstraint()){
        std::vector<std::string> freshHeadTerms;
        const aspc::Atom* head_atom = &getHead()[0];
        for(unsigned k=0;k<head_atom->getAriety();k++){
            if(head_atom->isVariableTermAt(k)){
                auto it = mapping.find(head_atom->getTermAt(k));
                std::string mappedVar = it != mapping.end() ? it->second : head_atom->getTermAt(k);
                freshHeadTerms.push_back(mappedVar);
            }else{
                freshHeadTerms.push_back(head_atom->getTermAt(k));
            }
        }
        remappedHead.push_back(aspc::Atom(head_atom->getPredicateName(),freshHeadTerms));
    }
    std::vector<aspc::Literal> remappedLiterals;
    std::vector<aspc::ArithmeticRelation> remappedIneqs;
    for(const aspc::Formula* f : formulas){
        if(f->isLiteral()){
            const aspc::Literal* literal = (const aspc::Literal*)f;
            std::vector<std::string> freshLitTerms;
            for(unsigned k=0;k<literal->getAriety();k++){
                if(literal->isVariableTermAt(k)){
                    auto it = mapping.find(literal->getTermAt(k));
                    std::string mappedVar = it != mapping.end() ? it->second : literal->getTermAt(k);
                    freshLitTerms.push_back(mappedVar);
                }else{
                    freshLitTerms.push_back(literal->getTermAt(k));
                }
            }
            remappedLiterals.push_back(aspc::Literal(literal->isNegated(),aspc::Atom(literal->getPredicateName(),freshLitTerms)));
        } else if(!f->containsAggregate()){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*)f;
            std::vector<aspc::ArithmeticExpression> right_left;
            for(aspc::ArithmeticExpression exp : {ineq->getRight(),ineq->getLeft()}){
                std::string term_1=exp.getTerm1();
                std::string remapped_term_1 = term_1;
                if(isVariable(term_1)){
                    auto it = mapping.find(term_1);
                    remapped_term_1 = it != mapping.end() ? it->second : term_1;
                }
                bool singleTerm = exp.isSingleTerm();
                std::string term_2 = singleTerm ? "" : exp.getTerm2();
                std::string remapped_term_2 = term_2;
                if(!singleTerm && isVariable(term_1)){
                    auto it = mapping.find(term_2);
                    remapped_term_2 = it != mapping.end() ? it->second : term_2;
                }
                char op = singleTerm ? '?' : exp.getOperation();
                right_left.push_back(singleTerm ? aspc::ArithmeticExpression(remapped_term_1) : aspc::ArithmeticExpression(remapped_term_1,remapped_term_2,op));
            }
            remappedIneqs.push_back(aspc::ArithmeticRelation(right_left[1],right_left[0],ineq->getComparisonType()));
        }else{
            std::cout << "Error: remapping with aggregate not supported yet"<<std::endl;
            exit(180);
        }
    }
    return aspc::Rule(remappedHead,remappedLiterals,remappedIneqs,false);
}
void aspc::Rule::addPositiveBodyVariablesToSet(std::unordered_set<std::string> & set) const {
    for(const aspc::Literal& l : getBodyLiterals()){
        if(l.isNegated()) continue;
        l.addVariablesToSet(set);
    }
    bool added=true;
    while(added){
        added=false;
        for(const aspc::ArithmeticRelation& ineq: getArithmeticRelations()){
            if(ineq.isBoundedValueAssignment(set)){
                std::string var = ineq.getAssignedVariable(set);
                auto it = set.emplace(var);
                if(it.second)
                    added=true;
            }
        }
    }
}
void aspc::Rule::orderBodyFormulasFromStarter(unsigned starter, std::vector<unsigned>& orderedBodyFormulas)const{
    std::unordered_set<std::string> boundVariables;
    std::unordered_set<unsigned> selectedFormulas;
    if(starter<formulas.size())
        formulas[starter]->addVariablesToSet(boundVariables);
    int size = formulas.size()==starter ? formulas.size() : formulas.size()-1;
    while(orderedBodyFormulas.size()<size){
        unsigned selectedIndex=-1;
        bool isPositiveLiteralSelected=false;
        bool isBoundedValueAssignmentSelected=false;
        bool isAggregateRelationSelected=false;
        for(unsigned i=0; i<formulas.size();i++){
            if(i==starter)
                continue;
            if(selectedFormulas.count(i)==0){
                const aspc::Formula* f = formulas[i];
                if(!f->containsAggregate()){
                    if(f->isBoundedRelation(boundVariables) || f->isBoundedLiteral(boundVariables)){
                        selectedIndex=i;
                        break;
                    }else if(f->isBoundedValueAssignment(boundVariables)){
                        if(!isBoundedValueAssignmentSelected){
                            isBoundedValueAssignmentSelected=true;
                            selectedIndex=i;
                        }
                    }else if(f->isPositiveLiteral()){
                        if(!isPositiveLiteralSelected && !isBoundedValueAssignmentSelected){
                            selectedIndex=i;
                            isPositiveLiteralSelected=true;
                        }
                    }
                }else if(f->isBoundedValueAssignment(boundVariables) || f->isBoundedRelation(boundVariables)){
                    if(!isPositiveLiteralSelected && !isBoundedValueAssignmentSelected && !isAggregateRelationSelected){
                        selectedIndex=i;
                        isAggregateRelationSelected=true;
                    }
                }
                
            }
        }
        if(selectedIndex==-1){
            std::cout << "Error:\tUnable to order rule ";print();
            exit(180);
        }
        selectedFormulas.insert(selectedIndex);
        orderedBodyFormulas.push_back(selectedIndex);
        formulas[selectedIndex]->addVariablesToSet(boundVariables);
    }
    // for(unsigned i=0; i<formulas.size();i++){
    //     if(formulas[i]->containsAggregate()){
    //         if(selectedFormulas.count(i)==0){
    //             selectedFormulas.insert(i);
    //             orderedBodyFormulas.push_back(i);
    //         }
    //     }
    // }
    
}

bool aspc::Rule::extractLabeledFormula(const std::vector<int>& formulaLabeling, std::unordered_map<std::string,int>& predToComponent, const std::vector<int>& sccLabel,int label,std::vector<bool>& extraction,std::unordered_set<std::string>& positiveEDBVar)const{
    int countExtractedLiteral = 0;
    std::unordered_set<std::string> negativeEDBVar;
    std::unordered_set<std::string> originalBodyVars;
    for(unsigned fIndex = 0; fIndex < formulas.size(); fIndex++){
        const aspc::Formula* f = formulas[fIndex];
        if(f->isLiteral()){
            const aspc::Literal* literal = (const aspc::Literal*) f;
            int component = predToComponent[literal->getPredicateName()];
            if(sccLabel[component] == label){
                extraction[fIndex] = true;
                countExtractedLiteral++;
                literal->addVariablesToSet(literal->isPositiveLiteral() ? positiveEDBVar: negativeEDBVar);
            }
            literal->addVariablesToSet(originalBodyVars);
        }
    }
    std::cout << "Found "<<countExtractedLiteral<<" for rule ";print();

    bool newVar=true;
    while(newVar){
        newVar=false;
        for(unsigned fIndex = 0; fIndex < formulas.size(); fIndex++){
            const aspc::Formula* f = formulas[fIndex];
            if(!f->isLiteral() && !f->containsAggregate()){
                const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) f;
                if(ineq->isBoundedValueAssignment(positiveEDBVar)){
                    std::string var = ineq->getAssignedVariable(positiveEDBVar);
                    if(negativeEDBVar.count(var) && !positiveEDBVar.count(var)){
                        extraction[fIndex] = true;
                        positiveEDBVar.insert(var);
                        newVar=true;
                    }
                }
            }
        }
    }
    for(unsigned fIndex = 0; fIndex < formulas.size(); fIndex++){
        const aspc::Formula* f = formulas[fIndex];
        if(f->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* ineq = (const aspc::ArithmeticRelationWithAggregate*) f;
            if(formulaLabeling[fIndex] == label){
                bool extractAggr=true;
                for(const aspc::Literal& lit : ineq->getAggregate().getAggregateLiterals()){
                    for(unsigned k=0;k<lit.getAriety(); k++){
                        if(lit.isVariableTermAt(k) && originalBodyVars.count(lit.getTermAt(k)) != 0 && positiveEDBVar.count(lit.getTermAt(k)) == 0){
                            extractAggr=false;
                        }
                    }
                }    
                if(extractAggr){
                    for(const aspc::ArithmeticRelation& rel : ineq->getAggregate().getAggregateInequalities()){
                        for(const aspc::ArithmeticExpression& exp: {rel.getLeft(),rel.getRight()} ){
                            for(std::string term : exp.getAllTerms()){
                                if(originalBodyVars.count(term)!=0 && positiveEDBVar.count(term)==0)
                                    extractAggr=false;
                            }
                        }
                    }
                    if(extractAggr){
                        for(std::string term : ineq->getGuard().getAllTerms()){
                            if(originalBodyVars.count(term)!=0 && positiveEDBVar.count(term)==0)
                                extractAggr=false;
                        }
                    }
                }
                if(extractAggr){
                    extraction[fIndex]=true; 
                    countExtractedLiteral++;  
                    std::cout << "Extracting aggregate"<<std::endl;
                }
            }else{
                extraction[fIndex]=false;
            }
        }
    }
    for(unsigned fIndex = 0; fIndex < formulas.size(); fIndex++){
        const aspc::Formula* f = formulas[fIndex];
        if(!f->isLiteral()){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) f;
            if(ineq->isBoundedRelation(positiveEDBVar)){
                extraction[fIndex] = true;
            }
        }else if(!f->isPositiveLiteral() && !f->isBoundedLiteral(positiveEDBVar))
            return false;
    }
    return countExtractedLiteral>=2;
}
void aspc::Rule::orderBodyFormulas(std::vector<unsigned>& orderedBodyFormulas)const{
    std::unordered_set<std::string> boundVariables;
    std::unordered_set<unsigned> selectedFormulas;
    while(orderedBodyFormulas.size()<formulas.size()){
        unsigned selectedIndex=-1;
        bool isPositiveLiteralSelected=false;
        bool isBoundedValueAssignmentSelected=false;
        bool isAggregateRelationSelected=false;
        for(unsigned i=0; i<formulas.size();i++){
            if(selectedFormulas.count(i)==0){
                const aspc::Formula* f = formulas[i];
                if(!f->containsAggregate()){
                    if(f->isBoundedRelation(boundVariables) || f->isBoundedLiteral(boundVariables)){
                        selectedIndex=i;
                        break;
                    }else if(f->isBoundedValueAssignment(boundVariables)){
                        if(!isBoundedValueAssignmentSelected){
                            isBoundedValueAssignmentSelected=true;
                            selectedIndex=i;
                        }
                    }else if(f->isPositiveLiteral()){
                        if(!isPositiveLiteralSelected && !isBoundedValueAssignmentSelected){
                            selectedIndex=i;
                            isPositiveLiteralSelected=true;
                        }
                    }
                }else if(f->isBoundedValueAssignment(boundVariables) || f->isBoundedRelation(boundVariables)){
                    if(!isPositiveLiteralSelected && !isBoundedValueAssignmentSelected && !isAggregateRelationSelected){
                        selectedIndex=i;
                        isAggregateRelationSelected=true;
                    }
                }
                
            }
        }
        if(selectedIndex==-1){
            std::cout << "Error:\tUnable to order rule ";print();
            exit(180);
        }
        selectedFormulas.insert(selectedIndex);
        orderedBodyFormulas.push_back(selectedIndex);
        formulas[selectedIndex]->addVariablesToSet(boundVariables);
    }
    // for(unsigned i=0; i<formulas.size();i++){
    //     if(formulas[i]->containsAggregate()){
    //         if(selectedFormulas.count(i)==0){
    //             selectedFormulas.insert(i);
    //             orderedBodyFormulas.push_back(i);
    //         }
    //     }
    // }
    
}
void aspc::Rule::addArithmeticRelationsWithAggregate(ArithmeticRelationWithAggregate r){
    arithmeticRelationsWithAggregate.push_back(r);
}
        
void aspc::Rule::bodyReordering(const vector<unsigned>& starters) {
    if (starters.empty()) {
        bodyReordering();
    }
    // std::cout<<"BodyReordering"<<std::endl;
    // print();
    for (unsigned starter : starters) {
        unordered_set<string> boundVariables;
        if(starter < formulas.size()){
            // std::cout<<"Ordering starting from: ";
            // formulas[starter]->print();
            // std::cout<<std::endl;
        }
        
        if (starter < formulas.size()) {
            formulas[starter]->addVariablesToSet(boundVariables);
            orderedBodyByStarters[starter].push_back(formulas[starter]);
            orderedBodyIndexesByStarters[starter].push_back(starter);
        }else if(starter>formulas.size() && !isConstraint()){
            for(unsigned k = 0; k < head[0].getAriety(); k++){
                if(head[0].isVariableTermAt(k)){
                    boundVariables.insert(head[0].getTermAt(k));
                }
            }
        }

        list<const Formula*> allFormulas;
        //TODO improve
        for (const Formula* f : formulas) {
            
            if (starter == formulas.size() || f != formulas[starter]) {
                allFormulas.push_back(f);
            }
        }
        
        while (!allFormulas.empty()) {
            const Formula* boundExpression = NULL;
            const Formula* boundLiteral = NULL;
            const Formula* boundValueAssignment = NULL;
            const Formula* positiveLiteral = NULL;
            const Formula* aggregate = NULL;
            const Formula* selectedFormula = NULL;

            for (list<const Formula*>::const_reverse_iterator formula = allFormulas.rbegin(); formula != allFormulas.rend(); formula++) {
                if ((*formula)->isBoundedRelation(boundVariables) && !(*formula)->containsAggregate()) {
                    boundExpression = *formula;
                } else if ((*formula)->isBoundedValueAssignment(boundVariables)) {
                    boundValueAssignment = *formula;
                } else if ((*formula)->isBoundedLiteral(boundVariables)) {
                    boundLiteral = *formula;
                } else if ((*formula)->isPositiveLiteral()) {
                    positiveLiteral = *formula;
                } else if ((*formula)->containsAggregate()){
                    aggregate = *formula;
                }
                
            }


            if (boundExpression) {
                selectedFormula = boundExpression;
            } else if (boundValueAssignment) {
                selectedFormula = boundValueAssignment;
            } else if (boundLiteral) {
                selectedFormula = boundLiteral;
            } else if(positiveLiteral){
                selectedFormula = positiveLiteral;
            } else if(aggregate){
                selectedFormula=aggregate;
            }
            
            assert(selectedFormula);
            if (selectedFormula != boundExpression && selectedFormula != boundLiteral) {
                selectedFormula->addVariablesToSet(boundVariables);
            }
            orderedBodyByStarters[starter].push_back(selectedFormula);

            // TODO remove
            unsigned selectedIndex = 0;
            for (const Formula* f : formulas) {
                if (f == selectedFormula) {
                    break;
                }
                selectedIndex++;
            }
            orderedBodyIndexesByStarters[starter].push_back(selectedIndex);
            allFormulas.remove(selectedFormula);
        }
        // for(const aspc::Formula* f: orderedBodyByStarters[starter]){
        //     f->print();
        //     std::cout<<" ";
        // }
        // std::cout<<std::endl;

    }

    //for(unsigned i : orderedBodyIndexesByStarters[formulas.size()]){
    //    formulas[i]->print();
    //}

}

//TODO remove duplication: duplicated because value invention is treated as check for reasons building

vector<const aspc::Formula*> aspc::Rule::getOrderedBodyForReasons(unordered_set<string> boundVariables) const {

    vector<const Formula*> res;
    list<const Formula*> allFormulas;
    //TODO improve
    for (const Formula* f : formulas) {
        allFormulas.push_back(f);
    }
    while (!allFormulas.empty()) {
        const Formula* boundExpression = NULL;
        const Formula* boundLiteral = NULL;
        const Formula* boundValueAssignment = NULL;
        const Formula* positiveLiteral = NULL;
        const Formula* selectedFormula = NULL;

        for (list<const Formula*>::reverse_iterator formula = allFormulas.rbegin(); formula != allFormulas.rend(); formula++) {
            if ((*formula)->isBoundedRelation(boundVariables)) {
                boundExpression = *formula;
            } else if ((*formula)->isBoundedValueAssignment(boundVariables)) {
                boundValueAssignment = *formula;
            } else if ((*formula)->isBoundedLiteral(boundVariables)) {
                boundLiteral = *formula;
            } else if ((*formula)->isPositiveLiteral()) {
                positiveLiteral = *formula;
            }
        }

        if (boundExpression) {
            selectedFormula = boundExpression;
        } else if (boundValueAssignment) {
            selectedFormula = boundValueAssignment;
        } else if (boundLiteral) {
            selectedFormula = boundLiteral;
        } else {
            selectedFormula = positiveLiteral;
        }
        assert(selectedFormula);
        if (selectedFormula != boundExpression && selectedFormula != boundLiteral) {
            selectedFormula->addVariablesToSet(boundVariables);
        }

        res.push_back(selectedFormula);

        allFormulas.remove(selectedFormula);
    }
    return res;
}

void aspc::Rule::printOrderedBodies() const {

    for (const auto& entry : orderedBodyByStarters) {
        for (const Formula* f : entry.second) {
            f->print();
            cout << " ";
        }
        cout << endl;
    }
    cout << endl;

}

pair<int, int> aspc::Rule::findFirstOccurrenceOfVariableByStarter(const string& var, unsigned starter) const {

    for (unsigned i = 0; i < orderedBodyByStarters.at(starter).size(); i++) {
        if (orderedBodyByStarters.at(starter)[i]->isLiteral()) {
            int index = orderedBodyByStarters.at(starter)[i]->firstOccurrenceOfVariableInLiteral(var);
            if (index != -1) {
                return pair<int, int>(i, index);
            }
        }
    }
    return pair<int, int>(-1, -1);
}

const vector<unsigned>& aspc::Rule::getOrderedBodyIndexesByStarter(unsigned start) const {
    return orderedBodyIndexesByStarters.at(start);
}

const vector<const aspc::Formula*> & aspc::Rule::getFormulas() const {
    return formulas;
}

const vector<const aspc::Formula*>& aspc::Rule::getOrderedBodyByStarter(unsigned start) const {
    return orderedBodyByStarters.at(start);
}

vector<unsigned> aspc::Rule::getStarters() const {
    vector<unsigned> res;
    for (const auto & entry : orderedBodyByStarters) {
        res.push_back(entry.first);
        
    }
    return res;


}
