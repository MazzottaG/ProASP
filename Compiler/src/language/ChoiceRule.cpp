#include "ChoiceRule.h"

aspc::ChoiceRule::ChoiceRule(const aspc::ArithmeticExpression& leftGuard, const aspc::ArithmeticExpression& rightGuard, const std::vector<aspc::ChoiceElement>& head, const std::vector<aspc::Literal>& bodyLiterals, const std::vector<aspc::ArithmeticRelation>& arithmeticRelations, aspc::ComparisonType leftGuardComparisonType, aspc::ComparisonType rightGuardComparisonType): leftGuard(leftGuard), rightGuard(rightGuard), head(head), bodyLiterals(bodyLiterals), arithmeticRelations(arithmeticRelations), leftGuardComparisonType(leftGuardComparisonType), rightGuardComparisonType(rightGuardComparisonType){
    std::cout <<"Left comparison type: " << leftGuardComparisonType << "\n";
    std::cout <<"Right comparison type: " << rightGuardComparisonType << "\n";
    for(const aspc::Literal& lit : bodyLiterals){
        formulas.push_back(new aspc::Literal(lit));
    }
    for(const aspc::ArithmeticRelation& rel : arithmeticRelations){
        formulas.push_back(new aspc::ArithmeticRelation(rel));
    }
}

aspc::ChoiceRule::ChoiceRule(const aspc::ChoiceRule& other) : leftGuard(other.leftGuard), rightGuard(other.rightGuard), head(other.head), bodyLiterals(other.bodyLiterals), arithmeticRelations(other.arithmeticRelations), leftGuardComparisonType(other.leftGuardComparisonType), rightGuardComparisonType(other.rightGuardComparisonType){
    for(const aspc::Literal& lit : bodyLiterals){
        formulas.push_back(new aspc::Literal(lit));
    }
    for(const aspc::ArithmeticRelation& rel : arithmeticRelations){
        formulas.push_back(new aspc::ArithmeticRelation(rel));
    }
}

aspc::ChoiceRule::~ChoiceRule(){
    for(const Formula* f : formulas){
        delete f;
    }
}

const std::vector<aspc::ChoiceElement>& aspc::ChoiceRule::getHead() const{
    return head;
}

const std::vector<aspc::Literal>& aspc::ChoiceRule::getBodyLiterals() const{
    return bodyLiterals;
}

const std::vector<aspc::ArithmeticRelation>& aspc::ChoiceRule::getArithmeticRelations() const{
    return arithmeticRelations;
}

const std::vector<const aspc::Formula*>& aspc::ChoiceRule::getFormulas() const{
    return formulas;
}

bool aspc::ChoiceRule::isSafe() const{
    std::unordered_set<std::string> positiveBodyVars;
    std::unordered_set<std::string> negativeBodyVars;
    //check body safety
    for(const Literal& l : bodyLiterals){
        if(!l.isNegated())
            l.addVariablesToSet(positiveBodyVars);
        else
            l.addVariablesToSet(negativeBodyVars);
    }
    bool added;
    do{
        added = false;
        for(int i = 0; i < arithmeticRelations.size(); ++i){
            const ArithmeticRelation& rel = arithmeticRelations.at(i);
            if(rel.isBoundedValueAssignment(positiveBodyVars)){
                positiveBodyVars.insert(rel.getAssignedVariable(positiveBodyVars));
                added = true;
            }
        }
    }while(added);
    
    for(const std::string& var : negativeBodyVars)
        if(positiveBodyVars.count(var) == 0)
            return false;
    
    //check choice elements safety
    for(unsigned i = 0; i < head.size(); ++i){
        std::unordered_set<std::string> positiveBodyVarsChoiceElem(positiveBodyVars);
        std::unordered_set<std::string> negativeBodyVarsChoiceElem;

        const ChoiceElement& elem = head.at(i);
        for(unsigned i = 0; i < elem.getAtom().getTermsSize(); ++i)
            if(elem.getAtom().isVariableTermAt(i))
                negativeBodyVarsChoiceElem.insert(elem.getAtom().getTermAt(i));

        for(const Literal& l : elem.getBodyLiterals()){
            if(!l.isNegated())
                l.addVariablesToSet(positiveBodyVarsChoiceElem);
            else
                l.addVariablesToSet(negativeBodyVarsChoiceElem);
        }

        bool added;
        do{
            added = false;
            for(int i = 0; i < elem.getArithmeticRelations().size(); ++i){
                const ArithmeticRelation& rel = elem.getArithmeticRelations().at(i);
                if(rel.isBoundedValueAssignment(positiveBodyVarsChoiceElem)){
                    positiveBodyVarsChoiceElem.insert(rel.getAssignedVariable(positiveBodyVarsChoiceElem));
                    added = true;
                }
            }
        }while(added);

        for(const std::string& var : negativeBodyVarsChoiceElem)
            if(positiveBodyVarsChoiceElem.count(var) == 0)
                return false;
    }
    return true;
}

const aspc::ArithmeticExpression& aspc::ChoiceRule::getLeftGuard() const{
    return leftGuard;
}

const aspc::ArithmeticExpression& aspc::ChoiceRule::getRightGuard() const{
    return rightGuard;
}

aspc::ComparisonType aspc::ChoiceRule::getLeftGuardComparisonType() const{
    return leftGuardComparisonType;
}

aspc::ComparisonType aspc::ChoiceRule::getRightGuardComparisonType() const{
    return rightGuardComparisonType;
}

void aspc::ChoiceRule::print() const{
    if(leftGuardComparisonType != aspc::ComparisonType::UNASSIGNED){
        std::cout << leftGuard << " " << aspc::ArithmeticRelation::comparisonType2String[leftGuardComparisonType];
    }
    std::cout <<"{ ";
    for(unsigned i = 0; i < head.size(); ++i){
        head.at(i).print();
        if(i != head.size()-1)
            std::cout <<" ; ";
    }
    std::cout <<"}";
    if(rightGuardComparisonType != aspc::ComparisonType::UNASSIGNED){
        std::cout << " " << aspc::ArithmeticRelation::comparisonType2String[rightGuardComparisonType] << " " << rightGuard;
    }

    if (formulas.size() != 0)
        std::cout <<":-";
    for(const Formula* f : formulas)
        f->print();
    std::cout <<"."<<std::endl;
}