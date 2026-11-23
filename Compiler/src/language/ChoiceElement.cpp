#include "ChoiceElement.h"

aspc::ChoiceElement::ChoiceElement(const Atom& atom, const std::vector<Literal>& bodyLiterals, const std::vector<ArithmeticRelation>& arithmeticRelations) : atom(atom), bodyLiterals(bodyLiterals), arithmeticRelations(arithmeticRelations){
    for(const aspc::Literal& lit : bodyLiterals){
        formulas.push_back(new aspc::Literal(lit));
    }
    for(const aspc::ArithmeticRelation& rel : arithmeticRelations){
        formulas.push_back(new aspc::ArithmeticRelation(rel));
    }
}

aspc::ChoiceElement::ChoiceElement(const ChoiceElement& other) : atom(other.atom), bodyLiterals(other.bodyLiterals), arithmeticRelations(other.arithmeticRelations){
    for(const aspc::Literal& lit : bodyLiterals){
        formulas.push_back(new aspc::Literal(lit));
    }
    for(const aspc::ArithmeticRelation& rel : arithmeticRelations){
        formulas.push_back(new aspc::ArithmeticRelation(rel));
    }
}

aspc::ChoiceElement::~ChoiceElement(){
    for(const Formula* f : formulas)
        delete f;
}

const aspc::Atom& aspc::ChoiceElement::getAtom() const{
    return atom;
}

const std::vector<const aspc::Formula*> & aspc::ChoiceElement::getFormulas() const{
    return formulas;
}

const std::vector<aspc::Literal>& aspc::ChoiceElement::getBodyLiterals() const{
    return bodyLiterals;
}

const std::vector<aspc::ArithmeticRelation> & aspc::ChoiceElement::getArithmeticRelations() const{
    return arithmeticRelations;
}

void aspc::ChoiceElement::print() const{
    atom.print();
    if(formulas.size() > 0)
        std::cout << " : ";
    for(const aspc::Formula* f : formulas){
        f->print();
        std::cout <<" ";
    }
}

