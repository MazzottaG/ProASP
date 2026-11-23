#ifndef CHOICE_ELEMENT_H
#define CHOICE_ELEMENT_H

#include <vector>
#include "Atom.h"
#include "Literal.h"
#include "ArithmeticRelation.h"

namespace aspc{
    class ChoiceElement{
        private:
            Atom atom;
            std::vector<Literal> bodyLiterals;
            std::vector<const aspc::Formula*> formulas;
            std::vector<aspc::ArithmeticRelation> arithmeticRelations;
        
        public:
            ChoiceElement(const Atom&, const std::vector<Literal>& body, const std::vector<ArithmeticRelation>&);
            ChoiceElement(const ChoiceElement&);
            ~ChoiceElement();
            const aspc::Atom& getAtom() const;
            const std::vector<const aspc::Formula*> & getFormulas() const;
            const std::vector<Literal>& getBodyLiterals() const;
            const std::vector<ArithmeticRelation> & getArithmeticRelations() const;
            void print() const;
    };

}

#endif /*CHOICE_ELEMENT_H*/