#ifndef CHOICE_RULE_H
#define CHOICE_RULE_H

#include <vector>
#include "Literal.h"
#include "Atom.h"
#include "ArithmeticRelation.h"
#include "ChoiceElement.h"

namespace aspc{
    class ChoiceRule{
        private:
            std::vector<aspc::ChoiceElement> head;
            std::vector<aspc::Literal> bodyLiterals;
            std::vector<ArithmeticRelation> arithmeticRelations;
            std::vector<const aspc::Formula*> formulas;
            aspc::ArithmeticExpression leftGuard;
            aspc::ComparisonType leftGuardComparisonType;
            aspc::ArithmeticExpression rightGuard;
            aspc::ComparisonType rightGuardComparisonType;

        public:
            ChoiceRule(const aspc::ArithmeticExpression&, const aspc::ArithmeticExpression&, const std::vector<aspc::ChoiceElement>&, const std::vector<aspc::Literal>&, const std::vector<aspc::ArithmeticRelation>&, aspc::ComparisonType, aspc::ComparisonType);
            ChoiceRule(const ChoiceRule&);
            ~ChoiceRule();
            const std::vector<aspc::ChoiceElement>& getHead() const;
            const std::vector<aspc::Literal>& getBodyLiterals() const;
            const std::vector<aspc::ArithmeticRelation>& getArithmeticRelations() const;
            const std::vector<const aspc::Formula*>& getFormulas() const;
            bool isSafe() const;
            const aspc::ArithmeticExpression& getLeftGuard() const;
            const aspc::ArithmeticExpression& getRightGuard() const;
            aspc::ComparisonType getLeftGuardComparisonType() const;
            aspc::ComparisonType getRightGuardComparisonType() const;
            void print() const;
    };
}

#endif /*CHOICE_RULE_H*/