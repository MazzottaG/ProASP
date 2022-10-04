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

#ifndef LITERAL_H_ASPC
#define LITERAL_H_ASPC

#include "Atom.h"
#include "Formula.h"

namespace aspc {

    class Literal : public aspc::Formula {
    public:
        Literal(const std::string & predicateName);
        Literal(const std::string & predicateName, bool negated);
        Literal(bool negated, const aspc::Atom & atom);
        Literal(const Literal &);
        Literal();
        virtual ~Literal();

        void negate();
        bool isNegated() const;
        const std::string & getTermAt(unsigned i) const;
        bool isVariableTermAt(unsigned i) const;
        const std::string & getPredicateName() const;
        unsigned getAriety() const;
        const aspc::Atom & getAtom() const;
        const std::vector<std::string>& getTerms() const;
        void setTerms(std::vector<std::string> terms_);
        void setTermAt(int term_index,std::string term_);
        void addTerm(const std::string &);
        bool operator==(const Literal& right) const;
        // TupleWithReasons getTupleWithReasons() const;
        // TupleWithoutReasons getTupleWithoutReasons() const;
        void setNegated(bool);
        std::unordered_set<std::string> getVariables() const;
        bool unifies(const aspc::Literal & right) const;
        bool unifies(const aspc::Atom & right) const;
        std::string getCanonicalRepresentation(const std::unordered_set<std::string> & litBoundVariables) const;
        void transformToCanonicalRep();
        bool isGround() const;

        virtual bool isBoundedRelation(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedLiteral(const std::unordered_set<std::string> &) const override;
        virtual bool isBoundedValueAssignment(const std::unordered_set<std::string> &) const override;
        virtual void addVariablesToSet(std::unordered_set<std::string> &) const override;
        virtual bool isPositiveLiteral() const override;
        virtual void print() const override;
        virtual std::string to_string() const;
        virtual bool isLiteral() const override;
        virtual unsigned firstOccurrenceOfVariableInLiteral(const std::string & v) const override;




    private:
        aspc::Atom atom;
        bool negated;

    };
}

#endif
