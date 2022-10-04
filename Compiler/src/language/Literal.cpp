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

#include "Literal.h"
#include <iostream>
#include <set>

using namespace std;

aspc::Literal::Literal(bool negated, const aspc::Atom & atom) : atom(atom), negated(negated) {
}

aspc::Literal::Literal(const Literal& b): atom(b.atom), negated(b.negated) {

}
aspc::Literal::Literal(const string& predicateName): atom(predicateName), negated(false) {
    
}

aspc::Literal::Literal(const string& predicateName, bool negated): atom(predicateName), negated(negated) {
    
}

aspc::Literal::Literal() {
    
}

void aspc::Literal::addTerm(const string& t) {
    atom.addTerm(t);
}


aspc::Literal::~Literal() {

}

void aspc::Literal::negate() {
    negated = true;
}

bool aspc::Literal::isNegated() const {
    return negated;
}

const string & aspc::Literal::getTermAt(unsigned i) const {
    return atom.getTermAt(i);
}

unsigned aspc::Literal::getAriety() const {
    return atom.getAriety();
}

bool aspc::Literal::isVariableTermAt(unsigned i) const {
    return atom.isVariableTermAt(i);
}

const string & aspc::Literal::getPredicateName() const {
    return atom.getPredicateName();
}

const aspc::Atom & aspc::Literal::getAtom() const {
    return atom;
}

std::string aspc::Literal::to_string() const {
    return (negated ? "not ": "") + atom.toString();
}
void aspc::Literal::print() const {
    if (negated) {
        std::cout << "not ";
    }
    atom.print();
}

const vector<string>& aspc::Literal::getTerms() const {
    return atom.getTerms();
}
void aspc::Literal::setTerms(std::vector<std::string> terms_){
    atom.setTerms(terms_);
}
void aspc::Literal::setTermAt(int term_index,std::string term_){
    atom.setTermAt(term_index,term_);
}

void aspc::Literal::addVariablesToSet(unordered_set<string>& set) const {
    for (unsigned i = 0; i < getAriety(); i++) {
        if (isVariableTermAt(i)) {
            set.insert(getTermAt(i));
        }
    }

}

bool aspc::Literal::isBoundedRelation(const unordered_set<string>&) const {
    return false;
}

bool aspc::Literal::isBoundedLiteral(const unordered_set<string>& set) const {
    for (unsigned i = 0; i < getAriety(); i++) {
        if (isVariableTermAt(i) && !set.count(getTermAt(i))) {
            return false;
        }
    }
    return true;

}

bool aspc::Literal::isBoundedValueAssignment(const unordered_set<string>&) const {
    return false;
}

bool aspc::Literal::isPositiveLiteral() const {
    return !negated;
}

bool aspc::Literal::isLiteral() const {
    return true;
}

unsigned aspc::Literal::firstOccurrenceOfVariableInLiteral(const string & v) const {

    for(unsigned i=0;i<getAriety();i++) {
        if(atom.getTermAt(i)==v) {
            return i;
        }
    }
    return -1;
}

bool aspc::Literal::operator==(const aspc::Literal& right) const {
    return this->atom == right.atom && negated == right.negated;

}

// TupleWithReasons aspc::Literal::getTupleWithReasons() const {
//     return this->atom.getTupleWithReasons(negated);
// }
// TupleWithoutReasons aspc::Literal::getTupleWithoutReasons() const {
//     return this->atom.getTupleWithoutReasons(negated);
    
// }

void aspc::Literal::setNegated(bool negated) {
    this->negated = negated;
}

unordered_set<string> aspc::Literal::getVariables() const {
    unordered_set<string> res;
    for(unsigned i=0;i<getAriety();i++) {
        if(atom.isVariableTermAt(i)) {
            res.insert(atom.getTermAt(i));
        }
    }
    return res;

}

bool aspc::Literal::unifies(const aspc::Atom& right) const {
    
    return atom.unifies(right);
}


bool aspc::Literal::unifies(const aspc::Literal& right) const {
    
    return atom.unifies(right.atom);
}

string aspc::Literal::getCanonicalRepresentation(const unordered_set<string> & litBoundVariables) const {
    string res = "";
    if(negated) {
        res+="not ";
    }
    return res+atom.getCanonicalRepresentation(litBoundVariables);
}

void aspc::Literal::transformToCanonicalRep() {
    atom.transformToCanonicalRep();

}

bool aspc::Literal::isGround() const {
    for(unsigned i = 0; i < getAriety(); i++) {
        if(atom.isVariableTermAt(i)) {
            return false;
        }
    }
    return true;
}
