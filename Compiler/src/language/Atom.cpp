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

#include "Atom.h"
#include "../utils/ConstantsManager.h"
#include <string>
#include <iostream>

using namespace std;

aspc::Atom::Atom(const std::string & predicateName, const std::vector<std::string> & terms) : predicateName(ConstantsManager::getInstance().getPredicateName(predicateName)), terms(terms) {

}

aspc::Atom::Atom(const aspc::Atom& b) : predicateName(b.predicateName), terms(b.terms) {

}

aspc::Atom::Atom() : predicateName(ConstantsManager::getInstance().getPredicateName("")),terms({}) {

}
aspc::Atom::~Atom() {

}

void aspc::Atom::addTerm(const string& t) {
    terms.push_back(t);
}

const std::string & aspc::Atom::getTermAt(unsigned i) const {
    return terms[i];
}

unsigned aspc::Atom::getAriety() const {
    return terms.size();
}

bool aspc::Atom::isVariableTermAt(unsigned i) const {
    return (terms[i][0] >= 'A' && terms[i][0] <= 'Z') || terms[i] == "_";

}

const string & aspc::Atom::getPredicateName() const {
    return predicateName;
}

vector<unsigned> aspc::Atom::getIntTuple() const {
    vector<unsigned> tuple(terms.size());
    for (unsigned i = 0; i < terms.size(); i++) {
        tuple[i] = ConstantsManager::getInstance().mapConstant(terms[i]);
        //tuple[i] = stoi((*terms)[i]);
    }
    return tuple;
}

// TupleWithoutReasons aspc::Atom::getTupleWithoutReasons(bool negated = false) const {
//     TupleWithoutReasons tuple(&predicateName, negated);
//     tuple.resize(terms.size());
//     for (unsigned i = 0; i < terms.size(); i++) {
//         tuple[i] = ConstantsManager::getInstance().mapConstant(terms[i]);
//     }
//     return tuple;
// }

// TupleWithReasons aspc::Atom::getTupleWithReasons(bool negated = false) const {
//     TupleWithReasons tuple(&predicateName, negated);
//     tuple.resize(terms.size());
//     for (unsigned i = 0; i < terms.size(); i++) {
//         tuple[i] = ConstantsManager::getInstance().mapConstant(terms[i]);
//     }
//     return tuple;
// }

const std::vector<std::string> & aspc::Atom::getTerms() const {
    return terms;
}
void aspc::Atom::setTermAt(int term_index,std::string term_){
    terms[term_index]=term_;
}
void aspc::Atom::setTerms(std::vector<std::string> terms_){
    terms.clear();
    for(std::string t: terms_){
        terms.push_back(t);
    }
}

unsigned aspc::Atom::getTermsSize() const {
    return terms.size();
}

void aspc::Atom::print() const {
    std::cout << predicateName << "(";
    for (unsigned i = 0; i < terms.size(); i++) {
        cout << terms[i];
        if (i != terms.size() - 1) {
            cout << ",";
        }
    }
    cout << ")";
}

string aspc::Atom::toString() const {
    string result;
    result += (predicateName + "(");
    for (unsigned i = 0; i < terms.size(); i++) {
        result += terms[i];
        if (i != terms.size() - 1) {
            result += ",";
        }
    }
    result += ")";
    return result;
}

bool aspc::Atom::unifies(const aspc::Atom& right) const {
    if (predicateName != right.predicateName) {
        return false;
    }
    for (unsigned i = 0; i < terms.size(); i++) {
        if (!isVariableTermAt(i) && !right.isVariableTermAt(i) && terms[i] != right.terms[i]) {
            return false;
        }
    }
    return true;
}

string aspc::Atom::getCanonicalRepresentation(const unordered_set<string> & litBoundVariables) const {
    string res = predicateName+"(";
    unordered_map<string, string> var2canonical;


    for (unsigned i = 0; i < terms.size(); i++) {
        if(litBoundVariables.count(terms[i])) {
            res += "_";
        } else {
            if (isVariableTermAt(i)) {
                const auto & it = var2canonical.find(terms[i]);
                if (it != var2canonical.end()) {
                    res += it -> second;
                } else {
                    string var = "X" + to_string(var2canonical.size());
                    res += var;
                    var2canonical[terms[i]] = var;
                }
            } else {
                res += terms[i];
            }
        }
        if (i != terms.size() - 1) {
            res += ",";
        }
    }
    return res+")";
}

void aspc::Atom::getCoveredVariables(const unordered_set<string>& boundVariables, vector<unsigned>& output) const {
    
    for(unsigned i = 0; i < terms.size(); i++) {
        if(!isVariableTermAt(i) || boundVariables.count(terms[i])) {
            output.push_back(i);
        }
    }
}

void aspc::Atom::getBoundTermsMask(const unordered_set<string>& boundVariables, vector<bool>& output) const {
    output.resize(terms.size(), false);
    for(unsigned i = 0; i < terms.size(); i++) {
        if(!isVariableTermAt(i) || boundVariables.count(terms[i])) {
            output[i] = true;
        }
    }
}


void aspc::Atom::transformToCanonicalRep() {
    unordered_map<string, string> var2canonical;
    for (unsigned i = 0; i < terms.size(); i++) {
        if (isVariableTermAt(i)) {
            const auto & it = var2canonical.find(terms[i]);
            if (it != var2canonical.end()) {
                terms[i] = it -> second;
            } else {
                string var = "X" + to_string(var2canonical.size());
                var2canonical[terms[i]] = var;
                terms[i] = var;
            }
        } 
    }
}
