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

#ifndef ATOM_H_ASPC
#define ATOM_H_ASPC
#include <string>
#include <vector>
#include <iostream>
// #include "../datastructures/TupleWithoutReasons.h"
// #include "../datastructures/TupleWithReasons.h"
#include "../utils/ConstantsManager.h"



namespace aspc {

    class Atom {


    public:

        Atom(const std::string & predicateName) : predicateName(ConstantsManager::getInstance().getPredicateName(predicateName)) {
        }

        Atom(const std::string & predicateName, const std::vector<std::string> & terms);
        Atom(const Atom &);
        Atom();
        
        virtual ~Atom();
        const std::string & getPredicateName() const;
        const std::string & getTermAt(unsigned) const;
        void addTerm(const std::string &);
        unsigned getTermsSize() const;
        const std::vector<std::string> & getTerms() const;
        void setTerms(std::vector<std::string> terms_);
        void setTermAt(int term_index,std::string term_);
        unsigned getAriety() const;
        bool isVariableTermAt(unsigned) const;
        std::vector<unsigned> getIntTuple() const;
        // TupleWithReasons getTupleWithReasons(bool) const;
        // TupleWithoutReasons getTupleWithoutReasons(bool) const;
        void print() const;
        std::string toString() const;
        bool unifies(const Atom & right) const;
        std::string getCanonicalRepresentation(const std::unordered_set<std::string> & litBoundVariables) const;
        void transformToCanonicalRep();
        void getCoveredVariables(const std::unordered_set<std::string> & variables, std::vector<unsigned> & output) const;
        void getBoundTermsMask(const std::unordered_set<std::string> & boundVariables, std::vector<bool> & output) const;
        bool operator==(const Atom& right) const {
                
            return predicateName == (right.predicateName) && terms == right.terms;
            //TODO shared singleton for compiler and compiled
            //return &predicateName == &(right.predicateName) && terms == right.terms;
        }
        
    private:
        const std::string & predicateName;
        std::vector<std::string> terms;
    };

}
#endif

