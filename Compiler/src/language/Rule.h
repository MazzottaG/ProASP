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

#ifndef RULE_H_ASPC
#define RULE_H_ASPC
#include <vector>
#include <map>
#include <unordered_map>
#include <list>
#include <tuple>
#include "Atom.h"
#include "Literal.h"
#include "ArithmeticRelation.h"
#include "ArithmeticRelationWithAggregate.h"
#include "../utils/SharedFunctions.h"

enum RuleType {
    GENERATIVE_RULE, CONSTRAINT
};




namespace aspc {
    

    class Rule {
    public:
        static unsigned rulesCounter;
        static unsigned rulesCounterRewriting;
        static std::string inequalityStrings[];
        Rule(const std::vector<aspc::Atom> & head, const std::vector<aspc::Literal> & body, const std::vector<ArithmeticRelation> & arithmeticRelation,const std::vector<aspc::ArithmeticRelationWithAggregate> & arithmeticRelationsWithAggregate, bool rewriting);
        Rule(const std::vector<aspc::Atom> & head, const std::vector<aspc::Literal> & body, const std::vector<ArithmeticRelation> & arithmeticRelation,const std::vector<aspc::ArithmeticRelationWithAggregate> & arithmeticRelationsWithAggregate);
        Rule(const std::vector<aspc::Atom> & head, const std::vector<aspc::Literal> & body, const std::vector<ArithmeticRelation> & inequalities, bool reorderBody);
        Rule(const std::vector<aspc::Atom> & head, const std::vector<aspc::Literal> & body, const std::vector<ArithmeticRelation> & inequalities, const std::vector<ArithmeticRelationWithAggregate> & inequalitiesWithAggregate, bool reorderBody, bool rewriting);
        Rule(const Rule& other);
        bool equalBodyExpect(const Rule& other,const std::unordered_set<std::string>& forbidden);
        virtual ~Rule();
        const std::vector<aspc::Atom> & getHead() const;
        const std::vector<aspc::Literal> & getBodyLiterals() const;
        const std::vector<ArithmeticRelation> & getArithmeticRelations() const;
        const std::vector<ArithmeticRelationWithAggregate> & getArithmeticRelationsWithAggregate() const;
        void addBodyVars(std::unordered_set<std::string>&) const;
        void addSharedVars(std::unordered_set<std::string>&,std::vector<std::string>&,std::unordered_set<std::string>&,const aspc::ArithmeticRelationWithAggregate*,bool=true) const;
        void addArithmeticRelationsWithAggregate(ArithmeticRelationWithAggregate r);
        void addPositiveBodyVariablesToSet(std::unordered_set<std::string> &) const;
        aspc::Rule cloneWithRenamedVariables(const std::unordered_map<std::string,std::string>& mapping) const;
        RuleType getType() const;
        unsigned getRuleId() const;
        std::vector<std::map<unsigned, std::pair<unsigned, unsigned> > > getJoinIndicesWithJoinOrder(const std::vector<unsigned> & order) const;
        std::map<unsigned, std::pair<unsigned, unsigned> > getBodyToHeadVariablesMap() const;
        unsigned getBodySize() const;
        void print() const;
        bool containsNegation() const;
        bool containsLiteral() const;
        bool containsAggregate() const;
        bool isConstraint() const;
        std::pair<int, int> findFirstOccurrenceOfVariableByStarter(const std::string & var, unsigned starter) const;
        void orderBodyFormulas(std::vector<unsigned>& )const;
        void orderBodyFormulasFromStarter(unsigned starter, std::vector<unsigned>& orderedBodyFormulas)const;
        void bodyReordering();
        void bodyReordering(const std::vector<unsigned> & starters);
        void printOrderedBodies() const;
        void addBodyLiteral(aspc::Literal);
        void addArithmeticRelations(const aspc::ArithmeticRelation& ineq){arithmeticRelations.push_back(ineq);}
        const std::vector<unsigned> & getOrderedBodyIndexesByStarter(unsigned start) const;
        const std::vector<const aspc::Formula*>& getOrderedBodyByStarter(unsigned start) const;
        std::vector<unsigned> getStarters() const;

        const std::vector<const aspc::Formula*> & getFormulas() const;
        std::vector<const aspc::Formula*> getOrderedBodyForReasons(std::unordered_set<std::string> boundVariables) const;
        
        aspc::Literal* getAggregateLiteral (unsigned formulas_index,unsigned literal_index)const{
            return (aggregateLiterals.find(formulas_index)->second)[literal_index];
        }

        void changeCompareTypeToAggregate(int aggrIndex,aspc::ComparisonType type){
            arithmeticRelationsWithAggregate[aggrIndex].setCompareType(type);
        }
        
        std::vector<aspc::Literal*> getAggregateLiteral (unsigned formulas_index)const{
            return aggregateLiterals.find(formulas_index)->second;
        }

        bool containAggregatePredicate(std::string predicateName)const{
            for(const aspc::ArithmeticRelationWithAggregate& ar:arithmeticRelationsWithAggregate)
                for(const aspc::Literal& li : ar.getAggregate().getAggregateLiterals())
                    if(li.getPredicateName() == predicateName)
                        return true;
            return false;
        }
        void updateJoinTupleName(unsigned int formulaIndex,std::string joinTupleName);
        int getSupportAtom()const {return supportAtom;}
        void setSupportAtom(int id){supportAtom=id;}
        bool extractLabeledFormula(const std::vector<int>& formulaLabeling,std::unordered_map<std::string,int>& predToComponent,const std::vector<int>& sccLabel,int label,std::vector<bool>& extraction,std::unordered_set<std::string>& positiveEDBVar)const;
        int rewriteHead(const std::unordered_map<std::string,std::string>& remapped_predicates){
            std::string headPredicate(head[0].getPredicateName());
            std::vector<std::string> headTerms(head[0].getTerms());
            auto it = remapped_predicates.find(headPredicate);
            if(it!=remapped_predicates.end()){
                head.clear();
                head.push_back(aspc::Atom(it->second,headTerms));
                return headTerms.size();
            }
            return -1;
        }
    private:
        std::vector<aspc::Atom> head;
        std::vector<aspc::Literal> bodyLiterals;
        int ruleId;
        std::vector<ArithmeticRelation> arithmeticRelations;
        std::vector<ArithmeticRelationWithAggregate> arithmeticRelationsWithAggregate;
        std::vector<const aspc::Formula*> formulas;
        std::unordered_map<unsigned,std::vector<aspc::Literal*> > aggregateLiterals;

        std::unordered_map<unsigned, std::vector<const aspc::Formula*> > orderedBodyByStarters;
        std::unordered_map<unsigned, std::vector<unsigned> > orderedBodyIndexesByStarters;

        int supportAtom;
    };
}

#endif

