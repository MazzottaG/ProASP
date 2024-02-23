#include "Analyzer.h"
        

bool Analyzer::findAggregateNegativeDependency(const std::vector<std::vector<int>>& scc, unsigned componentId,const aspc::ArithmeticRelationWithAggregate* aggrRelation){
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        unsigned bodyPredicateId = dependencyManager.getPredicateId(literal.getPredicateName());
        bool found=false;
        for(unsigned id:scc[componentId]) if(id == bodyPredicateId) found=true;
        if(found && literal.isNegated())
            return true;
    }
    return false;
}

bool Analyzer::labelAggregateLiteral(std::unordered_map<std::string,int>& predToComponent,std::vector<int>& sccLabel,const aspc::ArithmeticRelationWithAggregate* aggrRelation){
    bool labeled=false;
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        int component=predToComponent[literal.getPredicateName()];
        if(sccLabel[component] == UNK_LAZY){
            sccLabel[component]=NOT_LAZY;
            labeled = true;
        }
    }
    return labeled;
}

void Analyzer::mapPredicateToComponent(const std::vector<std::vector<int>>& scc,std::unordered_map<std::string,int>& predicateToComponent){
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        std::cout << "Component "<<componentId<<": ";
        bool stratified = true;
        for(int pId : scc[componentId]){
            std::string predicate = dependencyManager.getPredicateName(pId);
            std::cout <<predicate << " ";
            predicateToComponent[predicate]=componentId;
        }
        std::cout <<std::endl;
        if(componentId == 0) return;
        componentId--;
    }
}
void Analyzer::labelStratified(std::vector<int>& stratLabel,const std::vector<std::vector<int>>& scc){
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        bool stratified = true;
        for(int pId : scc[componentId]){
            std::string predicate = dependencyManager.getPredicateName(pId);
            std::vector<unsigned> rulesForPredicate = program.getRulesForPredicate(predicate);
            for(unsigned ruleId : rulesForPredicate){
                const aspc::Rule* rule = &program.getRule(ruleId);
                const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
                for(unsigned fId = 0; fId<body->size(); fId++){
                    if(body->at(fId)->isLiteral()){
                        const aspc::Literal* bodyLiteral = (const aspc::Literal*) body->at(fId);
                        unsigned bodyPredicateId = dependencyManager.getPredicateId(bodyLiteral->getPredicateName());
                        bool found=false;
                        for(unsigned id:scc[componentId]) if(id == bodyPredicateId) found=true;
                        if(found && bodyLiteral->isNegated())
                            stratified = false;
                    }else if(body->at(fId)->containsAggregate()){
                        bool found = findAggregateNegativeDependency(scc,componentId,(const aspc::ArithmeticRelationWithAggregate*)body->at(fId));
                        if(found) stratified=false;
                    }
                }
            }
        }
        stratLabel[componentId]= stratified ? STRATIFIED : NOT_STRATIFIED;
        if(componentId == 0) return;
        componentId--;
    }
}
void Analyzer::labelLazyness(const std::vector<std::vector<int>>& scc, std::unordered_map<std::string,int>& predToComponent,std::vector<int>& sccLabel){
    bool labeledComponent=true;
    while(labeledComponent){
        labeledComponent = false;
        for(unsigned ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
            const aspc::Rule* rule = &program.getRule(ruleId);
            const std::vector<aspc::Atom>* head = &rule->getHead();
            bool labelBody = rule->isConstraint();
            if(!labelBody){
                for(unsigned hId = 0; hId < head->size(); hId++){
                    int component = predToComponent[head->at(hId).getPredicateName()];
                    if(sccLabel[component] == NOT_LAZY){
                        labelBody = true;
                        break;
                    }
                }
            }
            if(labelBody){
                for(const aspc::Formula* f: rule->getFormulas()){
                    if(f->isLiteral()){
                        const aspc::Literal* lit = (const aspc::Literal*)f;
                        int component=predToComponent[lit->getPredicateName()];
                        if(sccLabel[component] == UNK_LAZY){
                            sccLabel[component]=NOT_LAZY;
                            labeledComponent=true;
                        }
                    }else if(f->containsAggregate()){
                        if(labelAggregateLiteral(predToComponent,sccLabel,(const aspc::ArithmeticRelationWithAggregate*) f))
                            labeledComponent = true;
                    }
                    
                }
            }
        }
    }
    for(unsigned i = 0; i<sccLabel.size();i++){
        if(sccLabel[i] == UNK_LAZY)
            sccLabel[i]=LAZY;
    }
}
void Analyzer::labelEager(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
    // A component is eager if it is not stratified 
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        if(stratLabel[componentId] == NOT_STRATIFIED)
            typeLabel[componentId] = TYPE_EAGER;
        if(componentId == 0) break;
        componentId--;
    }
    bool newEager=true;
    while(newEager){
        newEager=false;
        componentId = scc.size()-1;
        while (componentId >= 0){
            if(typeLabel[componentId] == UNK_TYPE){
                //A component is eager if it depends from an eager component and cannot be lazy 
                bool foundDep = false;
                for(unsigned comp = 0; comp<scc.size();comp++){
                    if(typeLabel[comp] == TYPE_EAGER){
                        for(int u: scc[comp]){
                            for(int v: scc[componentId]){
                                if(dependencyManager.existsEdge(u,v)){
                                    foundDep=true;
                                }
                            }
                        }
                    }
                }
                if(foundDep){
                    if(lazyLabel[componentId] == NOT_LAZY){
                        typeLabel[componentId] = TYPE_EAGER;
                        newEager = true;
                    }
                }
            }
            if(componentId == 0) break;
            componentId--;
        }
    }
}   
void Analyzer::labelLazy(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        if(typeLabel[componentId] == UNK_TYPE){
            //A component is Lazy if it is not eager, it depends from an eager component, and it can be lazy
            bool foundDep = false;
            for(unsigned comp = 0; comp<scc.size();comp++){
                if(typeLabel[comp] == TYPE_EAGER){
                    for(int u: scc[comp]){
                        for(int v: scc[componentId]){
                            if(dependencyManager.existsEdge(u,v))
                                foundDep=true;
                        }
                    }
                }
            }
            if(foundDep){
                if(lazyLabel[componentId] == LAZY){
                    typeLabel[componentId] = TYPE_LAZY;
                }else{
                    if(lazyLabel[componentId] == NOT_LAZY){
                        std::cout << "Error: component "<<componentId<<" depends from eager, cannot be lazy and has not be labeled as eager"<<std::endl;
                        exit(180);
                    }
                    std::cout << "Error: unable to find lazyness label for "<<componentId<<std::endl;
                    exit(180);
                }
            }
            
        }
        if(componentId == 0) break;
        componentId--;
    }
    bool newLazy=true;
    while(newLazy){
        newLazy=false;
        componentId = scc.size()-1;
        while (componentId >= 0){
            if(typeLabel[componentId] == UNK_TYPE){
                //A component is Lazy if it depends from a lazy component and can be lazy
                bool foundDep = false;
                for(unsigned comp = 0; comp<scc.size();comp++){
                    if(typeLabel[comp] == TYPE_LAZY){
                        for(int u: scc[comp]){
                            for(int v: scc[componentId]){
                                if(dependencyManager.existsEdge(u,v))
                                    foundDep=true;
                            }
                        }
                    }
                }
                if(foundDep){
                    if(lazyLabel[componentId] == NOT_LAZY){
                        std::cout << "Error: component "<<componentId<<" depends from lazy component but it cannot be lazy"<<std::endl;
                        exit(180);
                    }else if(lazyLabel[componentId] == LAZY){
                        typeLabel[componentId]=TYPE_LAZY;
                        newLazy=true;
                    }else{
                        std::cout << "Error: unable to find lazyness label for "<<componentId<<std::endl;
                        exit(180);
                    }
                }
            }
            if(componentId == 0) break;
            componentId--;
        }
    }
}
void Analyzer::labelDatalog(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        if(typeLabel[componentId] == UNK_TYPE){
            typeLabel[componentId]=TYPE_DATALOG;
        }
        if(componentId == 0) break;
        componentId--;
    }
}
void Analyzer::labelType(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
    labelEager(typeLabel,stratLabel,lazyLabel,scc);            
    labelLazy(typeLabel,stratLabel,lazyLabel,scc);            
    labelDatalog(typeLabel,stratLabel,lazyLabel,scc);    
}
int Analyzer::labelAggregate(const std::vector<int>& sccLabel,const aspc::ArithmeticRelationWithAggregate* aggrRelation,std::unordered_map<std::string,int>& predToComponent){
    bool onlyDatalog = true;
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        int component = predToComponent[literal.getPredicateName()];
        if(sccLabel[component]!=TYPE_DATALOG){
            onlyDatalog=false;
        }
    }
    return onlyDatalog ? DATALOG_FORMULA : NON_DATALOG_FORMULA;
}
bool Analyzer::labelFormulas(const std::vector<int>& sccLabel,const std::vector<const aspc::Formula*>* body,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& label){
    bool onlyDatalog = true;
    for(unsigned fIndex = 0; fIndex < body->size(); fIndex++){
        if(body->at(fIndex)->isLiteral()){
            const aspc::Literal* literal = (const aspc::Literal*) body->at(fIndex);
            int component = predToComponent[literal->getPredicateName()];
            label[fIndex] = sccLabel[component] == TYPE_DATALOG ? DATALOG_FORMULA : NON_DATALOG_FORMULA;
            if(label[fIndex]!=DATALOG_FORMULA){
                onlyDatalog=false;
            }
        }else if(body->at(fIndex)->containsAggregate()){
            std::cout << "Aggregate formula ";
            body->at(fIndex)->print();
            std::cout << std::endl;
            label[fIndex]=labelAggregate(sccLabel,(const aspc::ArithmeticRelationWithAggregate*)body->at(fIndex),predToComponent);
            if(label[fIndex]!=DATALOG_FORMULA){
                onlyDatalog=false;
            }
        }else{
            std::cout << "Found inequalities extracting join rule"<<std::endl;
        }
    }
    return onlyDatalog;
}
void Analyzer::labelArithmeticRelations(const std::vector<const aspc::Formula*>* formulas,std::vector<int>& formulaLabeling, std::unordered_set<std::string>& positiveVars){
    bool newRelationLabeled = true;
    while (newRelationLabeled){
        newRelationLabeled = false;
        for(unsigned i=0; i<formulas->size(); i++){
            if(formulas->at(i)->isLiteral() || formulas->at(i)->containsAggregate() || formulaLabeling[i]!=UNK_FORMULA_LABEL) continue;
            if(formulas->at(i)->isBoundedRelation(positiveVars)){
                std::cout << "Labeling ";
                formulas->at(i)->print();
                std::cout << std::endl;
                formulaLabeling[i] = DATALOG_FORMULA;
            }else if(formulas->at(i)->isBoundedValueAssignment(positiveVars)){
                std::cout << "Found bound value assignment ";
                formulas->at(i)->print();
                std::cout << std::endl;
            
                std::string assgnVar = ((const aspc::ArithmeticRelation*) formulas->at(i))->getAssignedVariable(positiveVars);
                formulaLabeling[i]=DATALOG_FORMULA;
                newRelationLabeled=true;
                positiveVars.insert(assgnVar);
            }
        }   
    }
}

void Analyzer::labelRemainingArithmeticRelations(const std::vector<const aspc::Formula*>* formulas,std::vector<int>& formulaLabeling, std::unordered_set<std::string>& positiveVars){
    bool newRelationLabeled = true;
    while (newRelationLabeled){
        newRelationLabeled = false;
        for(unsigned i=0; i<formulas->size(); i++){
            if(formulas->at(i)->isLiteral() || formulas->at(i)->containsAggregate() || formulaLabeling[i]!=UNK_FORMULA_LABEL) continue;
            std::cout << "Labeling ";
            formulas->at(i)->print();
            std::cout << std::endl;
            formulaLabeling[i] = NON_DATALOG_FORMULA;

            if(formulas->at(i)->isBoundedValueAssignment(positiveVars)){
                std::string assgnVar = ((const aspc::ArithmeticRelation*) formulas->at(i))->getAssignedVariable(positiveVars);
                newRelationLabeled=true;
                positiveVars.insert(assgnVar);
            }
        }   
    }
}

bool Analyzer::canExportAggregate(const aspc::ArithmeticRelationWithAggregate* aggrRelation, std::unordered_set<std::string> positiveEDBVars, std::unordered_set<std::string> positiveIDBVars){
    for(const aspc::Literal& literal : aggrRelation->getAggregate().getAggregateLiterals()){
        for(unsigned k = 0; k < literal.getAriety(); k++){
            std::string term = literal.getTermAt(k);
            if(literal.isVariableTermAt(k) && positiveIDBVars.count(term)!=0 && positiveEDBVars.count(term) == 0){
                return false;
            }
        }
    }
    for(const aspc::ArithmeticRelation& rel : aggrRelation->getAggregate().getAggregateInequalities()){
        for(const aspc::ArithmeticExpression& exp : {rel.getLeft(),rel.getRight()}){
            for(std::string term : aggrRelation->getGuard().getAllTerms()){
                if(isVariable(term) && positiveIDBVars.count(term)!=0 && positiveEDBVars.count(term) == 0)
                    return false;
            }
        }
    }
    for(std::string term : aggrRelation->getGuard().getAllTerms()){
        if(isVariable(term) && positiveIDBVars.count(term)!=0 && positiveEDBVars.count(term) == 0)
            return false;
    }
    return true;
}
bool Analyzer::findMaximalDatalogBody(const aspc::Rule* rule,int ruleId,const std::vector<int>& sccLabel,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& formulaLabeling){
    std::cout << "Analyzer::findMaximalDatalogBody ";
    rule->print();
    const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
    bool onlyDatalog = labelFormulas(sccLabel,body,predicateToComponent,formulaLabeling);
    rulesBodyLabeling[ruleId]=formulaLabeling;
    std::cout << "   Labeling rule "<<ruleId<<std::endl;
    for(unsigned index = 0;index < body->size(); index++){
        const aspc::Formula* f = body->at(index);
        std::cout << "      Found formula: ";
        f->print();
        std::cout << "   as "<< (formulaLabeling[index] == DATALOG_FORMULA ? "EDB" : (formulaLabeling[index] == NON_DATALOG_FORMULA ? "IDB" : "Unknown"))<<std::endl;
    }
    if(onlyDatalog){
        std::cout << "Only datalog" << std::endl;
        return true;
    }
    if(inputLabel[ruleId]){
        for(unsigned i=0; i<body->size(); i++){
            formulaLabeling[i]=NON_DATALOG_FORMULA;
        }
        return false;
    }

    std::cout << "Analyzing remaining formulas" << std::endl;
    
    std::unordered_set<std::string> positiveEDBVars;
    std::unordered_set<std::string> positiveIDBVars;

    const std::vector<const aspc::Formula*>* formulas = &rule->getFormulas();
    for(unsigned i=0; i<formulas->size(); i++){
        if(!formulas->at(i)->isLiteral() || !formulas->at(i)->isPositiveLiteral() || formulaLabeling[i] == UNK_FORMULA_LABEL) continue;
        formulas->at(i)->addVariablesToSet(formulaLabeling[i] == DATALOG_FORMULA ? positiveEDBVars : positiveIDBVars);
    }      

    labelArithmeticRelations(formulas,formulaLabeling,positiveEDBVars);
    labelRemainingArithmeticRelations(formulas,formulaLabeling,positiveIDBVars);

    for(unsigned i=0; i<formulas->size(); i++){
        if(!formulas->at(i)->isLiteral() || formulas->at(i)->isPositiveLiteral()) continue;
        if(formulaLabeling[i] == DATALOG_FORMULA && !formulas->at(i)->isBoundedLiteral(positiveEDBVars)){
            formulaLabeling[i] = NON_DATALOG_FORMULA;
        }
    }      

    for(unsigned i=0; i<formulas->size(); i++){
        if(!formulas->at(i)->containsAggregate() || formulaLabeling[i] == NON_DATALOG_FORMULA) continue;
        std::unordered_set<std::string> sharedVars;
        if(!canExportAggregate((const aspc::ArithmeticRelationWithAggregate*) formulas->at(i), positiveEDBVars,positiveIDBVars))
            formulaLabeling[i]=NON_DATALOG_FORMULA;
    } 
    std::unordered_set<std::string> joinVars;
    std::vector<std::string> vars;

    for(unsigned i=0; i<formulas->size(); i++){
        const aspc::Formula* f = formulas->at(i);
        if(formulaLabeling[i] == DATALOG_FORMULA) continue;
        if(f->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* aggregate = (const aspc::ArithmeticRelationWithAggregate*) f;
            for(const aspc::Literal& l : aggregate->getAggregate().getAggregateLiterals()){
                for(unsigned k=0; k<l.getAriety();k++){
                    std::string term = l.getTermAt(k);
                    if(l.isVariableTermAt(k) && positiveEDBVars.count(term)!=0){
                        if(joinVars.count(term)==0){
                            joinVars.insert(term);
                            vars.push_back(term);
                        }
                    }
                }
            }
            for(const aspc::ArithmeticRelation& l : aggregate->getAggregate().getAggregateInequalities()){
                for(const aspc::ArithmeticExpression& exp : {l.getLeft(),l.getRight()})
                    for(std::string term: exp.getAllTerms()){
                        if(isVariable(term) && positiveEDBVars.count(term)!=0){
                            if(joinVars.count(term)==0){
                                joinVars.insert(term);
                                vars.push_back(term);
                            }
                        }
                    }
            }
            for(std::string term: aggregate->getGuard().getAllTerms()){
                if(isVariable(term) && positiveEDBVars.count(term)!=0){
                    if(joinVars.count(term)==0){
                        joinVars.insert(term);
                        vars.push_back(term);
                    }
                }
            }
        }else if(!f->isLiteral()){
            const aspc::ArithmeticRelation* rel = (const aspc::ArithmeticRelation*)f;
            for(const aspc::ArithmeticExpression& exp : {rel->getLeft(),rel->getRight()})
                for(std::string term: exp.getAllTerms()){
                    if(isVariable(term) && positiveEDBVars.count(term)!=0){
                        if(joinVars.count(term)==0){
                            joinVars.insert(term);
                            vars.push_back(term);
                        }
                    }
                }
        }else{
            const aspc::Literal* l = (const aspc::Literal*)f;
            for(unsigned k=0; k<l->getAriety();k++){
                std::string term = l->getTermAt(k);
                if(l->isVariableTermAt(k) && positiveEDBVars.count(term)!=0){
                    if(joinVars.count(term)==0){
                        joinVars.insert(term);
                        vars.push_back(term);
                    }
                }
            }
        }
    }     
    for(const aspc::Atom& l : rule->getHead()){
        for(unsigned k=0; k<l.getAriety();k++){
            std::string term = l.getTermAt(k);
            if(l.isVariableTermAt(k) && positiveEDBVars.count(term)!=0){
                if(joinVars.count(term)==0){
                    joinVars.insert(term);
                    vars.push_back(term);
                }
            }
        }
    }

    joinRuleTerms[ruleId]=vars;
    return false;          
}
void Analyzer::rewriteWithJoin(const aspc::Rule* rule,int ruleId,std::vector<int> formulaLabeling,bool isConstraint){
    std::vector<aspc::Literal> literalsIDB;
    std::vector<aspc::Literal> literalsEDB;
    
    std::vector<aspc::ArithmeticRelation> ineqsIDB;
    std::vector<aspc::ArithmeticRelation> ineqsEDB;

    std::vector<aspc::ArithmeticRelationWithAggregate> aggregatesEDB;
    std::vector<aspc::ArithmeticRelationWithAggregate> aggregatesIDB;
    for(unsigned i=0; i<rule->getFormulas().size();i++){
        const aspc::Formula* f = rule->getFormulas().at(i);
        if(formulaLabeling[i] == NON_DATALOG_FORMULA){
            if(f->isLiteral()) literalsIDB.push_back(*((const aspc::Literal*)f));
            else if(!f->containsAggregate()) ineqsIDB.push_back(*((const aspc::ArithmeticRelation*)f));
            else aggregatesIDB.push_back(*((const aspc::ArithmeticRelationWithAggregate*)f));
        }else{
            if(f->isLiteral()) literalsEDB.push_back(*((const aspc::Literal*)f));
            else if(!f->containsAggregate()) ineqsEDB.push_back(*((const aspc::ArithmeticRelation*)f));
            else aggregatesEDB.push_back(*((const aspc::ArithmeticRelationWithAggregate*)f));
        }
    }
    std::string joinPredicate = "join"+std::to_string(ruleId);
    RuleBody edbBodyData(literalsEDB,ineqsEDB,aggregatesEDB,joinRuleTerms[ruleId]);
    std::cout << "Adding join rule for ";
    rule->print();
    edbBodyData.print("temp");
    bool defined = false;
    std::cout << "Iterating previous sharedVars data"<<std::endl;
    for(auto pair: joinRuleData){
        std::cout << "Comparing with"<<std::endl;
        pair.second.print(pair.first);
        if(pair.second == edbBodyData){
            joinPredicate = pair.first;
            defined = true;
            break;
        }
    }
    if(!defined){
        dependencyManager.addNewPredicate(joinPredicate);
        joinRuleData[joinPredicate]=edbBodyData;
        datalogPrg.addRule(aspc::Rule({aspc::Atom(joinPredicate,joinRuleTerms[ruleId])},literalsEDB,ineqsEDB,aggregatesEDB,false,false));
    }
    
    // literalsIDB.push_back(aspc::Literal(false,aspc::Atom(joinPredicate,joinRuleTerms[ruleId])));
    std::vector<aspc::Literal> reorderedLiterals;
    reorderedLiterals.push_back(aspc::Literal(false,aspc::Atom(joinPredicate,joinRuleTerms[ruleId])));
    for(unsigned i=0; i<literalsIDB.size(); i++) reorderedLiterals.push_back(aspc::Literal(literalsIDB[i]));
    std::vector<aspc::Atom> emptyhead;
    eagerPrg.addRule(aspc::Rule(isConstraint ? emptyhead : rule->getHead(),reorderedLiterals,ineqsIDB,aggregatesIDB,false,false));
    eagerLabel.push_back(inputLabel[ruleId]);
}

void Analyzer::buildPrograms(const std::vector<std::vector<int>>& scc,const std::vector<int>&  sccLabel,std::unordered_map<std::string,int>& predToComponent){
    unsigned componentId = scc.size()-1;
    eagerLabel.clear();
    std::cout << "Building programs"<<std::endl;
    while (componentId >= 0){
        for(int predicateId : scc[componentId]){
            std::string predicate = dependencyManager.getPredicateName(predicateId);
            auto rulesForPredicate = program.getRulesForPredicate(predicate);
            for(int ruleId : rulesForPredicate){
                const aspc::Rule* rule = &program.getRule(ruleId);
                if(sccLabel[componentId] == TYPE_EAGER){
                    std::vector<int> formulaLabeling(rule->getFormulas().size(),UNK_FORMULA_LABEL);
                    bool fullDatalog = findMaximalDatalogBody(rule,ruleId,sccLabel,predToComponent,formulaLabeling);

                    if(fullDatalog)
                        datalogPrg.addRule(*rule);
                    else{
                        bool datalogAggr = false;
                        unsigned datalogLit   = 0;
                        const aspc::Literal* firstEDB=NULL;
                        for(unsigned i=0; i<rule->getFormulas().size();i++){
                            const aspc::Formula* f = rule->getFormulas().at(i);
                            if(formulaLabeling[i] == DATALOG_FORMULA){
                                if(f->isLiteral()) {
                                    datalogLit++;
                                    if(firstEDB == NULL){
                                        firstEDB = (const aspc::Literal*)f;
                                    }
                                }
                                else if(f->containsAggregate()) datalogAggr = true;
                            }
                        }
                        bool projection=false;
                        if(datalogLit == 1){
                            assert(firstEDB != NULL);
                            std::unordered_set<std::string> headVars;
                            aspc::Literal(false,rule->getHead()[0]).addVariablesToSet(headVars);
                            if(!firstEDB->isBoundedLiteral(headVars)){
                                projection=true;
                            }
                        }
                        if(datalogAggr || projection || datalogLit > 1){
                            rewriteWithJoin(rule,ruleId,formulaLabeling,false);
                            remappingBodyLabeling[eagerLabel.size()-1]=ruleId;
                        }else{
                            joinRuleTerms.erase(ruleId);
                            remappingBodyLabeling[eagerLabel.size()]=ruleId;
                            eagerPrg.addRule(*rule);
                            eagerLabel.push_back(inputLabel[ruleId]);
                        }
                    }
                }
                else{
                    if(sccLabel[componentId] == TYPE_LAZY) lazyPrg.addRule(*rule);
                    else datalogPrg.addRule(*rule);
                }
            }
        }
        if(componentId == 0) break;
        componentId--;
    }
    for(unsigned ruleId = 0; ruleId<program.getRulesSize(); ruleId++){
        const aspc::Rule* rule = &program.getRule(ruleId);
        if(!rule->isConstraint()) continue;
        std::vector<int> formulaLabeling(rule->getFormulas().size(),UNK_FORMULA_LABEL);
        bool fullDatalog = findMaximalDatalogBody(rule,ruleId,sccLabel,predToComponent,formulaLabeling);

        if(fullDatalog){
            remappingBodyLabeling[eagerLabel.size()]=ruleId;
            eagerPrg.addRule(*rule);
            eagerLabel.push_back(inputLabel[ruleId]);
        }else{
            bool datalogAggr = false;
            unsigned datalogLit   = 0;
            for(unsigned i=0; i<rule->getFormulas().size();i++){
                const aspc::Formula* f = rule->getFormulas().at(i);
                if(formulaLabeling[i] == DATALOG_FORMULA){
                    if(f->isLiteral()) datalogLit++;
                    else if(f->containsAggregate()) datalogAggr = true;
                }
            }
            bool tooVariables = joinRuleTerms[ruleId].size() >= datalogLit/2;
            if(!tooVariables && (datalogAggr || datalogLit > 1)){
                rewriteWithJoin(rule,ruleId,formulaLabeling,true);
                remappingBodyLabeling[eagerLabel.size()-1]=ruleId;
            }else{
                joinRuleTerms.erase(ruleId);
                remappingBodyLabeling[eagerLabel.size()]=ruleId;

                eagerPrg.addRule(*rule);
                eagerLabel.push_back(inputLabel[ruleId]);
            }
        }
    }
    std::cout << "------------- DATALOG -------------"<<std::endl;
    datalogPrg.print();
    std::cout << "------------- EAGER -------------"<<std::endl;
    eagerPrg.print();
    std::cout << "------------- LAZY -------------"<<std::endl;
    lazyPrg.print();
}
void Analyzer::printProgramBySCC(const std::vector<std::vector<int>>& scc,const std::vector<int>& sccLabel,int label){
    unsigned componentId = scc.size()-1;
    while (componentId >= 0){
        if(sccLabel[componentId] == label){
            std::cout << "Component "<<componentId<<std::endl;
            for(int pId : scc[componentId]){
                std::string predicate = dependencyManager.getPredicateName(pId);
                std::cout << "   Predicate "<<predicate<<std::endl;
                std::vector<unsigned> rulesForPredicate = program.getRulesForPredicate(predicate);
                for(unsigned ruleId : rulesForPredicate){
                    const aspc::Rule* rule = &program.getRule(ruleId);
                    std::cout << "      ";rule->print();
                }
            }
        }
        if(componentId == 0) return;
        componentId--;
    }
}
void Analyzer::splitProgram(){
    dependencyManager.buildDependecyGraph(program);
    auto scc = dependencyManager.getSCC();

    if(scc.size() == 0) return;
    mapPredicateToComponent(scc,predicateToComponent);

    std::vector<int> sccStratLabel(scc.size(),UNK_STRATIFIED);
    labelStratified(sccStratLabel,scc);

    std::vector<int> sccLazyLabel(scc.size(),UNK_LAZY);
    for(unsigned i = 0;i<sccStratLabel.size(); i++){
        if(sccStratLabel[i] == NOT_STRATIFIED)
            sccLazyLabel[i] = NOT_LAZY;
    }

    labelLazyness(scc,predicateToComponent,sccLazyLabel);
    // std::cout << "--------- LAZYNESS ---------"<<std::endl;
    // printProgramBySCC(scc,sccLazyLabel,LAZY);
    // std::cout << "--------- NOT LAZYNESS ---------"<<std::endl;
    // printProgramBySCC(scc,sccLazyLabel,NOT_LAZY);
    
    sccTypeLabel=std::vector<int>(scc.size(),UNK_TYPE);
    labelType(sccTypeLabel,sccStratLabel,sccLazyLabel,scc);

    buildPrograms(scc,sccTypeLabel,predicateToComponent);        
}

Analyzer::Analyzer(const aspc::Program& p,const std::vector<bool>& labels,bool fullgrounded):program(p),inputLabel(labels),fullGrounding(fullgrounded){
    splitProgram();
}
const std::vector<bool>& Analyzer::getEagerLabel()const {return eagerLabel;}
const aspc::Program& Analyzer::getDatalog()const {return datalogPrg;}
const aspc::Program& Analyzer::getEager()const {return eagerPrg;}
const aspc::Program& Analyzer::getLazy()const {return lazyPrg;}

const std::unordered_map<std::string,unsigned> Analyzer::getPredicateToId()const {return dependencyManager.getPredicateToId();}
const std::vector<std::string> Analyzer::getIdToPredicate()const {return dependencyManager.getIdToPredicate();}
bool Analyzer::isEDB(std::string predicate){
    return predicateToComponent.count(predicate) && sccTypeLabel[predicateToComponent[predicate]] == TYPE_DATALOG;
}
