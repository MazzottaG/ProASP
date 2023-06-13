#ifndef SMARTREWRITER_H
#define ANALYZER_H
#include "../language/Program.h"
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../utils/SharedFunctions.h"
class Analyzer{
    private:
        aspc::Program program;
        GraphWithTarjanAlgorithm dependencyGraph;
        std::vector<std::string> idToPredicate;
        std::unordered_map<std::string,unsigned> predicateToId;

        // Rewriter output
        aspc::Program datalogPrg;
        aspc::Program eagerPrg;
        aspc::Program lazyPrg;

        std::unordered_map<int,std::vector<std::string>> joinRuleTerms;
        
        void buildDependecyGraph(){
            for(unsigned ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
                const aspc::Rule* rule = &program.getRule(ruleId);
                // Map predicates to nodes
                const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
                for(unsigned bId = 0; bId<body->size(); bId++){
                    if(!body->at(bId)->isLiteral()) continue;
                    const aspc::Literal* literal = (const aspc::Literal*) body->at(bId);
                    if(!predicateToId.count(literal->getPredicateName())){
                        predicateToId[literal->getPredicateName()]=idToPredicate.size();
                        dependencyGraph.addNode(idToPredicate.size());
                        idToPredicate.push_back(literal->getPredicateName());
                    }
                }
                if(rule->isConstraint()) continue;;
                const std::vector<aspc::Atom>* head = &rule->getHead();
                for(unsigned hId = 0; hId<head->size(); hId++){
                    const aspc::Atom* h = &head->at(hId);
                    if(!predicateToId.count(h->getPredicateName())){
                        predicateToId[h->getPredicateName()]=idToPredicate.size();
                        dependencyGraph.addNode(idToPredicate.size());
                        idToPredicate.push_back(h->getPredicateName());
                    }
                }
                // Add body to head dependencies
                for(unsigned bId = 0; bId<body->size(); bId++){
                    if(!body->at(bId)->isLiteral()) continue;
                    const aspc::Literal* literal = (const aspc::Literal*) body->at(bId);
                    int bPredId = predicateToId[literal->getPredicateName()];
                    for(unsigned hId = 0; hId<head->size(); hId++){
                        const aspc::Atom* h = &head->at(hId);
                        int hPredId = predicateToId[h->getPredicateName()];
                        dependencyGraph.addEdge(bPredId,hPredId);
                    }
                }    
            }
        }
        void mapPredicateToComponent(const std::vector<std::vector<int>>& scc,std::unordered_map<std::string,int>& predicateToComponent){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                std::cout << "Component "<<componentId<<std::endl;
                bool stratified = true;
                for(int pId : scc[componentId]){
                    std::string predicate = idToPredicate[pId];
                    std::cout << "   Predicate: "<<predicate<<std::endl;
                    predicateToComponent[predicate]=componentId;
                }
                if(componentId == 0) return;
                componentId--;
            }
        }
        void labelStratified(std::vector<int>& stratLabel,const std::vector<std::vector<int>>& scc){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                bool stratified = true;
                for(int pId : scc[componentId]){
                    std::string predicate = idToPredicate[pId];
                    std::vector<unsigned> rulesForPredicate = program.getRulesForPredicate(predicate);
                    for(unsigned ruleId : rulesForPredicate){
                        const aspc::Rule* rule = &program.getRule(ruleId);
                        const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
                        for(unsigned fId = 0; fId<body->size(); fId++){
                            if(!body->at(fId)->isLiteral()) continue;
                            const aspc::Literal* bodyLiteral = (const aspc::Literal*) body->at(fId);
                            unsigned bodyPredicateId = predicateToId[bodyLiteral->getPredicateName()];
                            bool found=false;
                            for(unsigned id:scc[componentId]) if(id == bodyPredicateId) found=true;
                            if(found && bodyLiteral->isNegated())
                                stratified = false;
                        }
                    }
                }
                stratLabel[componentId]= stratified ? STRATIFIED : NOT_STRATIFIED;
                if(componentId == 0) return;
                componentId--;
            }
        }
        void labelLazyness(const std::vector<std::vector<int>>& scc, std::unordered_map<std::string,int>& predToComponent,std::vector<int>& sccLabel){
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
                            if(!f->isLiteral()) continue;
                            const aspc::Literal* lit = (const aspc::Literal*)f;
                            int component=predToComponent[lit->getPredicateName()];
                            if(sccLabel[component] == UNK_LAZY){
                                sccLabel[component]=NOT_LAZY;
                                labeledComponent=true;
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
        void labelEager(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
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
                                        if(dependencyGraph.existsEdge(u,v))
                                            foundDep=true;
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
        void labelLazy(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                if(typeLabel[componentId] == UNK_TYPE){
                    //A component is Lazy if it is not eager, it depends from an eager component, and it can be lazy
                    bool foundDep = false;
                    for(unsigned comp = 0; comp<scc.size();comp++){
                        if(typeLabel[comp] == TYPE_EAGER){
                            for(int u: scc[comp]){
                                for(int v: scc[componentId]){
                                    if(dependencyGraph.existsEdge(u,v))
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
                                        if(dependencyGraph.existsEdge(u,v))
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
        void labelDatalog(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                if(typeLabel[componentId] == UNK_TYPE){
                    typeLabel[componentId]=TYPE_DATALOG;
                }
                if(componentId == 0) break;
                componentId--;
            }
        }
        void labelType(std::vector<int>& typeLabel,const std::vector<int>& stratLabel,const std::vector<int>& lazyLabel,const std::vector<std::vector<int>>& scc){
            labelEager(typeLabel,stratLabel,lazyLabel,scc);            
            labelLazy(typeLabel,stratLabel,lazyLabel,scc);            
            labelDatalog(typeLabel,stratLabel,lazyLabel,scc);    
        }
        
        bool labelFormulas(const std::vector<int>& sccLabel,const std::vector<const aspc::Formula*>* body,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& label){
            bool onlyDatalog = true;
            for(unsigned fIndex = 0; fIndex < body->size(); fIndex++){
                if(body->at(fIndex)->isLiteral()){
                    const aspc::Literal* literal = (const aspc::Literal*) body->at(fIndex);
                    int component = predToComponent[literal->getPredicateName()];
                    label[fIndex]=sccLabel[component];
                    if(sccLabel[component]!=TYPE_DATALOG){
                        onlyDatalog=false;
                    }
                }
            }
            return onlyDatalog;
        }
        int extractJoinRule(const aspc::Rule* rule,int ruleId,const std::vector<int>& sccLabel,std::unordered_map<std::string,int>& predToComponent,std::vector<int>& formulaLabeling){
            const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
            bool onlyDatalogLiteral = labelFormulas(sccLabel,body,predToComponent,formulaLabeling);
            if(onlyDatalogLiteral){
                if(rule->isConstraint())
                    eagerPrg.addRule(*rule);
                else
                    datalogPrg.addRule(*rule);
                return DATALOG_BODY;
            }else{
                std::vector<bool> extractedFormulas(body->size(),false);
                std::unordered_set<std::string> positiveEDBVars;
                if(rule->extractLabeledFormula(predToComponent,sccLabel,TYPE_DATALOG,extractedFormulas,positiveEDBVars)){
                    std::unordered_set<std::string> varsIDB;
                    std::vector<aspc::Literal> literalsIDB;
                    std::vector<aspc::Literal> literalsEDB;
                    std::vector<aspc::ArithmeticRelation> ineqsIDB;
                    std::vector<aspc::ArithmeticRelation> ineqsEDB;
                    std::unordered_set<std::string> vars;
                    for(unsigned i=0;i<body->size();i++){
                        if(extractedFormulas[i]){
                            if(body->at(i)->isLiteral())
                                literalsEDB.push_back(*((const aspc::Literal*)body->at(i)));
                            else ineqsEDB.push_back(*((const aspc::ArithmeticRelation*)body->at(i)));
                        }else{
                            formulaLabeling[i]=TYPE_EAGER;
                            if(body->at(i)->isLiteral()){
                                body->at(i)->addVariablesToSet(vars);
                                literalsIDB.push_back(*((const aspc::Literal*)body->at(i)));
                            }
                            else {
                                auto ineq = (const aspc::ArithmeticRelation*)body->at(i);
                                ineqsIDB.push_back(*ineq);
                                for(aspc::ArithmeticExpression expr : {ineq->getLeft(), ineq->getRight()}){
                                    for(std::string term : expr.getAllTerms()){
                                        if(isVariable(term)) vars.insert(term);
                                    }
                                }
                            }
                        }
                    }
                    for(const aspc::Atom h: rule->getHead()){
                        aspc::Literal(false,h).addVariablesToSet(vars);
                    }
                    for(std::string v : vars)
                        if(positiveEDBVars.count(v))
                            joinRuleTerms[ruleId].push_back(v);
                    std::string joinPredicate = "join"+std::to_string(ruleId);
                    datalogPrg.addRule(aspc::Rule({aspc::Atom(joinPredicate,joinRuleTerms[ruleId])},literalsEDB,ineqsEDB,false));
                    if(!predicateToId.count(joinPredicate)){
                        predicateToId[joinPredicate]=idToPredicate.size();
                        idToPredicate.push_back(joinPredicate);
                    }
                    return EXTRACTED_JOIN;
                }else{
                    std::cout << "unable to extract formulas for rule ";rule->print();
                }

            }
            return NOT_EXTRACTED;
        }
        void buildPrograms(const std::vector<std::vector<int>>& scc,const std::vector<int>&  sccLabel,std::unordered_map<std::string,int>& predToComponent){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                for(int predicateId : scc[componentId]){
                    std::string predicate = idToPredicate[predicateId];
                    auto rulesForPredicate = program.getRulesForPredicate(predicate);
                    for(int ruleId : rulesForPredicate){
                        const aspc::Rule* rule = &program.getRule(ruleId);
                        if(sccLabel[componentId] == TYPE_EAGER){
                            std::vector<int> formulaLabeling(rule->getFormulas().size(),UNK_TYPE);
                            int extracted = extractJoinRule(rule,ruleId,sccLabel,predToComponent,formulaLabeling);
                            if(extracted == EXTRACTED_JOIN){
                                std::vector<aspc::Literal> literals;
                                std::vector<aspc::ArithmeticRelation> ineqs;
                                std::string joinPredicate = "join"+std::to_string(ruleId);
                                if(!predicateToId.count(joinPredicate)){
                                    predicateToId[joinPredicate]=idToPredicate.size();
                                    idToPredicate.push_back(joinPredicate);
                                }
                                literals.push_back(aspc::Literal(false,aspc::Atom(joinPredicate,joinRuleTerms[ruleId])));
                                for(unsigned i=0; i<rule->getFormulas().size();i++){
                                    const aspc::Formula* f = rule->getFormulas().at(i);
                                    if(formulaLabeling[i] == TYPE_EAGER){
                                        if(f->isLiteral()) literals.push_back(*((const aspc::Literal*)f));
                                        else ineqs.push_back(*((const aspc::ArithmeticRelation*)f));
                                    }
                                }
                                eagerPrg.addRule(aspc::Rule(rule->getHead(),literals,ineqs,false));
                            }else if(extracted == NOT_EXTRACTED){
                                eagerPrg.addRule(*rule);
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
                std::vector<int> formulaLabeling(rule->getFormulas().size(),UNK_TYPE);
                int extracted = extractJoinRule(rule,ruleId,sccLabel,predToComponent,formulaLabeling);
                if(extracted == EXTRACTED_JOIN){
                    std::vector<aspc::Literal> literals;
                    std::vector<aspc::ArithmeticRelation> ineqs;
                    std::string joinPredicate = "join"+std::to_string(ruleId);
                    if(!predicateToId.count(joinPredicate)){
                        predicateToId[joinPredicate]=idToPredicate.size();
                        idToPredicate.push_back(joinPredicate);
                    }
                    literals.push_back(aspc::Literal(false,aspc::Atom(joinPredicate,joinRuleTerms[ruleId])));
                    for(unsigned i=0; i<rule->getFormulas().size();i++){
                        const aspc::Formula* f = rule->getFormulas().at(i);
                        if(formulaLabeling[i] == TYPE_EAGER){
                            if(f->isLiteral()) literals.push_back(*((const aspc::Literal*)f));
                            else ineqs.push_back(*((const aspc::ArithmeticRelation*)f));
                        }
                    }
                    eagerPrg.addRule(aspc::Rule({},literals,ineqs,false));
                }else if(extracted == NOT_EXTRACTED){
                    eagerPrg.addRule(*rule);
                }
            }
            std::cout << "------------- DATALOG -------------"<<std::endl;
            datalogPrg.print();
            std::cout << "------------- EAGER -------------"<<std::endl;
            eagerPrg.print();
            std::cout << "------------- LAZY -------------"<<std::endl;
            lazyPrg.print();
        }
        void printProgramBySCC(const std::vector<std::vector<int>>& scc,const std::vector<int>& sccLabel,int label){
            unsigned componentId = scc.size()-1;
            while (componentId >= 0){
                if(sccLabel[componentId] == label){
                    std::cout << "Component "<<componentId<<std::endl;
                    for(int pId : scc[componentId]){
                        std::string predicate = idToPredicate[pId];
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
        void splitProgram(){
            auto scc = dependencyGraph.SCC();
            if(scc.size() == 0) return;
            std::unordered_map<std::string,int> predicateToComponent;
            mapPredicateToComponent(scc,predicateToComponent);

            std::vector<int> sccStratLabel(scc.size(),UNK_STRATIFIED);
            labelStratified(sccStratLabel,scc);


            std::vector<int> sccLazyLabel(scc.size(),UNK_LAZY);
            for(unsigned i = 0;i<sccStratLabel.size(); i++){
                if(sccStratLabel[i] == NOT_STRATIFIED)
                    sccLazyLabel[i] = NOT_LAZY;
            }
            std::cout << "Component 0 is "<< (sccLazyLabel[0] == UNK_LAZY ? "unk" : sccLazyLabel[0] == LAZY ? "lazy" : "not lazy")<<std::endl;

            labelLazyness(scc,predicateToComponent,sccLazyLabel);
            std::cout << "--------- LAZYNESS ---------"<<std::endl;
            printProgramBySCC(scc,sccLazyLabel,LAZY);
            std::cout << "--------- NOT LAZYNESS ---------"<<std::endl;
            printProgramBySCC(scc,sccLazyLabel,NOT_LAZY);
            
            std::vector<int> sccTypeLabel(scc.size(),UNK_TYPE);
            labelType(sccTypeLabel,sccStratLabel,sccLazyLabel,scc);

            buildPrograms(scc,sccTypeLabel,predicateToComponent);        
        }
        
        
    public:
        const int UNK_LAZY  = 0;
        const int NOT_LAZY  = 1;
        const int LAZY      = 2;

        const int UNK_STRATIFIED = 0;
        const int STRATIFIED    = 1;
        const int NOT_STRATIFIED = 2;

        const int UNK_TYPE      = 0;
        const int TYPE_LAZY     = 1;
        const int TYPE_EAGER    = 2;
        const int TYPE_DATALOG  = 3;

        const int DATALOG_BODY      = 0;
        const int EXTRACTED_JOIN    = 1;
        const int NOT_EXTRACTED     = 2;

        Analyzer(const aspc::Program& p):program(p){
            buildDependecyGraph();
            splitProgram();
        }

        const aspc::Program& getDatalog()const {return datalogPrg;}
        const aspc::Program& getEager()const {return eagerPrg;}
        const aspc::Program& getLazy()const {return lazyPrg;}

        const std::unordered_map<std::string,unsigned> getPredicateToId()const {return predicateToId;}
        const std::vector<std::string> getIdToPredicate()const {return idToPredicate;} 
        
};
#endif