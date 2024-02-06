#ifndef DEPENDENCIESHANDLER_H
#define DEPENDENCIESHANDLER_H
#include <unordered_map> 
#include <unordered_set>
#include <vector>
#include "../utils/GraphWithTarjanAlgorithm.h"
#include "../language/Program.h"

class DependenciesHandler{
    public:
        DependenciesHandler(const aspc::Program& p):program(p),builtSCC(false),builtSCCFull(false){}
        void buildDG(bool full=false){
            unsigned programSize = program.getRulesSize();
            GraphWithTarjanAlgorithm* dg = full ? &full_dg : &pdg;
            for(unsigned ruleId = 0; ruleId < programSize; ruleId++){
                const aspc::Rule& r = program.getRule(ruleId);
                for(const aspc::Atom& a : r.getHead()){
                    auto it =local_predicates.emplace(a.getPredicateName(),localPredicatesName.size());
                    if(it.second){
                        dg->addNode(localPredicatesName.size());
                        localPredicatesName.push_back(a.getPredicateName());
                    }
                }
                for(const aspc::Literal& l : r.getBodyLiterals()){
                    if(l.isPositiveLiteral() || (full && l.isLiteral())){
                        auto it =local_predicates.emplace(l.getPredicateName(),localPredicatesName.size());
                        if(it.second){
                            dg->addNode(localPredicatesName.size());
                            localPredicatesName.push_back(l.getPredicateName());
                        }
                        for(const aspc::Atom& a : r.getHead()){
                            unsigned headPred =local_predicates[a.getPredicateName()];
                            dg->addEdge(it.first->second,headPred);
                        }
                    }
                }
                for(const aspc::ArithmeticRelationWithAggregate& agg: r.getArithmeticRelationsWithAggregate())
                    for(const aspc::Literal& l : agg.getAggregate().getAggregateLiterals()){
                        if(l.isPositiveLiteral() || (full && l.isLiteral())){
                            auto it =local_predicates.emplace(l.getPredicateName(),localPredicatesName.size());
                            if(it.second){
                                dg->addNode(localPredicatesName.size());
                                localPredicatesName.push_back(l.getPredicateName());
                            }
                            for(const aspc::Atom& a : r.getHead()){
                                unsigned headPred =local_predicates[a.getPredicateName()];
                                dg->addEdge(it.first->second,headPred);
                            }
                        }
                    }
            }
        }
        const std::vector<std::vector<int>>& computeSCC(bool full=false){
            if((!builtSCC && !full) || (!builtSCCFull && full)){
                if(!full)
                    builtSCC=true;
                else 
                    builtSCCFull=true;

                buildDG(full);
                if(!full)
                    scc = pdg.SCC();
                else
                    full_scc = full_dg.SCC();

                auto* comp = full ? &full_components : &components;
                auto* computed_scc = full ? &full_scc : &scc;
                for(unsigned componentId=0;componentId<computed_scc->size(); componentId++){
                    comp->push_back({});
                    std::unordered_set<std::string>* component=&comp->back();
                    for(unsigned i=0;i<computed_scc->at(componentId).size();i++){
                        component->insert(localPredicatesName[computed_scc->at(componentId)[i]]);
                    }
                }
            }
            return full ? full_scc : scc;
        }
        
        bool isBuiltSCC(bool full=false){return full ? builtSCCFull : builtSCC;}
        const std::vector<std::unordered_set<std::string>>& getComponents(bool full=false){return full ? full_components : components;}
        bool findDenpendecy(int from, int to, bool full=false){
            GraphWithTarjanAlgorithm* dg = full ? &full_dg : &pdg;
            std::vector<std::unordered_set<std::string>>* comps = full ? &full_components : &components;
            for(std::string from_pred : comps->at(from)){
                std::cout << "            Checking edges from "<<from_pred<<std::endl;
                int from_id = local_predicates[from_pred];
                for(std::string to_pred : comps->at(to)){
                    std::cout << "               to "<<to_pred<<std::endl;
                    int to_id = local_predicates[to_pred];
                    if(dg->existsEdge(from_id,to_id)) return true;
                }
            }
            return false;
        }

        std::vector<std::unordered_set<std::string>> getNotStratifiedComponents(){
            if(!builtSCCFull) computeSCC(true);
            std::vector<std::unordered_set<std::string>> notStratComps;
            for(const auto& comp : full_components){
                for(int ruleId = 0; ruleId < program.getRulesSize(); ruleId++){
                    const aspc::Rule* rule = &program.getRule(ruleId);
                    bool headInComponent = false;
                    for(const aspc::Atom& head : rule->getHead()){
                        if(comp.count(head.getPredicateName())){
                            headInComponent=true;
                            break;
                        }
                    }
                    bool negativeBodyInComponent = false;
                    for(const aspc::Formula* f : rule->getFormulas()){
                        if(f->isLiteral() && !f->isPositiveLiteral()){
                            const aspc::Literal* lit = (const aspc::Literal*)f;
                            if(comp.count(lit->getPredicateName())){
                                negativeBodyInComponent=true;
                                break;
                            }
                        }
                    }
                    if(headInComponent && negativeBodyInComponent){
                        notStratComps.push_back(comp);
                    }
                }
            }
            return notStratComps;
        }
    private:
        aspc::Program program;
        std::unordered_map<std::string,unsigned> local_predicates;
        std::vector<std::string> localPredicatesName;
        
        GraphWithTarjanAlgorithm pdg;
        std::vector<std::vector<int>> scc;
        std::vector<std::unordered_set<std::string>> components;
        
        GraphWithTarjanAlgorithm full_dg;
        std::vector<std::vector<int>> full_scc;
        std::vector<std::unordered_set<std::string>> full_components;
        
        bool builtSCC;
        bool builtSCCFull;
};
#endif