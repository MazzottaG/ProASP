#include "GrounderGenCompiler.h"

void GrounderGenCompiler::printAddConstraintClause(std::vector<unsigned> order,bool starter){

    for(int index : order){
        if(rule->getFormulas()[index]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)rule->getFormulas()[index];
            std::string sign = lit->isNegated() ? "":"-";
            if(lit->isNegated()){
                outfile << ind++ << "if(tuple_"<<index<<" != NULL){\n";
                    outfile << ind << "clause.push_back(tuple_"<<index<<"->getId());\n";                        
                outfile << --ind << "}\n";
            }else{
                outfile << ind << "clause.push_back(-tuple_"<<index<<"->getId());\n";                        
            }
        }else if(rule->getFormulas()[index]->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*)rule->getFormulas()[index];
            std::string sign = aggr->isNegated() ? "":"-";
            outfile << ind << "clause.push_back("<<sign<<"aggId->getId());\n";
        }
    }
    outfile << ind << "TupleFactory::getInstance().addNewInternalConstraint(clause);\n";
    outfile << ind << "clause.clear();\n";
}
void GrounderGenCompiler::printAddClause(std::vector<unsigned> order,bool starter){
    std::string terms= !starter ? "" : "starter->getId()";
    for(int index : order){
        if(rule->getFormulas()[index]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)rule->getFormulas()[index];
            if(terms != "")
                terms+=",";
            std::string sign = lit->isNegated() ? "-":"";
            terms+=sign+"tuple_"+std::to_string(index)+"->getId()";

            if(lit->isNegated()){
                outfile << ind++ << "if(tuple_"<<index<<" == NULL){\n";
                //found false literal not generated yet
                    // std::cout << "Debug original predicates GrounderGenCompiler";
                    // for(std::string pred : originalPredicates){
                    //     std::cout << pred << " ";
                    // }
                    // std::cout << std::endl;
                    outfile << ind << "tuple_"<<index<<"=TupleFactory::getInstance().addNewInternalTuple({";
                    for(unsigned k=0; k<lit->getAriety(); k++){
                        if(k>0) outfile << ",";
                        outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                    }
                    outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"(),"<<(originalPredicates.count(lit->getPredicateName()) ? "false" : "true")<<");\n";
                    #ifdef DEBUG_GEN
                    outfile << ind << "std::cout << \"Added tuple \";AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";
                    #endif
                    outfile << ind << "const auto& insertResult = tuple_"<<index<<"->setStatus(Undef);\n";
                    outfile << ind++ << "if(insertResult.second){\n";
                        outfile << ind << "TupleFactory::getInstance().removeFromCollisionsList(tuple_"<<index<<"->getId());\n";
                        outfile << ind << "AuxMapHandler::getInstance().insertUndef(insertResult);\n";
                        outfile << ind << "while (tuple_"<<index<<"->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                        outfile << ind << "TupleFactory::getInstance().trackLiteral(tuple_"<<index<<"->getId());\n";
                    outfile << --ind << "}\n";                        
                outfile << --ind << "}\n";
                
            }
            // outfile << ind << "std::cout << -"<<auxliteral<<"<<\" \" <<"<<(lit->isNegated() ? "\" -\"" : "\" \"")<<"; AuxMapHandler::getInstance().printTuple(tuple_"<<index<<"); std::cout << std::endl;\n";
            // outfile << ind << "std::cout << -"<<auxliteral<<"<<\" \"<< "<<(rule->getFormulas()[index]->isPositiveLiteral() ? "" : "-")<<"tuple_"<<index<<"->getId() << \" 0\"<<std::endl;\n";
        }else if(rule->getFormulas()[index]->containsAggregate()){
            const aspc::ArithmeticRelationWithAggregate* aggr = (const aspc::ArithmeticRelationWithAggregate*)rule->getFormulas()[index];
            std::string sign = aggr->isNegated() ? "-":"";
            if(terms != "")
                terms+=",";
            terms+=sign+"aggId->getId()";
        }
    }

    if(starter){
        int bodysize = rule->getFormulas().size();
        if(bodysize == 1){
            assert(order.size()==0);
            outfile << ind << "Tuple* clauseTuple = starter;\n";
        }else{
            outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
        }
    }else{
        int bodysize = rule->getFormulas().size();
        if(bodysize == 1){
            assert(rule->getFormulas()[order[0]]->isPositiveLiteral());
            outfile << ind << "Tuple* clauseTuple = tuple_"<<order[0]<<";\n";
        }else{
            outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
        }
    }
    // for(int index : order){
    //     if(rule->getFormulas()[index]->isLiteral()){
    //         outfile << ind << "std::cout <<"<<(rule->getFormulas()[index]->isPositiveLiteral() ? "\" -\"" : "\" \"")<<"; AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";
    //     }
    // }
    // outfile << ind << "std::cout << "<<auxliteral<<" << \" 0\"<<std::endl;\n";
}
void GrounderGenCompiler::compileAggregate(std::unordered_set<std::string>& boundVars,const aspc::ArithmeticRelationWithAggregate* aggr){
    
    std::unordered_set<std::string> sharedVars;
    std::vector<std::string> terms;
    std::string terms_str;
    rule->addSharedVars(boundVars,terms,sharedVars,aggr,false);
    std::cout << "   Shared Vars: {\n";
    for(std::string t : terms) {
        std::cout << " "<<t<<std::endl;
        if(terms_str != "") terms_str+=",";
        terms_str+=t;
    }
    std::cout << "   }\n";
    
    outfile << ind << "auto prop = propagators.emplace(std::vector<int>({"<<terms_str<<"}),AggregatePropagator());\n";
    
    std::string aggIdTerms;
    for(unsigned k = 0; k<aggregateData.aggId->getAriety(); k++){
        if(aggIdTerms != "") aggIdTerms+=",";
        aggIdTerms+=aggregateData.aggId->getTermAt(k);
    }
    outfile << ind << "Tuple* aggId = TupleFactory::getInstance().addNewInternalTuple({"<<aggIdTerms<<"},AuxMapHandler::getInstance().get_"<< aggregateData.aggId->getPredicateName()<<"(),true);\n";
    outfile << ind << "auto res = aggId->setStatus(Undef);\n";
    outfile << ind++ << "if(res.second){\n";
        outfile << ind << "while (aggId->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
    outfile << --ind << "}\n";
    outfile << ind << "prop.first->second.addBound(aggId,"<<aggr->getGuard().getStringRep() << ( aggr->isPlusOne() ? "+1":"" ) <<",false);\n";

    std::cout << "   Compiling aggregate "; aggr->print(); std::cout << std::endl;
    std::cout << "      Reordering body ... " << std::endl;
    std::vector<aspc::Formula*> orderedAggregateBody;
    aggr->getOrderedAggregateBody(orderedAggregateBody,boundVars);
    for(unsigned i = 0; i<orderedAggregateBody.size(); i++){
        std::cout << "      Formula "<<i<<" "; 
        orderedAggregateBody[i]->print();
        std::cout << std::endl;
    }

    std::cout << "      Compiling body ... " << std::endl;
    int closingPars = 0;
    unsigned index = 0;
    for(const aspc::Formula* f : orderedAggregateBody){
        std::cout << "         Compiling formula: "; f->print(); std::cout<<std::endl;
        if(f->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)f;
            if(lit->getPredicateName() == "") continue;
            if(lit->isBoundedLiteral(boundVars)){
                outfile << ind << "Tuple* tupleAgg_"<<index<<"=TupleFactory::getInstance().find({";
                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(k>0) outfile << ",";
                    outfile << (lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")");
                }
                outfile << "}, AuxMapHandler::getInstance().get_"<<lit->getPredicateName()<<"());\n";
                if(lit->isNegated()){
                    outfile << ind++ << "if(tupleAgg_"<<index<<" == NULL || !tupleAgg_"<<index<<"->isTrue()){\n";
                }else{
                    outfile << ind++ << "if(tupleAgg_"<<index<<" != NULL && !tupleAgg_"<<index<<"->isFalse()){\n";
                    if(!rule->isConstraint())
                        closingPars += printTrackedCheck("tupleAgg_"+std::to_string(index));
                }
            
                closingPars++;
            }else{
                std::string prefix = "AuxMapHandler::getInstance().get_";
                std::string mapName = lit->getPredicateName()+"_";
                std::string terms = "";
                std::unordered_set<unsigned> boundIndices;
                std::vector<unsigned> boundTerms;
                std::string predStruct = predicateToStruct[lit->getPredicateName()];
                std::string structType = predStruct == "Vec" ? "std::vector<int>*" : "IndexedSet*";

                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(!lit->isVariableTermAt(k) || boundVars.count(lit->getTermAt(k))){
                        std::string term = lit->isVariableTermAt(k) || isInteger(lit->getTermAt(k)) ? lit->getTermAt(k) : "ConstantsManager::getInstance().mapConstant(\""+lit->getTermAt(k)+"\")";
                        mapName+=std::to_string(k)+"_";
                        terms += (terms != "" ? ","+term : term);
                        boundIndices.insert(k);
                        boundTerms.push_back(k);
                    }
                }
                usedAuxMap[lit->getPredicateName()].insert(boundTerms);
                outfile << ind << structType<<" tuplesAggU_"<<index<<" = &"<<prefix<<"u"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                outfile << ind << structType<<" tuplesAgg_"<<index<<" = &"<<prefix<<"p"<<mapName<<"()->getValues"<<predStruct<<"({"<<terms<<"});\n";
                
                outfile << ind++ << "for(auto i=tuplesAgg_"<<index<<"->begin(); i!=tuplesAggU_"<<index<<"->end(); i++){\n";
                closingPars++;
                    outfile << ind << "if(i == tuplesAgg_"<<index<<"->end()) i=tuplesAggU_"<<index<<"->begin();\n";
                    outfile << ind << "if(i == tuplesAggU_"<<index<<"->end()) break;\n";
                    outfile << ind << "Tuple* tupleAgg_"<<index<<"= TupleFactory::getInstance().getTupleFromInternalID(*i);\n";
                    outfile << ind++ << "if(tupleAgg_"<<index<<"!= NULL){\n";
                    closingPars++;
                for(unsigned k=0; k<lit->getAriety(); k++){
                    if(lit->isVariableTermAt(k) && !boundIndices.count(k)){
                        if(!boundVars.count(lit->getTermAt(k))){
                            outfile << ind << "int "<< lit->getTermAt(k)<< " = tupleAgg_"<<index<<"->at("<<k<<");\n";
                            boundVars.insert(lit->getTermAt(k));
                        }else{
                            outfile << ind++ << "if("<< lit->getTermAt(k)<< " == tupleAgg_"<<index<<"->at("<<k<<")){\n";
                            closingPars++;
                        }
                    }
                }
                if(!rule->isConstraint())
                    closingPars += printTrackedCheck("tupleAgg_"+std::to_string(index));
            }
        }else if(!f->containsAggregate()){
            const aspc::ArithmeticRelation* ineq = (const aspc::ArithmeticRelation*) f;
            if(f->isBoundedValueAssignment(boundVars)){
                outfile << ind << "int "<<ineq->getAssignmentStringRep(boundVars)<<";"<<std::endl;
                boundVars.insert(ineq->getAssignedVariable(boundVars));
            }else{
                outfile << ind++ << "if("<<ineq->getStringRep()<<"){"<<std::endl;
                closingPars++;
            }
        }
        index++;
    }
    std::string aggVar_str;
    for(std::string v : aggr->getAggregate().getAggregateVariables()){
        if(aggVar_str!="") aggVar_str+=",";
        aggVar_str+=v;
    }

    std::string aggSetTerms;
    for(std::string v : aggregateData.aggSet->getTerms()){
        if(aggSetTerms!="") aggSetTerms+=",";
        aggSetTerms+=v;
    }
    outfile << ind << "Tuple* aggSet = TupleFactory::getInstance().find({"<<aggSetTerms<<"},AuxMapHandler::getInstance().get_"<<aggregateData.aggSet->getPredicateName()<<"());\n";
    outfile << ind << "prop.first->second.addWeightedLiteral(aggSet,{"<<aggVar_str<<"},"<< (aggr->getAggregate().isSum() ? aggr->getAggregate().getAggregateVariables()[0] : "1")<<","<<(aggregateData.aggSet->isNegated() ? "true": "false")<<");\n";
    while(closingPars>0){
        outfile << --ind << "}\n";
        closingPars--;
    }
    return;
}
void GrounderGenCompiler::printAggregateInitialization(std::unordered_set<std::string>& boundedVars){
    std::cout << "Aggregate grounder compiler for: \n";
    aggregateData.print();
    const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
    for(unsigned i = 0; i<body->size(); i++){
        if(body->at(i)->containsAggregate()){
            compileAggregate(boundedVars,(const aspc::ArithmeticRelationWithAggregate*) body->at(i));
        }
    }
    
}
void GrounderGenCompiler::printAddSP(int index){
    outfile << ind << "TupleFactory::getInstance()."<<(rule->getFormulas().size() != 1 ? "addAuxForLiteral" : "addAtomForLiteral")<<"(head_"<<index<<"->getId(),clauseTuple->getId());\n";
}

int GrounderGenCompiler::printTrackedCheck(std::string tuplename){
    outfile << ind++ << "if(!TupleFactory::getInstance().isTracked("<<tuplename<<"->getId())){\n";
    return 1;
}