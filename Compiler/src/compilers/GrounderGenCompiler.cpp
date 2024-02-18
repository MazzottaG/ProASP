#include "GrounderGenCompiler.h"

void GrounderGenCompiler::printAddConstraintClause(std::vector<unsigned> order,bool starter){
    std::unordered_set<std::string> boundVars;

    std::vector<int> formulaLabeling = originalRuleId >=0 ? prgAnalizer->getRemappedRuleBodyLabeling(originalRuleId) : std::vector<int>(rule->getFormulas().size(),prgAnalizer->NON_DATALOG_FORMULA);

    rule->addBodyVars(boundVars);
    for(int index : order){
        if(rule->getFormulas()[index]->isLiteral() && formulaLabeling[index] != prgAnalizer->DATALOG_FORMULA){
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
            if(aggregateData.isEqualAgg()){
                if(aggregateData.isBoundGen()){
                    outfile << ind << "clause.push_back(-aggId->getId());\n";
                    outfile << ind << "if(sum_index < subSetSums.size()-1) clause.push_back(nextAggId->getId());\n";
                }else{
                    outfile << ind << "clause.push_back(-aggId->getId());\n";
                    outfile << ind << "clause.push_back(nextAggId->getId());\n";
                }
            } else outfile << ind << "clause.push_back("<<sign<<"aggId->getId());\n";
        }
    }
    outfile << ind << "TupleFactory::getInstance().addNewInternalConstraint(clause);\n";
    outfile << ind << "clause.clear();\n";
}
void GrounderGenCompiler::printAddClause(std::vector<unsigned> order,bool starter){
    std::string terms= !starter ? "" : "starter->getId()";
    bool missingAggId=false;
    std::vector<int> formulaLabeling = originalRuleId >=0 ? prgAnalizer->getRemappedRuleBodyLabeling(originalRuleId) : std::vector<int>(rule->getFormulas().size(),prgAnalizer->NON_DATALOG_FORMULA);
    std::vector<int> clauseFormulas;
    std::cout << "Computing formula in body clause"<<std::endl;
    for(int index : order){
        std::cout << "   Considering formula: ";
        rule->getFormulas()[index]->print();
        std::cout << " as "<<(formulaLabeling[index] == prgAnalizer->DATALOG_FORMULA ? "EDB" : (formulaLabeling[index] == prgAnalizer->NON_DATALOG_FORMULA ? "IDB" : "Unknown"))<<std::endl;
        if(rule->getFormulas()[index]->isLiteral() && formulaLabeling[index]!=prgAnalizer->DATALOG_FORMULA){
            clauseFormulas.push_back(index);
            std::cout << "      Added in clause"<<std::endl;
        }
        if(rule->getFormulas()[index]->containsAggregate()) {clauseFormulas.push_back(index); std::cout << "      Added in clause"<<std::endl;}
    }
    for(int index : clauseFormulas){
        if(rule->getFormulas()[index]->isLiteral()){
            const aspc::Literal* lit = (const aspc::Literal*)rule->getFormulas()[index];
            if(terms != "")
                terms+=",";
            std::string sign = lit->isNegated() ? "-":"";
            terms+=sign+"tuple_"+std::to_string(index)+"->getId()";

            if(lit->isNegated()){
                outfile << ind++ << "if(tuple_"<<index<<" == NULL){\n";
                    // found false literal not generated yet
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
                        outfile << ind << "AuxMapHandler::getInstance().initTuple(tuple_"<<index<<");\n";
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

            if(aggregateData.isEqualAgg()){
                if(aggregateData.isBoundGen()){
                    if(terms != "") terms+=", ";
                    terms+= "aggId->getId()";
                    missingAggId=true;
                }else{
                    if(terms != "") terms+=", ";
                    terms+= "aggId->getId(),-nextAggId->getId()";
                }
            }else{
                std::string sign = aggr->isNegated() ? "-":"";
                if(terms != "")
                    terms+=",";
                terms+=sign+"aggId->getId()";
            }
        }
    }
    usedAuxInRuleCompletion=false;
    if(starter){
        int bodysize = clauseFormulas.size();
        if(bodysize == 0){
            //TODO Check what if rule is of the form a:-not b and not b is the starter
            //WARNING it assumes the recursive generator starts from positive literal
            outfile << ind << "Tuple* clauseTuple = starter;\n";
        }else{
            if(missingAggId){
                outfile<<ind << "std::vector<int> terms({"<<terms<<"});\n";
                outfile << ind << "if(sum_index < subSetSums.size()-1) terms.push_back(-nextAggId->getId());\n";
                outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause(terms);\n";
            }else outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
            usedAuxInRuleCompletion=true;
        }
    }else{
        int bodysize = clauseFormulas.size();
        if(bodysize == 1 && rule->getFormulas()[clauseFormulas[0]]->isPositiveLiteral()){
            outfile << ind << "Tuple* clauseTuple = tuple_"<<clauseFormulas[0]<<";\n";
        }else{
            if(missingAggId){
                outfile<<ind << "std::vector<int> terms({"<<terms<<"});\n";
                outfile << ind << "if(sum_index < subSetSums.size()-1) terms.push_back(-nextAggId->getId());\n";
                outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause(terms);\n";
            }else outfile << ind << "Tuple* clauseTuple = TupleFactory::getInstance().addNewInternalClause({"<<terms<<"});\n";
            usedAuxInRuleCompletion=true;
        }
    }
    // for(int index : order){
    //     if(rule->getFormulas()[index]->isLiteral()){
    //         outfile << ind << "std::cout <<"<<(rule->getFormulas()[index]->isPositiveLiteral() ? "\" -\"" : "\" \"")<<"; AuxMapHandler::getInstance().printTuple(tuple_"<<index<<");\n";
    //     }
    // }
    // outfile << ind << "std::cout << "<<auxliteral<<" << \" 0\"<<std::endl;\n";
}
unsigned GrounderGenCompiler::compileAggregate(std::unordered_set<std::string>& boundVars,const aspc::ArithmeticRelationWithAggregate* aggr){
    
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
    outfile << ind++ << "if(prop.second){\n";
        //Code for compiling aggregate set and add weighted literal to ground aggregate propagator
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
        std::unordered_set<std::string> currentBoundVars(boundVars);
        for(const aspc::Formula* f : orderedAggregateBody){
            std::cout << "         Compiling formula: "; f->print(); std::cout<<std::endl;
            if(f->isLiteral()){
                const aspc::Literal* lit = (const aspc::Literal*)f;
                if(lit->getPredicateName() == "") continue;
                if(lit->isBoundedLiteral(currentBoundVars)){
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
                        if(!lit->isVariableTermAt(k) || currentBoundVars.count(lit->getTermAt(k))){
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
                            if(!currentBoundVars.count(lit->getTermAt(k))){
                                outfile << ind << "int "<< lit->getTermAt(k)<< " = tupleAgg_"<<index<<"->at("<<k<<");\n";
                                currentBoundVars.insert(lit->getTermAt(k));
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
                if(f->isBoundedValueAssignment(currentBoundVars)){
                    outfile << ind << "int "<<ineq->getAssignmentStringRep(currentBoundVars)<<";"<<std::endl;
                    currentBoundVars.insert(ineq->getAssignedVariable(currentBoundVars));
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
    outfile << --ind << "} //closing new propagator if\n";
    auto storedTerms = aggregateData.aggId->getTerms();
    std::string aggIdTerms;
    for(unsigned tIndex = 0; tIndex<storedTerms.size()-1; tIndex++){
        if(aggIdTerms!="") aggIdTerms+=", ";
        aggIdTerms+=storedTerms[tIndex];
    }
    if(aggregateData.isEqualAgg()){
        unsigned closingPars = 0;
        if(aggregateData.isBoundGen()){

            //boundVars contains variables encountered in the body up to now
            std::string assignedVar = aggr->getAssignedVariable(boundVars);
            assert(aggr->getGuard().isSingleTerm());
            outfile << ind++ << "if(prop.second){\n";
            closingPars++;
                outfile << ind << "std::vector<int> subSetSums;\n";
                outfile << ind << "prop.first->second.computeSSSum(subSetSums);\n";
                outfile << ind++ << "for(unsigned sum_index = 0; sum_index < subSetSums.size(); sum_index++){\n";
                closingPars++;
                    outfile << ind << "int "<< assignedVar<<" = subSetSums[sum_index];\n";
                    outfile << ind << "Tuple* aggId = TupleFactory::getInstance().addNewInternalTuple({"<<aggIdTerms<<(aggIdTerms != "" ? ", ":"")<<assignedVar<<"},AuxMapHandler::getInstance().get_"<< aggregateData.aggId->getPredicateName()<<"(),true);\n";
                    outfile << ind << "if(sum_index < subSetSums.size()-1) "<<assignedVar<<" = subSetSums[sum_index+1];\n";
                    outfile << ind << "Tuple* nextAggId = TupleFactory::getInstance().addNewInternalTuple({"<<aggIdTerms<<(aggIdTerms != "" ? ", ":"")<<assignedVar<<"},AuxMapHandler::getInstance().get_"<< aggregateData.aggId->getPredicateName()<<"(),true);\n";
                    outfile << ind << assignedVar<<" = subSetSums[sum_index];\n";
                    
            boundVars.insert(assignedVar);
        }else{
            std::string guardTerm = aggr->getGuard().getStringRep();
            outfile << ind << "Tuple* aggId = TupleFactory::getInstance().addNewInternalTuple({" << aggIdTerms << (aggIdTerms != "" ? "," : "")<<guardTerm <<"},AuxMapHandler::getInstance().get_"<<aggregateData.aggId->getPredicateName()<<"(),true);\n";
            outfile << ind << "Tuple* nextAggId = TupleFactory::getInstance().addNewInternalTuple({" << aggIdTerms << (aggIdTerms != "" ? "," : "")<<guardTerm <<"+1},AuxMapHandler::getInstance().get_"<<aggregateData.aggId->getPredicateName()<<"(),true);\n";
        }
        outfile << ind++ << "for(Tuple* aggIdTuple: {aggId,nextAggId}){\n";
            outfile << ind << "auto res = aggIdTuple->setStatus(Undef);\n";
            outfile << ind++ << "if(res.second){\n";
                outfile << ind << "while (aggIdTuple->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
                outfile << ind << "prop.first->second.addBound(aggIdTuple,aggIdTuple->at("<<aggregateData.aggId->getTerms().size()-1<<"),false);\n";
            outfile << --ind << "}\n";
        outfile << --ind << "}\n";
        return closingPars;
    }else{
        std::string guardTerm = aggr->getGuard().getStringRep();
        if(aggr->isPlusOne()) guardTerm+="+1";
        outfile << ind << "Tuple* aggId = TupleFactory::getInstance().addNewInternalTuple({" << aggIdTerms << (aggIdTerms != "" ? "," : "")<<guardTerm <<"},AuxMapHandler::getInstance().get_"<<aggregateData.aggId->getPredicateName()<<"(),true);\n";
        outfile << ind << "auto resAggId = aggId->setStatus(Undef);\n";
        outfile << ind++ << "if(resAggId.second){\n";
            outfile << ind << "while (aggId->getId() >= solver->nVars()) {solver->setFrozen(solver->newVar(),true);}\n";
            outfile << ind << "prop.first->second.addBound(aggId,aggId->at("<<aggregateData.aggId->getTerms().size()-1<<"),false);\n";
        outfile << --ind << "}\n";
        return 0;
    }

}
unsigned GrounderGenCompiler::printAggregateInitialization(std::unordered_set<std::string>& boundedVars){
    std::cout << "Aggregate grounder compiler for: \n";
    aggregateData.print();
    const std::vector<const aspc::Formula*>* body = &rule->getFormulas();
    unsigned closingPars = 0;
    for(unsigned i = 0; i<body->size(); i++){
        if(body->at(i)->containsAggregate()){
            closingPars += compileAggregate(boundedVars,(const aspc::ArithmeticRelationWithAggregate*) body->at(i));
        }
    }
    return closingPars;
}
void GrounderGenCompiler::printAddSP(int index){
    outfile << ind << "TupleFactory::getInstance()."<<(usedAuxInRuleCompletion ? "addAuxForLiteral" : "addAtomForLiteral")<<"(head_"<<index<<"->getId(),clauseTuple->getId());\n";
}

int GrounderGenCompiler::printTrackedCheck(std::string tuplename){
    outfile << ind++ << "if(!TupleFactory::getInstance().isTracked("<<tuplename<<"->getId())){\n";
    return 1;
}