#ifndef LAZYPROPAGATOR_H
#define LAZYPROPAGATOR_H
#include <vector>
#include <chrono>
#include "AbstractLazyPropagator.h"
#include "TupleSignSet.h"
//#define DEBUG_PROP
//#define DEBUG_LAZY_PROP
class LazyPropagator{
private:
    std::vector<AbstractLazyPropagator *> propagators;
    std::vector<std::vector<int>> tuplesByPropagator;
    // keeps track of which predicate is watched by which component
    std::unordered_map<int, std::vector<int>> watchedPredicateToPropagators;
    // keeps track of which predicate is defined by which component
    std::unordered_map<int,int> predicateToPropagator;
    std::unordered_set<int> predicatedDefinedByPositiveProgram;
    std::unordered_set<int> alwaysToCheckTuples;
    std::unordered_set<int> currentlyToCheckTuples;
    //not false body literals found in propagateToFalse call
    TupleSignSet bodyLiteralsSet;
    std::vector<int> bodyLiterals;
    std::unordered_set<int> undefsSet;

    std::unordered_set<int> alwaysToCheckPredicates;
    std::unordered_set<int> trueEnqueued;
    //tuple to index in bodyLiterals up to which body literals must be removed
    std::unordered_map<int, int> tupleToBodyRemoveIndex;
    // bool restartFixpoint;
    bool propagationDone;
    bool truePropInPropFalse;
    static Glucose::Solver* s;
    int indexCurrentLevelTuplePropFalse;

    //used for keeping track of already explained tuples in propFalse
    std::unordered_set<int> alreadyExplained;
    LazyPropagator();

public:
    void getAlwaysToCheckTuples(std::unordered_set<int>&);
    void findAlwaysToCheckTuples();
    void addAlwaysToCheckTuple(int tupleId, int predicateId){
        if(alwaysToCheckPredicates.count(predicateId)){
            //std::cout << "Added " <<  tupleId << " in currentlyToCheckTuples\n";
            if(alwaysToCheckTuples.count(tupleId)){
                currentlyToCheckTuples.insert(tupleId);
            }
        }
    }
    void removeAlwaysToCheckTuple(int tupleId){
        //std::cout << "Removed " <<  tupleId << " from currentlyToCheckTuples\n";
        currentlyToCheckTuples.erase(tupleId);
    }

    static LazyPropagator &getInstance(){
        static LazyPropagator prop;
        return prop;
    }

    static void setSolver(Glucose::Solver* solver){
        s = solver; 
    }
    static Glucose::Solver* getSolver(){
        return s; 
    }

    bool isPredicateAlwaysToCheck(int predName){
        return alwaysToCheckPredicates.count(predName);
    }
    ~LazyPropagator(){
        for (AbstractLazyPropagator *p : propagators){
            delete p;
            p = nullptr;
        }
    }
    void clearWatchers(){
        for(int i = 0; i < propagators.size(); ++i){
            bool generatedProp;
            #ifdef DEBUG_LAZY_PROP
                    std::cout << "Clearing watchers for propagator " << propagators[i]->getId() << "\n";
            #endif
            tuplesByPropagator[propagators[i]->getId()].clear();
        }
    }
   
    std::pair<bool, Glucose::CRef> computeFixpointLevelZero(Glucose::vec<Glucose::Lit> &lits){
        trueEnqueued.clear();
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Fixpoint level zero of lazy propagator\n";
        #endif
        bool generated = false;
        std::pair<bool, Glucose::CRef> generatedPropAndConf = std::make_pair(false, Glucose::CRef_Undef);
        for (int i = 0; i < propagators.size(); ++i){ 
            generatedPropAndConf = propagators[i]->computeFixpointLevelZero(LazyPropagator::s, lits);
            if(generatedPropAndConf.second != Glucose::CRef_Undef)
                break;
            generated = generated || generatedPropAndConf.first;

        }
        return std::make_pair(generated, generatedPropAndConf.second);
    }
    
    std::pair<bool, Glucose::CRef> computeFixpoint(Glucose::vec<Glucose::Lit> &lits){
        trueEnqueued.clear();
        std::pair<bool, Glucose::CRef> generatedPropAndConf = std::make_pair(false, Glucose::CRef_Undef);
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Fixpoint of lazy propagator\n";
            for(unsigned i = 0; i < tuplesByPropagator.size(); ++i){
                std::cout << "Tuples for propagator " << propagators[i]->getId() << "\n"; 
                for(unsigned j = 0; j < tuplesByPropagator[i].size(); ++j){
                    AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(tuplesByPropagator[i][j]));
                    std::cout << " ";
                }
                std::cout << "\n";
            }
        #endif
        
        bool generated = false;
        for(int i = 0; i < propagators.size(); ++i){
            #ifdef DEBUG_LAZY_PROP
                    std::cout << "Calling propagator " << propagators[i]->getId() << "\n";
            #endif
            generatedPropAndConf = propagators[i]->computeFixpoint(LazyPropagator::s, tuplesByPropagator[propagators[i]->getId()], lits);
            if(generatedPropAndConf.second != Glucose::CRef_Undef)
                return generatedPropAndConf;
            generated = generated || generatedPropAndConf.first;
        }
        return generatedPropAndConf;
    }

    
    virtual void explainTrueLiteral(int var, Glucose::vec<Glucose::Lit> &propagationReason, std::unordered_set<int>* reasonSet = nullptr){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"ExplainTrue of lazy propagator for";
            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var));
            std::cout <<std::endl;
        #endif
        //std::cout <<"Inside explainTrueLiteral\n";
        std::vector<Glucose::Lit> toExplain;
        Glucose::Lit lit = Glucose::mkLit(var, false);
        Glucose::vec<Glucose::Lit> &litReason = TupleFactory::getInstance().getTupleFromInternalID(var)->getReasonLits();
        toExplain.push_back(lit);
        int indexCurrentLevelTuple = -1;
        int tupleId;
        Tuple *t;
        while (!toExplain.empty()){
            Glucose::Lit lit = toExplain.back();
            Tuple *tuple = TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(lit));
            // std::cout <<"Found ";
            // AuxMapHandler::getInstance().printTuple(tuple);
            // std::cout << " In toExplain of explainTrue\n";
            toExplain.pop_back();
            Glucose::vec<Glucose::Lit> &tupleReason = tuple->getReasonLits();
            if (tupleReason.size() > 0){
                // std::cout << "tupleReason size: " << tupleReason.size() << "\n";
                //special case for true
                if(TupleFactory::getInstance().isTupleFromGen(Glucose::var(tupleReason[0]))) propagationReason.push(tupleReason[0]);
                for(unsigned i = 1; i < tupleReason.size(); ++i){
                    bool sign = Glucose::sign(tupleReason[i]);
                    tupleId = Glucose::var(tupleReason[i]);
                    if(TupleFactory::getInstance().isTupleFromGen(tupleId) && s->levelFromPropagator(tupleId) > 0){
                        if(reasonSet){
                            if(!reasonSet->count(tupleId)){
                                reasonSet->insert(tupleId);
                                // std::cout << "Adding tuple from gen with id " << tupleId << " in true reason\n";
                                if(s->levelFromPropagator(tupleId) == s->currentLevel())
                                    indexCurrentLevelTuple = propagationReason.size();
                                propagationReason.push(Glucose::mkLit(tupleId, sign));
                            }
                        }else{
                            if(s->levelFromPropagator(tupleId) == s->currentLevel())
                                indexCurrentLevelTuple = propagationReason.size();
                            propagationReason.push(Glucose::mkLit(tupleId, sign));
                        }
                    }
                    else{
                        // std::cout <<"Add to explain" << Glucose::var(tupleReason[i]) << "\n";
                        toExplain.push_back(tupleReason[i]);
                    }
                }
            }
        }

        //DEBUG PRINT
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Reason in explain true of lazy prop for ";
            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var));            
            std::cout << ":";
            for(unsigned i = 0; i < propagationReason.size(); ++i){
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(propagationReason[i])));
                // std::cout << Glucose::var(propagationReason[i]);
                std::cout << " ";
            }
            std::cout<< std::endl;
        #endif
        //put current level tuple in position 1 if found
        if(indexCurrentLevelTuple != -1){
            Glucose::Lit lit = propagationReason[1];
            propagationReason[1] = propagationReason[indexCurrentLevelTuple];
            propagationReason[indexCurrentLevelTuple] = lit;
        }
    }

    virtual void explodeReasonLits(unsigned int var, Glucose::vec<Glucose::Lit> &propagationReason){
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Explode reason into vector for " << var << " - lazy propagator\n";
            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var));
            std::cout << std::endl;
        #endif
        std::vector<Glucose::Lit> toExplain;
        Glucose::Lit lit = Glucose::mkLit(var, false);

        int tupleId;
        Tuple *t;
        int currentLevelTupleIndex = -1;
        //SP has a small size and creating additional
        //data structures for avoiding a copys is a useless burden 
        Glucose::vec<Glucose::Lit> spCopy;
        spCopy.push(propagationReason[0]);
        for(unsigned i = 1; i < propagationReason.size(); ++i){
            tupleId = Glucose::var(propagationReason[i]);
            if(TupleFactory::getInstance().isTupleFromGen(tupleId)){
               spCopy.push(propagationReason[i]);
                if(currentLevelTupleIndex == -1 && s->levelFromPropagator(tupleId) == s->currentLevel())
                    currentLevelTupleIndex = i;
            }else{
                toExplain.push_back(propagationReason[i]);
            }
        }
        propagationReason.clear();
        for(unsigned i = 0 ; i < spCopy.size(); ++i){
            propagationReason.push(spCopy[i]);
        }
        while (!toExplain.empty()){
            // std::cout << "To explain in explodeLits: ";
            // AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(toExplain.back())));
            // std::cout << "\n";
            Glucose::Lit lit = toExplain.back();
            Tuple *tuple = TupleFactory::getInstance().getTupleFromInternalID(Glucose::var(lit));
            tupleId = tuple->getId();
            toExplain.pop_back();
            Glucose::vec<Glucose::Lit> &tupleReason = tuple->getReasonLits();
            if(tupleReason.size() > 0){
                for (unsigned i = 1; i < tupleReason.size(); ++i){
                    bool sign = Glucose::sign(tupleReason[i]);
                    tupleId = Glucose::var(tupleReason[i]);
                    if(TupleFactory::getInstance().isTupleFromInputInterface(tupleId)){
                        propagationReason.push(Glucose::mkLit(tupleId, sign));
                        if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(Glucose::var(lit))  && s->levelFromPropagator(Glucose::var(lit)) == s->currentLevel())
                            currentLevelTupleIndex = tupleReason.size();
                    }
                    else{
                        toExplain.push_back(tupleReason[i]);
                    }
                }
            }
            else{
                // std::cout <<"Empty reason for ";
                // AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(tupleId));
                // std::cout << "\n";
                if(!TupleFactory::getInstance().isFact(tupleId)){
                    //propagationReason[currentPos] = Glucose::mkLit(tupleId, sign(lit));
                    propagationReason.push(Glucose::mkLit(tupleId, sign(lit)));
                    if(currentLevelTupleIndex == -1 && TupleFactory::getInstance().isTupleFromGen(tupleId)  && s->levelFromPropagator(tupleId) == s->currentLevel())
                        currentLevelTupleIndex = propagationReason.size() -1;
                }
            }
        }
        
        //DEBUG 
        #ifdef DEBUG_LAZY_PROP
            
            std::cout <<"Reason in explain true of lazy prop from conflict: " ;
            for(unsigned i = 0; i < propagationReason.size(); ++i){
                //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(var(propagationReason[i])));
                std::cout << Glucose::var(propagationReason[i]) << " ";
            }
            std::cout<< std::endl;
        #endif
        #ifdef DEBUG_LAZY_PROP
            //When called from propFalse, current level tuple might already be known from outside
            if(currentLevelTupleIndex != -1)
                std::cout <<"Found current level tuple at position "<< currentLevelTupleIndex <<" : "<< Glucose::var(propagationReason[currentLevelTupleIndex])<<"\n";
        #endif
    }

    std::pair<bool, Glucose::CRef> propagateToFalse(Tuple* tuple, bool makePropagation = true){
        indexCurrentLevelTuplePropFalse = -1;
        undefsSet.clear();
        trueEnqueued.clear();
        #ifdef DEBUG_LAZY_PROP
            std::cout <<"Propagate to false of lazy propagator for tuple: ";
            AuxMapHandler::getInstance().printTuple(tuple);
            std::cout <<" with id " << tuple->getId() << "\n";
        #endif
        truePropInPropFalse = false;
        int predicateId = tuple->getPredicateName();
        if(predicateToPropagator.count(predicateId)){
            Glucose::vec<Glucose::Lit>& tupleReasons =  TupleFactory::getInstance().isLazyNegatedTuple(tuple->getId()) || (TupleFactory::getInstance().isTupleFromInputInterface(tuple->getId()) && !s->isAssigned(tuple->getId())) ? tuple->getReasonLits() : s->getReasonClause();
            tupleReasons.clear();
            std::unordered_set<int> reasonSet;
            reasonSet.clear();
            int lastTupleBeforePropagateToFalse = TupleFactory::getInstance().getLastId();
            tupleReasons.push(Glucose::mkLit(tuple->getId(), true));
            reasonSet.insert(tuple->getId());
            propagationDone = false;
            std::pair<bool, Glucose::CRef> propagatedAndConf =  propagators[predicateToPropagator[predicateId]]->propagateToFalse(LazyPropagator::s, tuple, tuple, tupleReasons, reasonSet, makePropagation, false);
            //not propagated due to undef in some body or propagation failed due to a conflict
            if(!propagatedAndConf.first || propagatedAndConf.second == Glucose::CRef_Undef){
                PositiveProgramFactory::getInstance().removeToCheckTuple(tuple->getId());
            }
            removeBodyLiteralsAddedByTuple(tuple->getId(), false);
            tupleToBodyRemoveIndex.clear();

            assert(bodyLiteralsSet.size() == 0);
            assert(bodyLiterals.size() == 0);
            assert(undefsSet.size() == 0);
            TupleFactory::getInstance().deleteDummies();
            alreadyExplained.clear();
            return propagatedAndConf;
        }
        return std::make_pair(false, Glucose::CRef_Undef);
    }
    void switchIfNoCurrentLevelTupleFound(int pos, Glucose::vec<Glucose::Lit>& reason){
        //std::cout <<"Inside switch\n";
        if(indexCurrentLevelTuplePropFalse != -1 || reason.size() == 1)
            return;
        //std::cout <<"switching\n";
        Glucose::Lit lit = reason[1];
        reason[1] = reason[pos];
        reason[pos] = lit;
    }
    
    void addExplainingTuple(int id){
        //std::cout <<"Added tupleToBodyRemoveIndex id: " << id << " body literals size: " << bodyLiterals.size() << "\n";
        tupleToBodyRemoveIndex.emplace(std::make_pair(id, bodyLiterals.size()));
    }

    bool addBodyLiteral(int id, bool sign){
        //std::cout << "Add body literal in vec ";
        // std::cout << id;
        //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(id));
        //std::cout << "\n";
        if(bodyLiteralsSet.insert(id, sign)){
            if(id > 0 && TupleFactory::getInstance().getTupleFromInternalID(id)->isUndef())
            undefsSet.insert(id);
            bodyLiterals.push_back(id);
            return true;
        }
        return false;
    }
    void removeLastBodyLiteral(int id){
        assert(bodyLiterals[bodyLiterals.size()-1] == id);
        bodyLiteralsSet.erase(id);
        undefsSet.erase(id);
        
        //std::cout <<"Removing body literal ";
        //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(id));
        // std::cout << id;
        //std::cout << "\n";
        bodyLiterals.pop_back();
    }
    void printBodyLiterals(){
        std::cout << "Printing body literals: ";
        for(unsigned i = 0; i < bodyLiterals.size(); ++i){
            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(bodyLiterals[i]));
            std::cout << " ";
        }
        std::cout <<"\n";
    }
    int getUndefsBodySize(){
        return undefsSet.size();
    }
    int getBodySize(){
        return bodyLiterals.size();
    }

    void addPossibleSupportsForTuple(int id){
        #ifdef DEBUG_LAZY_PROP
            std::cout<<"Saving possible supports for tuple ";// << id;
            AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(id)); 
            std::cout<<" : ";
        #endif
        //there must be some body literal to save
        assert(bodyLiterals.size() > 0);
        for(int i = 0; i < bodyLiterals.size(); ++i){
            #ifdef DEBUG_LAZY_PROP
                std::cout <<bodyLiterals[i];
                AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(bodyLiterals[i]));
                std::cout << " ";
            #endif
            PositiveProgramFactory::getInstance().addPossibleSupportForTuple(id, bodyLiterals[i], bodyLiteralsSet.signOf(bodyLiterals[i]));
        }
        #ifdef DEBUG_LAZY_PROP
            //std::cout <<" Tuple factory had "<<TupleFactory::getInstance().propagatedByLazyPropTuples.size() << " tuples propagated by lazy prop\n";
            std::cout<<"\n";
        #endif
    }

    void storeBodyLiteralsFromTuple(int tuple, TupleSignSet& lits){
        //std::cout <<"Storing body literals for tuple: " << tuple << " ->\n";
        assert(tupleToBodyRemoveIndex.count(tuple) != 0);
        assert(lits.size() == 0);
        //std::cout << tupleToBodyRemoveIndex.count(tuple) << "\n";
        int tupleId;
        //std::cout << "Doing store body literals from " << tupleToBodyRemoveIndex.at(tuple) << "to " << bodyLiterals.size() <<"\n";
        for(unsigned i = tupleToBodyRemoveIndex.at(tuple); i < bodyLiterals.size(); ++i){
            // AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(bodyLiterals.at(i)));
            //std::cout << " \n";
            tupleId = bodyLiterals.at(i);
            //std::cout <<"Before insert of " << tupleId << "\n";
            lits.insert(tupleId, bodyLiteralsSet.signOf(tupleId));
            //std::cout <<"After insert\n";
        }
        //std::cout <<"\n";
    }
    
    void addEnqueued(int id){
        trueEnqueued.insert(id);
    }
    
    bool alreadyEnqueued(int id){
        return trueEnqueued.count(id) > 0;
    }

    std::vector<int>& getBodyLiterals(){
        return bodyLiterals;
    }

    //remove body literals added from tuple id
    void removeBodyLiteralsAddedByTuple(int id, bool noErase = true){
        if(tupleToBodyRemoveIndex.count(id)){
            // std::cout <<"Removing added body literals by " << id << " should remove up to " << tupleToBodyRemoveIndex[id] << "\n";
            for(int i = bodyLiterals.size() -1; i >= tupleToBodyRemoveIndex.at(id); --i){
                // std::cout << "Removing at index " << i << "\n";
                bodyLiteralsSet.erase(bodyLiterals.at(i));
                undefsSet.erase(bodyLiterals.at(i));
                //std::cout <<"Removing ";
                //AuxMapHandler::getInstance().printTuple(TupleFactory::getInstance().getTupleFromInternalID(bodyLiterals.back())); 
                //std::cout << " from bodyLiterals\n";
                bodyLiterals.pop_back();
            }
            if(!noErase)
                tupleToBodyRemoveIndex.erase(id);
        }
        //std::cout <<"After removeBodyLiterals by " << id << "\n";
    }
    
    AbstractLazyPropagator *getPropagatorFromPredicateId(int predId){
        assert(predicateToPropagator.count(predId));
        return propagators[predicateToPropagator[predId]];
    }

    void addAlreadyExplainedTuple(int id){
        //std::cout <<"Added alreadyExplained tuple " << id << "\n";
        alreadyExplained.insert(id);
    }
    bool isTupleAlreadyExplained(int id){
        return alreadyExplained.count(id) > 0;
    }

    void attachWatched(int tupleId){
        int tuplePred = TupleFactory::getInstance().getTupleFromInternalID(tupleId)->getPredicateName();
        for(int propagatorId : watchedPredicateToPropagators[tuplePred]){
            tuplesByPropagator[propagatorId].push_back(tupleId);
        }
    }
    bool isPredicateDefinedInPositiveProgram(int predicateName){
        return predicatedDefinedByPositiveProgram.count(predicateName) > 0;
    }
    
    void setPropagationDone(bool propDone){
        propagationDone = propDone;
    }
    
    bool isPropagationDone(){
        return propagationDone;
    }
    void setTruePropInPropFalse(bool value){
        truePropInPropFalse = value;
    }
};
#endif /*LAZYPROPAGATOR_H*/
