#ifndef ABSTRACTGENERATORCOMPILER_H
#define ABSTRACTGENERATORCOMPILER_H
#include <fstream>
#include "../utils/Indentation.h"
#include "../language/Rule.h"
#include "../utils/SharedFunctions.h"
#include "../rewriting/Analyzer.h"

class AbstractGeneratorCompiler{

    public:
        AbstractGeneratorCompiler(std::ofstream& file,int indentation,const aspc::Rule* r,const std::vector<std::string>& predNames,const std::unordered_map<std::string,unsigned>& predIds,const std::unordered_map<std::string,std::string>& predToStruct,std::unordered_set<std::string>& origPreds):outfile(file),ind(indentation),rule(r),predicateNames(predNames),predicateIds(predIds),auxliteral("aux_body"),predicateToStruct(predToStruct),originalPredicates(origPreds){
            // std::cout << "AbstractGeneratorCompiler::constructor Revised";
            // std::cout << "Debug original predicates ";
            // for(std::string pred : originalPredicates){
            //     std::cout << pred << " ";
            // }
            // std::cout << std::endl; 
        }

        void setRuleId(int id){ this->ruleId=id;}
        void setAnalyzer(Analyzer* analyzer){
            prgAnalizer=analyzer;
        }
        virtual void compileFromStarter(bool recursive);
        virtual void compileNoStarter(bool recursive);
        virtual std::string concreteClass(){return "BasicGenerator";}
        virtual void printAddClause(std::vector<unsigned>,bool){}
        virtual void printAddConstraintClause(std::vector<unsigned>,bool){}
        virtual void printAddSP(int index){}
        virtual bool leaveAggregateAtEnd()const{return true;}
        virtual unsigned printAggregateInitialization(std::unordered_set<std::string>&){}
        virtual void printUntrackLiteral(std::string tuplename){
            outfile << ind << "TupleFactory::getInstance().untrackLiteral("<<tuplename<<"->getId());\n";
        }
        virtual void printHeadDerivation(std::string);
        virtual int printTrackedCheck(std::string tuplename){ return 0;}
        void compileSingleStarter(bool recursive,std::vector<unsigned> order,unsigned starter);
        std::unordered_map<std::string,std::set<std::vector<unsigned>>> getUsedAuxMaps()const{return usedAuxMap;}
        std::vector<std::vector<unsigned>> reorderRule();

        std::ofstream& outfile;
        Indentation ind;
        const aspc::Rule* rule;

        const std::vector<std::string>& predicateNames;
        const std::unordered_map<std::string,unsigned>& predicateIds;

        std::unordered_map<std::string,std::set<std::vector<unsigned>>> usedAuxMap;
        const std::string auxliteral; 
        std::unordered_map<std::string,std::string> predicateToStruct;
        std::unordered_set<std::string> originalPredicates;

        Analyzer* prgAnalizer;
        int ruleId;
};
#endif