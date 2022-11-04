#ifndef INPUTREADER_H
#define INPUTREADER_H
#include "../datastructures/TupleFactory.h"
#include "../utils/ConstantsManager.h"
#include "../solver/AuxMapHandler.h"
#include <fstream>
#include <chrono>


class InputReader{
    public:
        InputReader(const std::string& filename):factsCount(0),inputFile(filename){}
        void readFacts(Glucose::Solver * solver){
            string line;
            if (inputFile.is_open()){
                while ( getline (inputFile,line) ){
                    unsigned start=0;
                    bool skip = false;
                    for(unsigned i=0;i<line.size();i++){
                        if(line[i] == '.'){
                            skip=true;
                            parseTuple(line.substr(start,i-start),solver);
                            start=i+1;
                        }else if(skip){
                            if(line[i]<'a' || line[i]>'z'){
                                start=i+1;
                            }else{
                                skip=false;
                            }
                        }
                    }
                }
                inputFile.close();
                
            }
            else cout << "Unable to open file"<<std::endl; 
        }
        void parseTuple(const std::string & literalString,std::ofstream& outfile) {
            std::vector<int> terms;
            std::string predicateName;
            unsigned i = 0;
            for (i = 0; i < literalString.size(); i++) {
                if (literalString[i] == '(') {
                    predicateName = literalString.substr(0, i);
                    break;
                }
                if (i == literalString.size() - 1) {
                    predicateName = literalString.substr(0);
                }
            }
            for (; i < literalString.size(); i++) {
                char c = literalString[i];
                if ((c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' || c == '-') {
                    int start = i;
                    int openBrackets = 0;
                    while ((c != ' ' && c != ',' && c != ')') || openBrackets > 0) {
                        if (c == '(') {
                            openBrackets++;
                        } else if (c == ')') {
                            openBrackets--;
                        }
                        i++;
                        c = literalString[i];
                    }
                    terms.push_back(ConstantsManager::getInstance().mapConstant(literalString.substr(start, i - start)));
                }
            }
            TupleLight* tuple=TupleFactory::getInstance().addNewInternalTuple(terms, AuxMapHandler::getInstance().getPredicateId(predicateName));
            const auto& insertResult = tuple->setStatus(True);
            if(insertResult.second){
                factsCount++;
                TupleFactory::getInstance().removeFromCollisionsList(tuple->getId());
                AuxMapHandler::getInstance().insertTrue(insertResult);

                outfile << tuple->getId() << " 0"<<std::endl;

            }
        }

        unsigned getFactsCount()const {return factsCount;}

    private:
        std::ifstream inputFile;
        unsigned factsCount;
};
#endif