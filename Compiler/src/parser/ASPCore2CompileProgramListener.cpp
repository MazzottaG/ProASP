#include "ASPCore2CompileProgramListener.h"

std::set<int> ASPCore2CompileProgramListener::watchedTerminalTypes = std::set<int>({
    ASPCore2Parser::SYMBOLIC_CONSTANT,
    ASPCore2Parser::VARIABLE,
    ASPCore2Parser::STRING,
    ASPCore2Parser::NUMBER,
    ASPCore2Parser::EQUAL,
    ASPCore2Parser::UNEQUAL,
    ASPCore2Parser::LESS,
    ASPCore2Parser::LESS_OR_EQ,
    ASPCore2Parser::GREATER,
    ASPCore2Parser::GREATER_OR_EQ,
    ASPCore2Parser::PLUS,
    ASPCore2Parser::DASH 
});

std::set<int> ASPCore2CompileProgramListener::forbiddenTerminalTypes = std::set<int>({
    ASPCore2Parser::TIMES,
    ASPCore2Parser::SLASH,
    ASPCore2Parser::BACK_SLASH
});
