#ifndef CHOICE_REWRITER_H
#define CHOICE_REWRITER_H
#include <algorithm>
#include "../language/Program.h";


// enum CompileChoiceOption{
//     COMPILE_NORMALS, COMPILE_CONSTRAINTS, GROUND_NORMALS, GROUND_CONSTRAINTS, NO_OPTION 
// };

enum CompileChoiceOption{
    COMPILE_ALL, COMPILE_NORMALS, COMPILE_CONSTRAINTS, GROUND_ALL, NO_OPTION 
};
class ChoiceRewriter{
    private:
        aspc::Program rewrittenProgram;
        std::vector<bool> ruleLabels;
        unsigned newFirstRuleIndex;
        unsigned newFirstChoiceRuleIndex;
        CompileChoiceOption compileChoiceOption;
        bool removeChoices;

    public:
    static std::string CHOICE_SET_ATOM_NAME;
    static std::string GENERIC_VARIABLE_NAME;
    static std::string CHOICE_OPTION_SPECIFIER;
    static std::string CHOICE_OPTION_REWRITE;
    static std::string NEG_PREDICATE_PREFIX;
    static std::unordered_map<std::string, CompileChoiceOption> CHOICE_COMPILE_OPTIONS;

    ChoiceRewriter();
    void setCompileChoiceOption(CompileChoiceOption);
    void setRewriteOption(bool rewrite);
    CompileChoiceOption getCompileChoiceOption() const;
    bool toGroundNormalRules(bool) const;
    bool toGroundChoiceConstraints(bool) const;
    void rewriteChoiceRules(const aspc::Program&, bool);
    const aspc::Program& getRewrittenProgram() const;
    std::vector<bool> getRuleLabels() const;
};

#endif /*CHOICE_REWRITER_H*/