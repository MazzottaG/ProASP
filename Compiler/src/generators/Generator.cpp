#include "../solver/Generator.h"

#include "../generators/Comp_2_Gen.h"

#include "../generators/Comp_1_Gen.h"

#include "../generators/Comp_0_Gen.h"

Generator::Generator(){
    generators.push_back(new Comp_2_Gen());
    generators.push_back(new Comp_1_Gen());
    generators.push_back(new Comp_0_Gen());
}
