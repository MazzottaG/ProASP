/*
 *
 *  Copyright 2021  BLIND.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */
/*
 *
 *  Copyright 2016 Bernardo Cuteri, Alessandro De Rosis, Francesco Ricca.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 */

#include "ConstantsManager.h"
#include "SharedFunctions.h"
#include <climits>
#include <iostream>

using namespace std;

const int halfMaxInt = INT_MAX / 2;

ConstantsManager::ConstantsManager() : constantsCounter(halfMaxInt) {

}

int ConstantsManager::mapConstant(const std::string & key) {
    if (isInteger(key)) {
        return stoi(key);
    }
    if (!constantToIntMap.count(key)) {
        constantToIntMap[key] = constantsCounter;
        inverseMap.push_back(key);
        constantsCounter++;
        return constantsCounter - 1;
    }
    //TODO avoid duplicated access
    return constantToIntMap[key];
}

string ConstantsManager::unmapConstant(int mapped) const {
    if (mapped >= halfMaxInt) {
        return inverseMap[mapped - halfMaxInt];
    }
    return to_string(mapped);
    // return inverseMap[mapped];
}

const string& ConstantsManager::getPredicateName(const string& predicateName) {

    const auto & find = predicateNames.find(predicateName);
    if (find != predicateNames.end()) {
        return *find;
    }
    return *(predicateNames.insert(predicateName).first);
}
