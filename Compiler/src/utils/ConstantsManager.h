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

#ifndef CONSTANTSMANAGER_H
#define	CONSTANTSMANAGER_H

#include <unordered_map>
#include <vector>
#include <string>
#include <unordered_set>

class ConstantsManager {
public:
    static ConstantsManager& getInstance() {
        static ConstantsManager instance;
        return instance;
    }
    ConstantsManager();
    int mapConstant(const std::string & constant);
    std::string unmapConstant(int mapped) const;
    const std::string & getPredicateName(const std::string & predicateName);

private:
    std::unordered_map<std::string, int> constantToIntMap;
    std::vector<std::string> inverseMap;
    int constantsCounter;
    std::unordered_set<std::string> predicateNames;
};

#endif	/* CONSTANTSMANAGER_H */

