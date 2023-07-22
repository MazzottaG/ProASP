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

/* 
 * File:   Indentation.h
 * Author: bernardo
 *
 * Created on March 10, 2016, 5:22 PM
 */

#ifndef INDENTATION_H
#define	INDENTATION_H
#include <ostream>

class Indentation {
    
public:
    Indentation(int depth);
    Indentation(const Indentation & ind);
    friend std::ostream & operator<<(std::ostream& o, const Indentation & i);
    Indentation operator++(int);
    Indentation & operator++();
    Indentation operator--(int);
    Indentation & operator--();
    int getDepth()const {return depth;}
private:
    int depth;
};

#endif	/* INDENTATION_H */

