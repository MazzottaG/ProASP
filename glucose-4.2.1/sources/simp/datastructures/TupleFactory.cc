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
#include "TupleFactory.h"
#include "../../core/Solver.h"

TupleLight TupleFactory::bufferTuple;
bool TupleFactory::usedFindNoSet=false;
std::vector<unsigned> TupleFactory::EMPTY_WATCHER;
// std::vector<AbstractPropagator*> TupleFactory::EMPTY_WATCHER;
