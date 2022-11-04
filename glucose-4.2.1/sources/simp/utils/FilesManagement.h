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
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   FileHasher.h
 * Author: bernardo
 *
 * Created on July 11, 2018, 3:15 PM
 */

#ifndef FILEHASHER_H
#define FILEHASHER_H
#include <string>

class FilesManagement {
public:
    FilesManagement();
    virtual ~FilesManagement();
    std::string computeMD5(const std::string & file_name);
    int tryGetLock(const std::string & path) const; 
    void releaseLock(int fd, const std::string & path) const;
    bool exists (const std::string& name) const;
private:
    void releaseLock(int fd, char const *lockName) const;
    int tryGetLock(char const *lockName) const;

};

#endif /* FILEHASHER_H */

