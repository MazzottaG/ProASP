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
 *  Copyright 2013 Mario Alviano, Carmine Dodaro, and Francesco Ricca.
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

#ifndef VECTORASSET_H
#define VECTORASSET_H

#include <cassert>
#include <iostream>
#include <vector>
#include <unordered_map>
using namespace std;

#define NOT_FOUND -1

template< class T >
/**
 * This class offers an efficient way to iterate over an unordered set.
 * 
 */
class VectorAsSet
{
    template< class TT >
    friend ostream& operator<<( ostream& out, const VectorAsSet< TT >& set );
    public:
        VectorAsSet(){}
        ~VectorAsSet(){}

        inline T& operator[]( unsigned idx );
        inline const T& operator[]( unsigned idx ) const;
        inline T& at( unsigned idx );
        inline const T& at( unsigned idx ) const;
        
        inline void clear();
        inline bool contains( const T& value ) const;
        
        inline bool empty() const;
        bool erase( const T& value );
        
        inline int find( const T& value ) const;
        bool insert( const T& value );
        
        inline unsigned size() const;
        
    private:
        VectorAsSet( const VectorAsSet& init );
        
        vector< T > data;
};

template< class T >
ostream&
operator<<(
    ostream& out,
    const VectorAsSet< T >& s )
{
    for( unsigned i = 0; i < s.size(); ++i )
        out << s.data[ i ] << " ";
    return out;
}

template< class T >
T&
VectorAsSet< T >::operator[](
    unsigned idx )
{
    assert( idx < data.size() );
    return data[ idx ];
}

template< class T >
const T&
VectorAsSet< T >::operator[](
    unsigned idx ) const
{
    assert( idx < data.size() );
    return data[ idx ];
}

template< class T >
T&
VectorAsSet< T >::at(
    unsigned idx )
{
    return operator[]( idx );
}

template< class T >
const T&
VectorAsSet< T >::at(
    unsigned idx ) const
{
    return operator[]( idx );
}

template< class T >
void
VectorAsSet< T >::clear()
{
    data.clear();
}

template< class T >
bool
VectorAsSet< T >::contains(
    const T& value ) const
{
    return find( value ) != NOT_FOUND;
}

template< class T >
bool
VectorAsSet< T >::empty() const
{
    return data.empty();
}

template< class T >
bool
VectorAsSet< T >::erase(
    const T& value )
{
    int position = find( value );
    if( position == NOT_FOUND)
        return false;
    
    data[ position ] = data.back();
    data.pop_back();
    
    return true;
}

template< class T >
int
VectorAsSet< T >::find(
    const T& value ) const
{
    typename std::vector< T >::iterator it = std::find(data.begin(),data.end(),value);
    return it == data.end() ? NOT_FOUND : std::distance(data.begin(),it);
}

template< class T >
bool
VectorAsSet< T >::insert(
    const T& value )
{
//    if( index.find( value ) != index.end() )
//        return false;
    // if( contains( value ) )
    //     return false;
    
//    index.insert( typename unordered_map< T, int >::value_type( value, data.size() ) );
    // index[ value ] = data.size();
    data.push_back( value );
    return true;
}

template< class T >
unsigned
VectorAsSet< T >::size() const
{
    return data.size();
}

#endif

