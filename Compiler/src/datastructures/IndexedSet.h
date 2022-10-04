#ifndef INDEXEDSET_H
#define INDEXEDSET_H
#include <iostream>
#include <set>
#include <list>
using namespace std;

struct Index
{
    Index(){

    }
    Index(int v, std::list<int>::iterator it){
        val=v;
        this->it=it;
    }
    Index(int v){
        val=v;
    }
    int val;
    list<int>::iterator it;
};
struct Comp{
    bool operator()(const Index& i1, const Index& i2)const{
        return i1.val>i2.val;
    }
};
//template<class T>
class IndexedSet{
    private:
        set<Index,Comp> storage;
        list<int> iterable;
    public:
        friend ostream& operator<< (ostream& out,const IndexedSet& s){
            for(int v : s.iterable){
                out<<v<<" ";
            }
            return out;
        }
        
        bool empty()const{
            return iterable.empty();
        }
        unsigned size()const{
            return iterable.size();
        }
        IndexedSet(){}
        void erase(int v){
            Index ind(v);
            const auto& index = storage.find(ind);
            if(index!=storage.end()){
                iterable.erase(index->it);
                storage.erase(index);
            }
        }
        pair<set<Index,Comp>::iterator,bool> insert (const int val){
            
            const auto& previous = storage.lower_bound(Index(val));
            if(previous == storage.end()){
                const auto& it = iterable.insert(iterable.end(),val);
                return {storage.emplace_hint(previous,Index(val,it)),true};
            }
            if(previous->val != val){
                const auto& it = iterable.insert(previous->it,val);
                return {storage.emplace_hint(previous,Index(val,it)),true};
            }
            return {storage.end(),false};

        }
        list<int>::const_iterator begin() const{
            return iterable.begin();
        }

        list<int>::const_iterator end() const{
            return iterable.end();
        }

        list<int>::iterator begin(){
            return iterable.begin();
        }

        list<int>::iterator end(){
            return iterable.end();
        }
};
#endif