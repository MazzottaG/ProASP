#ifndef TUPLESIGNSETWITHHEAD_H
#define TUPLESIGNSETWITHHEAD_H
#include <unordered_set>
struct IntBoolEntry {
    int value;
    bool sign;

    IntBoolEntry(int v, bool f) : value(v), sign(f) {}
    IntBoolEntry() : value(0), sign(false) {}
};

struct IntBoolEntryHash {
    std::size_t operator()(const IntBoolEntry& entry) const {
        return std::hash<int>()(entry.value);
    }
};

struct IntBoolEntryEq {
   bool operator()(const IntBoolEntry& e1, const IntBoolEntry& e2) const{
      return e1.value == e2.value;
   }
};

class TupleSignSetWithHead {
    private:
        IntBoolEntry head;
        std::unordered_set<IntBoolEntry, IntBoolEntryHash, IntBoolEntryEq> entries;

    public:
        TupleSignSetWithHead(){}
        void insertHead(int val, bool sign){
            head = IntBoolEntry(val,sign);   
        }
        IntBoolEntry getHead(){
            return head;
        }
        bool insert(int val, bool sign) {
            IntBoolEntry entry(val,sign);
            return entries.insert(IntBoolEntry(val, sign)).second;
        }
        void erase(int val){
            entries.erase(IntBoolEntry(val, false));
        }
        bool signOf(int val){
            auto it = entries.find(IntBoolEntry(val, false));
            assert(it != entries.end());
            return it->sign;
        }
        void clear(){
            entries.clear();
        }
        int size(){
            return entries.size();
        }
        auto begin() const { return entries.begin(); }
        auto end() const { return entries.end(); }
};
#endif /*TUPLESIGNSETWITHHEAD_H*/