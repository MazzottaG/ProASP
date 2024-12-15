#ifndef TUPLESIGNSET_H
#define TUPLESIGNSET_H
#include <unordered_set>
struct IntBoolEntry {
    int value;
    bool sign;

    IntBoolEntry(int v, bool f) : value(v), sign(f) {}
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

class TupleSignSet {
    private:
        std::unordered_set<IntBoolEntry, IntBoolEntryHash, IntBoolEntryEq> entries;

    public:
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
#endif /*TUPLESIGNSET_H*/