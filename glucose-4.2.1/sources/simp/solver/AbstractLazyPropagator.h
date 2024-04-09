#ifndef ABSTRACTLAZYPROPAGATOR_H
#define ABSTRACTLAZYPROPAGATOR_H

class AbstractLazyPropagator{
    public:
        virtual void computeFixpoint() = 0;
        virtual void explainTrueLiteral(int) = 0;
        virtual void checkLiteralStatus(std::vector<std::pair<int, bool>>) = 0;
};

#endif /*ABSTRACTLAZYPROPAGATOR_H*/