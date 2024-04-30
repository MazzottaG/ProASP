edge(X,Y):-link(X,Y).
edge(Y,X):-link(X,Y).
:-edge(X,Y),assign(X,C),assign(Y,C).
colored(X):-assign(X,C).
:-node(X),not colored(X).
