node(1..3).
edge(1,2).
edge(1,3).
edge(2,3).
col(X,r)|col(X,g)|col(X,b):-node(X).
:-edge(X,Y),col(X,C),col(Y,C).
