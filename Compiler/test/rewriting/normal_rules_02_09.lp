a(X):-b(X,Y).
a(X,Y):-b(X),not c(Y),Y=X+1.