a(X,Y):-b(X),Y=X+1.
a(X):-b(X,Y),not c(Y).