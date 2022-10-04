a(X,X+1):-b(X).
a(X,Y):-b(X),not c(Y),Y=X+1.