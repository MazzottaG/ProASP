assign(X,C):-node(X),col(C),not nassign(X,C).
nassign(X,C):-node(X),col(C),not assign(X,C).
:-assign(X,C1),assign(X,C2),C1!=C2.

