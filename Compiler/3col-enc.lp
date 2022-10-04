color(r,N):-node(N),not color(g,N),not color(b,N).
color(g,N):-node(N),not color(r,N),not color(b,N).
color(b,N):-node(N),not color(r,N),not color(g,N).

:-arc(X,Y),color(X,C),color(Y,C).
