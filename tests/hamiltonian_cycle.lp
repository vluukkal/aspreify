{ hc(X, Y) : arc(X, Y) } 1 :- vtx(X).

r(Y) :- arc(X, Y), hc(X, Y), initial(X).
r(Y) :- arc(X, Y), hc(X, Y), r(X).

 :- vtx(X), not r(X).

