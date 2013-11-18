%
% A simple variabled answer set program to test metagrounding.
% Calculating a hamiltonian cycle in a graph. 
% Two answer sets:
% {oncycle(2,1) oncycle(3,2) oncycle(1,3)}
% {oncycle(3,1) oncycle(2,3) oncycle(1,2)}
% for:
% edge(1,2).
% edge(2,3).
% edge(3,1).
% edge(1,3).
% edge(3,2).
% edge(2,1).
% 

oncycle(X,Y) :- edge(X,Y), not other(X,Y).
other(X,Y) :- edge(X,Y), edge(X,Z), Y != Z, oncycle(X,Z). 

node(X) :- edge(X,Y).
node(Y) :- edge(X,Y).

% reached(X) :- start(X).
reached(1).
reached(Y) :- reached(X), oncycle(X,Y), edge(X,Y). 

:- not oncycle(Y,X) : edge(Y,X), node(X).
:- node(X), not reached(X).

#hide.
#show oncycle(X,Y).

% A graph with loops in two directions 
edge(1,2).
edge(2,3).
edge(3,1).
edge(1,3).
edge(3,2).
edge(2,1).

