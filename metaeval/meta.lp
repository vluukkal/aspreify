%
% Metaevaluator for answer set programs without variables as described in 
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% Assume that foo.lp contains the program.
% 1. Reify the program: ./aspreify foo.lp 
% 2. Combine this with the reified program: cat meta.lp foo.lp.reified > toeval.lp
% 3. Calculate the answer sets: smodels toval.lp | smodels 0 
%    answer/1 predicates show which atoms belong to the answer set.    
%

% meta eval
hold(H) :- rule(R), head(R,H), 
           hold(P) : body(R,P) : pos(P), 
           not hold(N) : body(R,N) : neg(N). 

answer(N) :- hold(A), pred(A,N), atom(A).

% unification of predicates for ground programs
atom(X) :- pos(X).
atom(X) :- neg(X).

% As the same atom may have several different IDs 
% we need to check for equivalence this way. 
% This is quadratic, but if we do this in parser
% we can skip it. 
sameatom(A1,A2) :- 
        atom(A1), atom(A2),
        A1 != A2, 
        pred(A1,P), 
        pred(A2,P).
        
hold(A1) :- hold(A2), sameatom(A1,A2), not between(A1,A2). 

% We want to prune the sameatoms
% basically, we want to look at seuqential number ids
% of the atoms. 
between(A1,A2) :- 
        atom(A1), atom(A2), atom(A3),
        A1 < A3, A3 < A2,
        sameatom(A1,A3), sameatom(A3,A2). 


hide.
show hold(_).
show answer(_).
