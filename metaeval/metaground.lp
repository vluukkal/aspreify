%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% Assume that foo.lp contains the program.
% 1. Reify the program: ./aspreify foo.lp 
% 2. Combine this with the reified program: cat metaground.lp foo.lp.reified > toeval.lp
% 3. Calculate the answer sets: smodels toval.lp | smodels 0 
%    

% Separate postive facts from others
nonfact(R) :- rule(R), body(R,A).
nonfact(R) :- rule(R), head(R,H),alist(H,N,V),var(V,S). 
poscond(R,A) :- rule(R), body(R,A), pos(A). 

fact(A) :- assert(A). % , not nonfact(A). 

fact(R) :- head(R,H), rule(R), not nonfact(R). % not body(R,_).

% Pick one rule out of many to be grounded 
% This generates stable models for each rule 
ground(R) :- not other(R), nonfact(R).
other(R1) :- ground(R2), nonfact(R1), nonfact(R2), R1 != R2. 

% Handle the arguments 
% fact(R) :- rule(R), not nonfact(R).

% Combine constant predicates with their value associations 
carg(A,N,S) :- alist(A,N,C), cnst(C,S).
cargn(P,A,N,S) :- carg(A,N,S), pred(A,P). 

% A particular variable has been bound to a particular rule. 
%
% ruleid, varname, varid, varpos, predname
%
% For this to work properly, we'd need to be able to trace 
% from vargn back up to body which ay be more than one step.
rulevar(R,A,V,P,N) :- body(R,B), vargn(P,B,N,A,V).

%match(A,F) :- not differ(A,F), poscond(R,A), ground(R), fact(F). 
%differ(A,F) :- pred(A,S1), pred(F,S2), S1 != S2,
%	       poscond(R,A), ground(R), fact(F).
%differ(A,F) :- carg(A,N,S1), carg(F,N,S2), S1 != S2, 
%	       poscond(R,A), ground(R), fact(F). 
%differ(A,F1) :- match(A,F2), poscond(R,A), ground(R),
%	     	fact(F1), fact(F2). 

% predid, pos, vid, vname, 
varg(A,N,V,S) :- alist(A,N,V), var(V,S).
vargn(P,A,N,S,V) :- varg(A,N,V,S), pred(A,P).

%value(R,S1,S2) :- varg(A,N,S1), carg(F,N,S2), match(A,F),
%	       	  poscond(R,A), ground(R), fact(F). 


% Now we need to ground the variables,
% For each 
% rulevar(R,A,V,P,N)
% where R - ruleid 
% 	A - variable name 
% will identify a variable to be ground and 
%       V - is the variable ID, multiple of which may map to same name
%       P - the predicate name associated with the variable 
%       N - the argument position in predicate P
%
% we need to pick a domain variable, e.g. a constant 
% cargn(P,C,N,X)
% where P - is the name of the predicate
%       C - is the ID of this constant 
%       N - is the position of this value in P
%       X - is the value for this position 
% And make it only for the ruel that has chosen to be ground 
% mkassign1(R,A,P,N,X) :- rulevar(R,A,V,P,N), cargn(P,C,N,X), ground(R).
mkassign1(R,A,P,N,X) :- rulevar(R,A,V,P,N), cargn(P,C,N,X).


% Problem: we get more than one solution per variable as
% there are more rulevars as there are actual variables. 
% Project mkassign, but selvar will never be derived?
mkassign2(R,A,X) :- mkassign1(R,A,P,N,X). %, selvar(A).

% There can only be one assignment per variable.
% Note that "assign" is a reserved word in lparse!
1 {mkassign(R,A,C) : mkassign2(R,A,C) } 1 :- 
  rulevar(R,A,V,P,N), ground(R).


