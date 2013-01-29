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

% How should we handle constraints?
nonfact(R) :- constraint(R), body(R,A).

fact(A) :- assert(A). % , not nonfact(A). 

fact(R) :- head(R,H), rule(R), not nonfact(R). % not body(R,_).

% Pick one rule out of many to be grounded 
% This generates stable models for each rule 
ground(R) :- not other(R), nonfact(R).
other(R1) :- ground(R2), nonfact(R1), nonfact(R2), R1 != R2. 


% Handle the arguments 
% fact(R) :- rule(R), not nonfact(R).

% We "draw lines" between the actual instances

% Generate all possible bindings
{sbindit(Rid,Predid,Jpredid) : rulepred(Rid,Predid) : assert(Aid) : rulepred(Aid,Jpredid)} :- ground(Rid). 

% Debugging with naming, not needed
vsbindit(Prednm,Predid,Jpredid) :- sbindit(Rid,Predid,Jpredid), pred(Predid,Prednm).

% Now limit them 

% Cannot be that justifying predicate is of different name 
:- sbindit(Rid,Predid,Jpredid),
   pred(Predid,Pn1),
   pred(Jpredid,Pn2),
   Pn1 != Pn2.


% Do not assign two different justifications to one Predid
:- 
   sbindit(Rid,Predid,Jpredid1),
   sbindit(Rid,Predid,Jpredid2),
   Jpredid1 != Jpredid2.

% Get the variables which have been assigned by sbindit 
boundv(Rid,Vn,Predid,Jpredid) :- 
   sbindit(Rid,Predid,Jpredid), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

% Keep track of justified predicates, those which are true
% by definition. This is bound to a single answer set,
% a single binding of variables to a single rule. 
ptrue(Predid) :- sbindit(Rid,Predid,Jpredid). 

% Try to push this true to derivations which are 
% obviously true, i.e based only on ptrue predicates. 
% But it may be that they are true only in 
% separate answer sets and thus cannot be propagated 
% within here. 

% Try to find simple (one-deep syntax tree) arithmetic expressions 
cmp(Rid,Eid,Op,Val1,Val2) :- 
  mkassign(Rid,Vn1,Val1), 
  mkassign(Rid,Vn2,Val2), 
  bexpr(Rid,Eid), 
  bop(Eid,Op),
  larg(Eid,Larg), 
  var(Larg,Vn1), 
  rarg(Eid,Rarg), 
  var(Larg,Vn2). 

pfalse(Eid) :- 
  cmp(Rid,Eid,Op,V1,V2),
  Op == "!=", 
  V1 == V2. 

ptrue(Eid) :- 
  cmp(Rid,Eid,Op,V1,V2),
  Op == "!=", 
  V1 != V2. 

% Debugging to show name and value of a binding, not needed
boundvv(Rid,Vn,Val,Predid,Jpredid) :- 
   boundv(Rid,Vn,Predid,Jpredid),
   alist(Predid,N,Vid), 
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).

mkassign(R,A,C) :- boundvv(R,A,C,Predid,Jpredid).

boundvn(Vn) :- boundv(Rid,Vn,Preid,Jpredid).

% For a ground rule, there cannot be a variable name, which does not have 
% a bound. We try to force each variable to get a bound, but if we dont 
% for some reason, we wont ground either ... 
% And when we have a rule which does grounding via the conjucntion, 
% we dont get this at all. 
%:-
%  ground(Rid),
%  rulevar(Rid,Vid),
%  var(Vid,Vn),
%  not boundvn(Vn).
  
nogvars(Rid) :-
  ground(Rid),
  rulevar(Rid,Vid),
  var(Vid,Vn),
  not boundvn(Vn).
  
noxpansions(Rid) :- 
  ground(Rid), 
  rulecomposite(Rid,Tlist), 
  tlist(Tlist,N,Qualid),
  N != 1,
  qual(Qualid,Predid),
  assert(Aid),
  rulepred(Aid,Jpredid),
  not xpand(Rid,Predid,Jpredid,Tlist).

:- 
  nogvars(Rid),
  noexpansions(Rid).




% Cannot be that we bind to variable with different values
:- 
  boundv(Rid,Vn,Predid1,Jpredid1),
  alist(Jpredid1, N1, Cid1), 
  cnst(Cid1,Val1),
  boundv(Rid,Vn,Predid2,Jpredid2),
  alist(Jpredid2, N2, Cid2), 
  cnst(Cid2,Val2),
  Val1 != Val2,
  Predid1 != Predid2,
  Jpredid1 != Jpredid2.

% The argument cardinality 
maxcard(P,Nmax) :- 
  pred(X,P),
  alist(X,Nmax,Y1),
  alist(X,Nother,Y2),
  Nmax > Nother.

% Next generate all possible conjunctive groundings; that is
% associate the groundings to the typed relation. 
% We are looking for composite(Lid) with tlist(Lid,N,Predid)
% We need rulecomposite in the reification. 
% Is it every element of the ':' separated list?
{xpand(Rid,Predid,Jpredid,Tlist) : 
 rulecomposite(Rid,Tlist) : 
 tlist(Tlist,N,Qualid) : N != 1 : 
 qual(Qualid,Predid) :
 assert(Aid) : 
 rulepred(Aid,Jpredid)} :- rulecomposite(Rid,Tlist). % ground(Rid).

% Cannot be that there is a justification with the same name 
% but it is not covered by xpand. 
:- 
   % There is an assertion for a particular name
   assert(Aid),
   rulepred(Aid,Jpredid), 
   pred(Jpredid,Pn),
   % That assertion cannot be found in expansions 
   not xpand(Rid,Predid,Jpredid,Tlist), 
   rulecomposite(Rid,Tlist), 
   tlist(Tlist,N,Qualid),
   qual(Qualid,Predid),
   pred(Predid,Pn). 

% Get the variables which have been assigned by xpand
boundxpand(Rid,Vn,Predid,Jpredid,Tlist) :- 
   xpand(Rid,Predid,Jpredid,Tlist), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

boundexpandvv(Rid,Pn,Vn,Val,Predid,Tlist,Jpredid) :- 
   boundxpand(Rid,Vn,Predid,Jpredid,Tlist),
   alist(Predid,N,Vid),
   pred(Predid,Pn),
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).


% Cannot be that expanded predicate is of different name 
:- xpand(Rid,Predid,Jpredid,Tlist),
   pred(Predid,Pn1),
   pred(Jpredid,Pn2),
   Pn1 != Pn2.

#hide.
#show mkassign/3.
#show ptrue/1. 
#show pfalse/1. 
#show xpand/4.
#show boundexpandvv/7. 

