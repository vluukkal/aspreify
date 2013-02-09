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

% Make sure that each predicate in body of a ground rule is 
% mapped. 
mapped(Predid) :- sbindit(Rid,Predid,Jpredid). 
unmapped(Predid1) :- 
  not mapped(Predid1), 
  ground(Rid), 
  not head(Rid,Predid1),
  rulepred(Rid,Predid1). 

:- 
  unmapped(Predid). 


% Get the variables which have been assigned by sbindit 
boundv(Rid,Vn,Predid,Jpredid) :- 
   sbindit(Rid,Predid,Jpredid), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

% Debugging to show name and value of a binding, not needed
boundvv(Rid,Vn,Val,Predid,Jpredid) :- 
   boundv(Rid,Vn,Predid,Jpredid),
   alist(Predid,N,Vid), 
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).

mkassign(R,A,C) :- boundvv(R,A,C,Predid,Jpredid).

boundvn(Vn) :- boundv(Rid,Vn,Preid,Jpredid).

% There cannot be a variable name, which does not have 
% a bound. 
:-
  ground(Rid),
  rulevar(Rid,Vid),
  var(Vid,Vn),
  not boundvn(Vn).
  

% Cannot be that we bind to variable with different values
foo :- 
  boundv(Rid,Vn,Predid1,Jpredid1),
  alist(Jpredid1, N1, Cid1), 
  cnst(Cid1,Val1),
  boundv(Rid,Vn,Predid2,Jpredid2),
  alist(Jpredid2, N2, Cid2), 
  cnst(Cid2,Val2),
  Val1 != Val2,
  Predid1 != Predid2,
  Jpredid1 != Jpredid2.

:- 
  mkassign(Rid,Vname,Val1),
  mkassign(Rid,Vname,Val2),
  Val1 != Val2.

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
{xpand(Rid,Predid,Jpredid) : 
 rulecomposite(Rid,Tlist) : 
 tlist(Tlist,1,Qualid) : 
 qual(Qualid,Predid) :
 assert(Aid) : 
 rulepred(Aid,Jpredid)} :- ground(Rid).


%foo :-
%   rulecomposite(Rid,Tlist),
%   tlist(Tlist,N,Qualid), 
%   qual(Qualid,Predid),
%   pred(Predid,Pname), 
   

#hide.
#show mkassign/3.
#show boundexpandvv/7.
