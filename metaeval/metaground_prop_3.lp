%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% This part of metragounder deals with thte truthvalues of individual 
% predicates and relevant rules. This is the basic notion of answer sets
% if all predicates are true, then so is the rule. 
% The main output are truepred/1, falsepred/1, truerule/1, falserule/1.
% 
% This also handles the truth values of non-predicate expressions, like
% comparisons or calculations. 
%
% Assume that foo.lp contains the program.
% 1. Reify the program: ./aspreify foo.lp 
% 2. Combine this with the reified program: cat metaground.lp foo.lp.reified > toeval.lp
% 3. Calculate the answer sets: gringo toeval.lp | clasp --project -n 0 
% 4. For full grounding pipeline do:
% 4.1 gringo toval.lp | clasp --project -n 0 | python smodelsres.py
% 4.2 ./aspreify -b foo.lp.reified smres*.lp
% 4.3 for f in *.ground; do cat $f >> foo.lp.reified.res; done 
%   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Now do some high level answer set like management. 

% Note that the dereifier reads in ptrue(Predid) and does not 
% render them. We could use falsepred as well. 

% ptrue(Predid) :- sbindit(Rid,Predid,Jpredid). 

% How about negation?
% But this will only come from ground rules and is hence not global. 
truepred3(Predid) :- sbindit(Rid,Predid,Jpredid), not neg(Predid). 

truepred(Predid) :- 
     not neg(Predid), 
     pred(Predid, Pn), 
     assert(Aid), 
     head(Aid,Hid), 
     pred(Hid,Pn). 

truepred2(Predid,Hid) :- 
     not neg(Predid), 
     pred(Predid, Pn), 
     assert(Aid), 
     head(Aid,Hid), 
     Predid != Hid, 
     pred(Hid,Pn). 

trueprules(Rid,Hid) :- 
    abody(Rid,Predid), 
    not manybodies(Rid), 
    truepred2(Predid,Hid). 


% A non-bindit version of truepred, which only applies 
% to single predicates in a body, 

%truepred(Predid) :- 
%    % Make sure that this is the only predicate 
%    abody(Rid,Predid), 
%    not manybodies(Rid), 



% If all bodyparts are true, then the whole rule is 
% true. A special case is if we only have one body. 
% ...
abody(Rid,Predid) :- 
    % ground(Rid), 
    not head(Rid,Predid), 
    rulepred(Rid,Predid).

manybodies(Rid) :- 
    % ground(Rid), 
    not head(Rid,Predid1), 
    not head(Rid,Predid2), 
    rulepred(Rid,Predid1), 
    rulepred(Rid,Predid2),
    Predid1 != Predid2.

% This means that we have essentially a projection 
% which can be considered a ground predicate. 
% We use this later to generate a mock-assertion 
% so that this can be treated as a ground predicate 
% by the rules.
trueprule(Rid) :- 
    abody(Rid,Predid), 
    not manybodies(Rid), 
    truepred(Predid). 

% How about trueprule for many bodies
trueprule(Rid) :- 
    abody(Rid,Predid1), 
    abody(Rid,Predid2), 
    Predid1 != Predid2, 
    truepred(Predid1),
    truepred(Predid2). 
    


singlebody(Rid) :- 
    abody(Rid,Predid), 
    not manybodies(Rid). 

% truerule would be for rendering only as a sign 
% to the dereifier.
% truerule(Rid) :- trueprule(Rid). % ZZZ

% If one of the bodies is not true, the whole rule is indeterminate.
% This occurs especially in case of non-ground predicates. 
indetrule(Rid) :- 
    not head(Rid,Predid1), 
    not head(Rid,Predid2), 
    rulepred(Rid,Predid1), 
    rulepred(Rid,Predid2),
    Predid1 != Predid2,
    truepred(Predid1),
    not truepred(Predid2). 

:- falserule(Rid). % XXX global one 
falserule(Rid) :- 
    not head(Rid,Predid1), 
    rulepred(Rid,Predid1), 
    falsepred(Predid1). 

falserule(Rid) :- 
    not head(Rid,Predid1), 
    bexpr(Rid,Predid1), 
    falsepred(Predid1). 


% Truerule is one that has no falsepredicates. 
truerule(Rid) :- truerule_nofalse(Rid),
	      	 not indetrule(Rid), 
		 not falserule(Rid).

truerule_nofalse(Rid) :- 
    ground(Rid),
    not falserule(Rid). 

% Try to deduce truth of a predicate by checking whether a nonbound 
% predicate has conforming domain predicates. 
truepredvarv(Rid,Predid,Vn,Jpredid,N) :- 
    ground(Rid), 
    % For a nonbound predicate named Pn 
    not predhasbind(Rid,Predid), 
    not head(Rid,Predid),
    pred(Predid,Pn),
    % That has a variable named Vn 
    alist(Predid,N,Varid),
    var(Varid,Vn),
    % Find a bound variable with the same name Vn to get 
    % a value that we need to compare. 
    % This will be bound to another predicate
    boundvv(Rid,Vn,Val,Predid2,Jpredid2),
    % Now check if we have a projection for this variable
    % from some other rule with the same Pn and Vn 
    project(Rid2,Pn,Vn2,Predid3,N,Jpredid,N2,Cval),
    not neg(Predid), 
    Val == Cval.


truepredvar(Rid,Predid,Vn) :- truepredvarv(Rid,Predid,Vn,Jpredid,N). 

% For this particular Predid, check whether there are 
% multiple bounds for different variables 
missingprojectvar(Rid,Predid,Vn,N) :- 
    ground(Rid), 
    % For a nonbound predicate named Pn with a variable 
    not predhasbind(Rid,Predid), 
    not head(Rid,Predid),
    body(Rid,Predid), 
    pred(Predid,Pn),
    alist(Predid,N,Vid), 
    var(Vid,Vn), 
    not truepredvar(Rid,Predid,Vn). 

missingp(Rid,Predid) :- missingprojectvar(Rid,Predid,Vn,N). 
% :- missingp(Rid,Predid). % XXX Too global

falsepredvar(Rid,Predid,Vn) :- 
    ground(Rid), 
    not predhasbind(Rid,Predid), 
    pred(Predid,Pn),
    alist(Predid,N,Varid),
    var(Varid,Vn), 
    not truepredvar(Rid,Predid,Vn). 

sametruepred(Predid,Vn,Jpredid) :- 
    truepredvarv(Rid,Predid,Vn,Jpredid,N1), 
    truepredvarv(Rid,Predid,Vn,Jpredid,N2).  

difftruepred(Predid,Vn,Jpredid1,Jpredid2) :- 
    truepredvarv(Rid,Predid,Vn,Jpredid1,N1), 
    truepredvarv(Rid,Predid,Vn,Jpredid2,N2),
    not truepredvarv(Rid,Predid,Vn,Jpredid1,N2),
    Jpredid1 != Jpredid2.

difftruepredp(Predid,Vn) :- difftruepred(Predid,Vn,Jpredid1,Jpredid2).

% Truepred is such that there is no predvar 
% for which there would not be a truepredvar 
% on a variable name for the 
truepred(Predid) :- 
    ground(Rid), 
    predvarext(Predid,Vid,Vn,N), 
    not neg(Predid), 
    not missingp(Rid,Predid).

%truepred(Predid) :- 
%    % There is a variable associated with this 
%    % pred and it has been associated 
%    predvarext(Predid,Vid,Vn,N), 
%    truepredvar(Rid,Predid,Vn), 
%    not difftruepred(Predid,Vn),
%    not falsepredvar(Rid,Predid,Vn). 

cmp(Rid,Eid,Op,Val1,Val2) :- 
  mkassign(Rid,Vn1,Val1), 
  mkassign(Rid,Vn2,Val2), 
  bexpr(Rid,Eid), 
  bop(Eid,Op),
  larg(Eid,Larg), 
  var(Larg,Vn1), 
  rarg(Eid,Rarg), 
  var(Rarg,Vn2). 

falsepred(Eid) :- falsepred_cmp(Eid,V1,V2). 
falsepred_cmp(Eid,V1,V2) :- 
  cmp(Rid,Eid,Op,V1,V2),
  Op == "!=", 
  V1 == V2. 

truepred(Eid) :- truepred_cmp(Eid,V1,V2).

truepred_cmp(Eid,V1,V2) :- 
  cmp(Rid,Eid,Op,V1,V2),
  Op == "!=", 
  V1 != V2. 

trueprule(Rid) :- 
    abody(Rid,Predid), 
    not manybodies(Rid), 
    truepred(Predid). 

ptrue(P) :- truepred(P). 
pfalse(P) :- falsepred(P). 


%EOF metaground_prop.lp 