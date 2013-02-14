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

% Distinguish predicates which are bound by a conjunction 
qualpred(Predid) :- 
  % rulepred(Rid,Predid), 
  rulecomposite(Rid,Cid), 
  tlist(Cid,N,Qid),
  qual(Qid,Predid).

% This is correct, but in case we do not 
% have any mkassigns, but only bindings in case 
% of the typed stuff, this may kill everything.
% Actually, we may want to say that, we deny this 
% for rules that have been grounded and have 
% variables which are outside of the typed list.  
:- 
   unmapped(Predid), % This is want we want, but now we try to make it less global
   % All of below states that we should not count predicates inside conjunction 
   % to this constraint. 
   rulepred(Rid,Predid), 
   not qualpred(Predid). 

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
% This could also kill everything 
foo :-
  ground(Rid),
  rulevar(Rid,Vid),
  var(Vid,Vn),
  not boundvn(Vn).
  

% Cannot be that we bind to variable with different values
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

qualvar(Rid,Vid) :- 
  rulevar(Rid,Vid), 
  var(Vid,Vn), 
  alist(Predid,N,Vid), 
  qual(Titem,Predid). 

% Get the name of the variable and make sure that 
% it is not in the first item of the tlist, that is,
% it effect binding of variables. 
qualvarn(Rid,Vid,Vn) :- 
  qualvar(Rid,Vid), 
  rulecomposite(Rid,Tlist), 
  qual(Titem,Predid), 
  alist(Predid,N1,Vid), % Trouble here if the item is not on first level 
  tlist(Tlist,N,Titem),
  N != 1,
  var(Vid,Vn). 
  
% Now collect the items for variables of the same name 

nonqualvar(Rid,Vid,Vn) :- 
  rulevar(Rid,Vid),
  var(Vid,Vn), 
  not qualvar(Rid,Vid).

% Next generate all possible conjunctive groundings; that is
% associate the groundings to the typed relation. 
% We are looking for composite(Lid) with tlist(Lid,N,Predid)
% We need rulecomposite in the reification. 
% Is it every element of the ':' separated list?
% If no other constraints exist, these are all in one 
% answer set. 
{xpand(Rid,Predid,Jpredid,Tlist,N) : 
 tlist(Tlist,N,Qualid) : N != 1 :
 qual(Qualid,Predid) :
 assert(Aid) : 
 rulepred(Aid,Jpredid)} :- rulecomposite(Rid,Tlist).

% These two take into account the constraints produced by the 
% various constraints. There could be a way to roll them into 
% one single xpand ...
{xpand2(Rid,Predid,Jpredid,Tlist,N)} :- 
    xpand(Rid,Predid,Jpredid,Tlist,N),
    selected(Jpredid).

:- 
    not xpand2(Rid,Predid,Jpredid,Tlist,N), 
    xpand(Rid,Predid,Jpredid,Tlist,N),
    selected(Jpredid). 

% Generate names for the bindings 
% Get the variables which have been assigned by xxxpand
% Here is the first time we have 
xpandn(Rid,Vn,Predid,Jpredid,Tlist,Nt) :- 
   xpand(Rid,Predid,Jpredid,Tlist,Nt), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

xpandnv(Rid,Pn,Vn,Val,N,Predid,Tlist,Jpredid,Nt) :- 
   xpandn(Rid,Vn,Predid,Jpredid,Tlist,Nt),
   alist(Predid,N,Vid),
   pred(Predid,Pn),
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).

% Now we constraint xpand according to constraints coming 
% from outside of the conjunction. 

% Firstly we produce those expansions which have the same
% value for the same position. This is useful in case 
% we have predicates outside of the scope of the conjunction,
% which nevertheless cannot be assigned a valuation. 
% This is useful even when assigning values later on. 
% Which justifications are compatible 
sameval(Rid,Jpredid1,Jpredid2,N) :- 
  xpand(Rid,Predid1,Jpredid1,Tlist1,N1), 
  xpand(Rid,Predid2,Jpredid2,Tlist2,N2), 
  % Different justificaitons 
  Jpredid1 != Jpredid2,
  % Predicate names must match 
  pred(Predid1,Pn1),
  pred(Predid2,Pn2),
  Pn1 == Pn2,
  % Indices must match
  alist(Jpredid1,N,Cid1),
  alist(Jpredid2,N,Cid2),
  % Constant values must match 
  cnst(Cid1,Val1),
  cnst(Cid2,Val2),
  Val1 == Val2. 

% Look for predicates that are not in types 
constraintpred(Predid1) :-
   rulepred(Rid,Predid1),
   not qualpred(Predid1).

% We only know if there is a variable, but 
% we should associate the variable to a predicate 
% directly, to avoid making an unpredicateble 
% search in case of nested expressions. 
% Here we assume no nesting but variables direct under alist. 
% We also limit this to a rule where there are cinjunction lists. 
constrainedvar(Rid,Vn) :- 
    constraintpred(Predid), 
    rulepred(Rid,Predid), 
    alist(Predid,N,Vid),
    var(Vid,Vn).
    
% Now we need to detect those xpands, which refer to this 
% constrainedvar 
constrainedxpand(Rid,Predid,N,Tlist,Jpredid,Nt) :- 
    constrainedvar(Rid,Vn), 
    xpandnv(Rid,Pn,Vn,Val,N,Predid,Tlist,Jpredid,Nt). 

% List the places where constrainedvar is being referred to inside the tlist
cnstvar(Rid,Predid,N,Vn,Nt) :-
    constrainedvar(Rid,Vn),
    xpandnv(Rid,Pn,Vn,Val,N,Predid,Tlist,Jpredid,Nt). 

% Project the same values of xpands 
xpandvar(Rid,Vn,Val,Jpredid) :- 
    xpandnv(Rid,Pn,Vn,Val,N,Predid,Tlist,Jpredid,Tn).

% Two expansions are in conflcit wrt. an external constraint
extcflct(Rid,Pn1,Jpredid1,Jpredid2) :- 
    xpandnv(Rid,Pn1,Vn,Val1,N1,Predid1,Tlist1,Jpredid1,Tn1),
    xpandnv(Rid,Pn2,Vn,Val2,N2,Predid2,Tlist2,Jpredid2,Tn2), 
    Val1 != Val2, 
    cnstvar(Rid,Predid,N,Vn,Nt). 

% Pick justifications which have same values 
% We want to pick many but we only get one. 
expjust(Jpredid) :-
%{expjust(Jpredid)} :-
    not otherexpjust(Jpredid), 
    xpand(Rid,Predid,Jpredid,Tlistid,Nt). 

otherexpjust(Jpredid1) :- 
    expjust(Jpredid2), 
    Jpredid1 != Jpredid2, 
    xpand(Rid,Predid,Jpredid1,Tlistid,Nt), 
    % not sameval(Rid,Jpredid1,Jpredid2,N),
    extcflct(Rid,Pn,Jpredid1,Jpredi2). 
    % alist(Jpredid1,N,Cid). % To get the N 
    
% Just generate all subsets of Jpreds 
{selected(Jpredid)} :-     xpand(Rid,Predid,Jpredid,Tlistid,Nt). 

% Weed out stuff, there cannot be externally conflicting stuff.
% Note that this cannot be global either, when combining with the 
% variable assignment. 
:- 
   selected(J1),
   selected(J2), 
   J1 != J2, 
   extcflct(Rid,Vn,J1,J2). 

% Does not seem to work, why 
%selected(J2) :-
%selected2(J2) :-
%   selected(J1),
%   sameval(Rid,J1,J2,N).

% Make sure that no relevant Justified predid 
% is left out. 


% Make sure that no justification with a compatible 
% valuation is left out. 
% A global constraint, caveat emptor... 
% missingjust(J1,J2) :- 
:- 
   selected(J1), 
   not selected(J2),
   J1 != J2, 
   cnstvar(Rid,Predid,N,Vn,Nt),
   sameval(Rid,J1,J2,N).

% Again, a global which is not good. 
% :- missingjust(J1,J2).

% Only allow those xpands which agree on the constraints 
% Cannot be that two expands differ on the value of a 
% constrained variable. 
badx(Vn,Val1,N1,Predid1,Tlist1,Jpredid1,Nt1) :- 
   xpandnv(Rid,Pn1,Vn,Val1,N1,Predid1,Tlist1,Jpredid1,Nt1),
   xpandnv(Rid,Pn2,Vn,Val2,N2,Predid2,Tlist2,Jpredid2,Nt2),
   constrainedvar(Rid,Vn), 
   Val1 != Val2. 

%  xpandnv(Rid,Pn1,Vn1,Val,Predid1,Tlist1,Jpredid1,Nt1), 
%  xpandnv(Rid,Pn2,Vn2,Val,Predid2,Tlist2,Jpredid2,Nt2), 

% Now check the compatibility with any variable bound outside
% of the typed list. 
% extdisagree(Vn,Val1,Jpredid1,Jpredid2,Val2,Nt1,Nt2) :- 
extdisagree(Vn,Val1,Jpredid1,Jpredid2,Val2) :- 
   nonqualvar(Rid,Vid,Vn),
   %boundexxxpandvv(Rid,Pn,Vn,Val1,Predid1,Tlist1,Jpredid1,Nt1), 
   boundexxxpandvv(Rid,Pn,Vn,Val1,Predid1,Tlist1,Jpredid1), 
   %boundexxxpandvv(Rid,Pn,Vn,Val2,Predid2,Tlist2,Jpredid2,Nt2), 
   boundexxxpandvv(Rid,Pn,Vn,Val2,Predid2,Tlist2,Jpredid2), 
   Val1 != Val2. 

extagree(Vn,Val1,Jpredid1,Jpredid2,Val2) :- 
   nonqualvar(Rid,Vid,Vn),
   boundexxxpandvv(Rid,Pn,Vn,Val1,Predid1,Tlist1,Jpredid1), 
   boundexxxpandvv(Rid,Pn,Vn,Val2,Predid2,Tlist2,Jpredid2), 
   Jpredid1 != Jpredid2,
   Val1 == Val2. 

% Cannot be that there is a justification with the same name 
% but it is not covered by xpand. 
:- 
   % There is an assertion for a particular name
   assert(Aid),
   rulepred(Aid,Jpredid), 
   pred(Jpredid,Pn),
   % That assertion cannot be found in expansions 
   not xpand(Rid,Predid,Jpredid,Tlist,N), 
   rulecomposite(Rid,Tlist), 
   tlist(Tlist,N,Qualid),
   qual(Qualid,Predid),
   pred(Predid,Pn). 

% Do not assign two different justifications to one Predid
% First we detect those which do
% Denying this would kill all solutions. 
cflctb(Rid,Predid,Jpredid1,Jpredid2,Tlist1,Tlist2,N) :- 
    xpand(Rid,Predid,Jpredid1,Tlist1,N),
    xpand(Rid,Predid,Jpredid2,Tlist2,N),
    Jpredid1 != Jpredid2. 

% Then we generate a single one for all of them 
% Jpredid1 is unique,we generate as many as there are Jpredids
1 {xxpand(Rid,Predid,Jpredid1,Tlist1,N)} 1 :- 
  cflctb(Rid,Predid,Jpredid1,Jpredid2,Tlist1,Tlist2,N). 
  
% Now we pick one of these Jpredids
% What if there are more than this one, which are pertinent?
% The two below are for single valued px
%px(Jpredid1) :- xxpand(Rid,Predid,Jpredid1,Tlist1,N), not otherpx(Jpredid1).
%otherpx(Jpredid1) :- px(Jpredid2), assert(Aid), rulepred(Aid,Jpredid1), Jpredid1 != Jpredid2.

% And then we pick one of them only 
% 1 {xxxpand(Rid,Predid,Jpredid1,Tlist1) } 1 :- xxpand(Rid,Predid,Jpredid1,Tlist1), px(Jpredid1). 
1 {xxxpand(Rid,Predid,Jpredid1,Tlist1) } 1 :- xxpand(Rid,Predid,Jpredid1,Tlist1,N). 

% Can't be so that there is a xxxpand which disagrees on value of 
% nonqualvar. 
disagree_old(Vn,Val1,Jpredid1,Jpredid2,Val2) :- 
   nonqualvar(Rid,Vid,Vn),
   boundexxxpandvv(Rid,Pn,Vn,Val1,Predid1,Tlist1,Jpredid1), 
   boundexxxpandvv(Rid,Pn,Vn,Val2,Predid2,Tlist2,Jpredid2), 
   Val1 != Val2. 

agree_old(Vn,Val1,Jpredid1,Jpredid2,Val2) :- 
   nonqualvar(Rid,Vid,Vn),
   boundexxxpandvv(Rid,Pn,Vn,Val1,Predid1,Tlist1,Jpredid1), 
   boundexxxpandvv(Rid,Pn,Vn,Val2,Predid2,Tlist2,Jpredid2), 
   Jpredid1 != Jpredid2,
   Val1 == Val2. 

% Generate separate answer sets for each justification ID
% {agree2(Jpredid1)} :- agree(Vn,Val1,Jpredid1,Jpredid2,Val2).
% {agree2(Jpredid2)} :- agree(Vn,Val1,Jpredid1,Jpredid2,Val2).
% Ideally this should be used for xxxpand. 


% Limit these so that in one answer set there can not 
% be two different values for two different justifications. 
% It seems that this produces single agree2 for single unique 
% value. 
% We could pick this and then expand to contain the 
% similar values...
% And we may still have too few of these, that is 
% we may have zero,one agree2()'s
%klank :-
%  agree2(Jpredid1), 
%  agree2(Jpredid2),
%  Jpredid1 != Jpredid3, 
%  agree(Vn,Val1,Jpredid1,Jpredid2,Val2), 
%  agree(Vn,Val3,Jpredid3,Jpredid4,Val4),
%  Val1 != Val3.

% We should still make sure that agree2 is not missing anything
% Cant be a agree1 with no agree2. 
%:- 
%  not agree2(Jpredid1), 
%  agree(Vn,Vl1,Jpredid1,Jpredid2,Vl2).

% prj1(Vn,Vl,J) :- agree(Vn,Vl,J,J2,V2).

% Now try to pick (from prj1) those which have the same Vn Vl
%{prj2(Vn,Vl,J1)} :- 
%  prj1(Vn,Vl,J1),
%  prj1(Vn,Vl,J2),
%  J1 != J2. 
  
% There is a prj1 which is not in any of the 
% prj2's.
%orphanprj(Vn,Vl,J1) :- 
%  prj1(Vn,Vl,J1), 
%  not prj2(Vn,Vl,J1).


% Get the variables which have been assigned by xxxpand
% Here is the first time we have 
boundxxxpand(Rid,Vn,Predid,Jpredid,Tlist) :- 
   xxxpand(Rid,Predid,Jpredid,Tlist), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

boundexxxpandvv(Rid,Pn,Vn,Val,Predid,Tlist,Jpredid) :- 
   boundxxxpand(Rid,Vn,Predid,Jpredid,Tlist),
   alist(Predid,N,Vid),
   pred(Predid,Pn),
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).


%
% Now we need to combine the assignments from the conjunctive grounding 
% with the actual assignments. Here we'd resolve conflicts, if they'd 
% be detected; that is out of many equal options we need to select 
% one based on its provenance (inside the conjunction or outside of it).
%

% For now, we generate mkassigns from the bindings. 
mkassign(Rid,Vn,Val) :- 
    boundexpandvv(Rid,Pn,Vn,Val,Predid1,Tlist,Jpredid),
    cnstvar(Rid,Predid2,N,Vn,Nt).

% Get the variables which have been assigned by xpand
boundxpand(Rid,Vn,Predid,Jpredid,Tlist) :- 
   % xpand(Rid,Predid,Jpredid,Tlist,Nn), 
   xpand2(Rid,Predid,Jpredid,Tlist,Nn),  % The limited version 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

% This is the expansion interpreted by aspreify 
boundexpandvv(Rid,Pn,Vn,Val,Predid,Tlist,Jpredid) :- 
   boundxpand(Rid,Vn,Predid,Jpredid,Tlist),
   alist(Predid,N,Vid),
   pred(Predid,Pn),
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).

% Cannot be that expanded predicate is of different name 
:- xpand(Rid,Predid,Jpredid,Tlist,N),
   pred(Predid,Pn1),
   pred(Jpredid,Pn2),
   Pn1 != Pn2.

% #hide.
#show mkassign/3.
#show boundexpandvv/7.

% debug
#show mapped/1.
#show unmapped/1. 
#show qualpred/1.
