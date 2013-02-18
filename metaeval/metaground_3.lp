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

% Also handle constraints 
nonfact(R) :- constraint(R), body(R,A).
poscond(R,A) :- constraint(R), body(R,A), pos(A). 


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
:- nodiffname(Rid). 
nodiffname(Rid) :- 
   need_var_bindings(Rid), 
   sbindit(Rid,Predid,Jpredid),
   pred(Predid,Pn1),
   pred(Jpredid,Pn2),
   Pn1 != Pn2.


% Do not assign two different justifications to one Predid
:- nodiffjusts(Rid). 
nodiffjusts(Rid) :- 
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
% eight(Rid) :- 

:- notunmapped(Rid).  % YYY
notunmapped(Rid) :- 
   % need_var_bindings(Rid), 
   % not need_conj_bindings(Rid), 

   % If there is a conjunction then not all are needed
   % Ths does not sound right, a conjunctive would leave
   % stuff not fully generated
   % not exists_mkassign_conj, 
   mapped(PredidX),  % there cannot be a unmapped without a mapped 
                     % but if there is no mapped then this wont work 
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

mkassign_var(R,A,C) :- boundvv(R,A,C,Predid,Jpredid).

boundvn(Vn) :- boundv(Rid,Vn,Preid,Jpredid).

% There cannot be a variable name, which does not have 
% a bound. 
% This could also kill everything 
%foo :-
%  ground(Rid),
%  rulevar(Rid,Vid),
%  var(Vid,Vn),
%  not boundvn(Vn).
  

% Cannot be that we bind to variable with different values
:- nodiffvarass(Rid).  % YYY
nodiffvarass(Rid) :- 
  need_var_bindings(Rid), 
  mkassign_var(Rid,Vname,Val1),
  mkassign_var(Rid,Vname,Val2),
  Val1 != Val2.

% The argument cardinality 
%maxcard(P,Nmax) :- 
%  pred(X,P),
%  alist(X,Nmax,Y1),
%  alist(X,Nother,Y2),
%  Nmax > Nother.

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

:- dontmissexpand(Rid). % YYY
dontmissexpand(Rid) :- 
    need_conj_bindings(Rid), 
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
:- notextcflct(Rid). % YYY
notextecflct(Rid) :- 
   need_conj_bindings(Rid),
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
:- notleftout(Rid).  % YYY
notleftout(Rid) :- 
   need_conj_bindings(Rid),
   selected(J1), 
   not selected(J2),
   J1 != J2, 
   cnstvar(Rid,Predid,N,Vn,Nt),
   sameval(Rid,J1,J2,N).

% Again, a global which is not good. 
% :- missingjust(J1,J2).

% Cannot be that there is a justification with the same name 
% but it is not covered by xpand. 

:- notcovered(Rid). % YYY
notcovered(Rid) :- 
   need_conj_bindings(Rid),
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
%1 {xxpand(Rid,Predid,Jpredid1,Tlist1,N)} 1 :- 
%  cflctb(Rid,Predid,Jpredid1,Jpredid2,Tlist1,Tlist2,N). 
  
% Now we pick one of these Jpredids
% What if there are more than this one, which are pertinent?
% The two below are for single valued px
%px(Jpredid1) :- xxpand(Rid,Predid,Jpredid1,Tlist1,N), not otherpx(Jpredid1).
%otherpx(Jpredid1) :- px(Jpredid2), assert(Aid), rulepred(Aid,Jpredid1), Jpredid1 != Jpredid2.


%
% Now we need to combine the assignments from the conjunctive grounding 
% with the actual assignments. Here we'd resolve conflicts, if they'd 
% be detected; that is out of many equal options we need to select 
% one based on its provenance (inside the conjunction or outside of it).
%

% For now, we generate mkassigns from the bindings. 
mkassign_conj(Rid,Vn,Val) :- 
    boundexpandvv(Rid,Pn,Vn,Val,Predid1,Tlist,Jpredid),
    cnstvar(Rid,Predid2,N,Vn,Nt).

% Cannot be that we bind to variable with different values
:- nodiffconjass(Rid).  % YYY
nodiffconjass(Rid) :- 
  need_conj_bindings(Rid), 
  mkassign_conj(Rid,Vname,Val1),
  mkassign_conj(Rid,Vname,Val2),
  Val1 != Val2.

% Determine what kind of mkassigns we need 
need_conj_bindings(Rid) :-
    ground(Rid), 
    rulecomposite(Rid,C).

need_var_bindings(Rid) :- 
    ground(Rid), 
    rulepred(Rid,Predid), 
    not qualpred(Predid). 


% Now state that both mkassigns must match, here we do not 
% distinguish between which side is wrong, but since we assume 
% that _conj is always more general the _var should constrain more 
% one :- 
:- notmatching(R). % YYY
notmatching(R) :- 
   need_conj_bindings(R), 
   need_var_bindings(R), 
   mkassign_var(R,A,C1),
   mkassign_conj(R,A,C2),
   C1 != C2. 

% We should still say that both must be present. 
% it seems that _var is more common 
% But this is the case if there are conjuncted variables. 
:- notboth(R). % YYY
notboth(R) :- 
   need_conj_bindings(R), 
   % need_var_bindings(R), 
   mkassign_var(R,A,C1),
   not mkassign_conj(R,A,C1), 
   cnstvar(R,Predid,N,A,Nt).

% Finally copy to mkassign
%mkassign(R,A,C) :- 
%        need_var_bindings(R), 
%  	mkassign_var(R,A,C).

%mkassign(R,A,C) :- 
%        not need_var_bindings(R), 
%  	mkassign_conj(R,A,C).

:- 
   not exists_mkassign_var,
   not exists_mkassign_conj. 

mkassign(R,A,C) :- 
   exists_mkassign_var,
   not exists_mkassign_conj,
   mkassign_var(R,A,C).

mkassign(R,A,C) :- 
   not exists_mkassign_var,
   exists_mkassign_conj,
   mkassign_conj(R,A,C).

mkassign(R,A,C) :- 
   exists_mkassign_var,
   exists_mkassign_conj,
   mkassign_var(R,A,C), 
   mkassign_conj(R,A,C).

:- denyconflicting(R). 
denyconflicting(R) :- 
   exists_mkassign_var,
   exists_mkassign_conj,
   C1 != C2,
   mkassign_var(R,A,C1), 
   mkassign_conj(R,A,C2).




exists_mkassign_var :- mkassign_var(R,A,C).
exists_mkassign_conj :- mkassign_conj(R,A,C).


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
:- notsamename(Rid). % YYY
notsamename(Rid) :- 
   xpand(Rid,Predid,Jpredid,Tlist,N),
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
