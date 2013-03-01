%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% This is the part that handles the variables inside conjunctive
% structures. 
% The main result is mkassign_conj/3, which is projected to mkassign/3
% later on. The source for this is xpand/5. 
% There is also boundexpandvv/7, which is interpreted by the dereifier.
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
 % assert(Aid) : 
 rulepred(Aid,Jpredid)} :- rulecomposite(Rid,Tlist), assert(Aid).

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
% directly, to avoid making an unpredicatable 
% search in case of nested expressions. 
% Here we assume no nesting but variables direct under alist. 
% We also limit this to a rule where there are conjunction lists. 
constrainedvar(Rid,Vn) :- 
    constraintpred(Predid), 
    rulepred(Rid,Predid), 
    alist(Predid,N,Vid),
    var(Vid,Vn).
    
% Now we need to detect those xpands, which refer to this 
% constrainedvar 
% XXX Perhaps use this with boundv as well 
constrainedxpand(Rid,Predid,N,Tlist,Jpredid,Nt) :- 
    constrainedvar(Rid,Vn), 
    xpandnv(Rid,Pn,Vn,Val,N,Predid,Tlist,Jpredid,Nt). 

% Is there a variable that has not been constrained
:- dangling(Rid,Vn).
dangling(Rid,Vn) :- 
    ground(Rid),
    constrainedvar(Rid,Vn), 
    not boundvn(Rid,Vn),
    not boundconjvn(Rid,Vn).

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

boundconjvn(Rid,Vn) :- 
    boundexpandvv(Rid,Pn,Vn,Val,Predid1,Tlist,Jpredid).

% Cannot be that we bind to variable with different values
:- nodiffconjass(Rid).  % YYY
nodiffconjass(Rid) :- 
  need_conj_bindings(Rid), 
  mkassign_conj(Rid,Vname,Val1),
  mkassign_conj(Rid,Vname,Val2),
  Val1 != Val2.

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

% EOF metaground_conj.lp 