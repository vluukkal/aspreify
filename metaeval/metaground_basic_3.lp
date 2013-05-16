%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% This is the basic metagrounder, which binds variables to ground atoms. 
% This does not take into account conjunctions and projections. 
% Main interface is the internal sbind/3, which will be translated to 
% mkassign_var/3.  
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


% We "draw lines" between the actual instances

% Generate all possible bindings
% As assert may now be generated, we move it out of the choice
% {sbindit(Rid,Predid,Jpredid) : rulepred(Rid,Predid) : assert(Aid) : rulepred(Aid,Jpredid)} :- ground(Rid). 
% {sbindit(Rid,Predid,Jpredid) : rulepred(Rid,Predid) : rulepred(Aid,Jpredid)} :- ground(Rid), assert(Aid). 
{sbindit(Rid,Predid,Jpredid) : rulepred(Rid,Predid) : rulepred(Aid,Jpredid)} :- assert(Aid). 

% We cant bind a head
%:- 
%   sbindit(Rid,Predid,Jpredid),
%   head(Rid,Predid). 

% A projection needed for later to force creation 
% of sbindit's. 
hasbind(Rid) :- sbindit(Rid,Predid,Jpredid). 
predhasbind(Rid,Predid) :- sbindit(Rid,Predid,Jpredid). 

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

:- nobindinhead(Rid).
nobindinhead(Rid) :- 
   sbindit(Rid,Predid,Jpredid1),
   head(Rid,Predid).

% Make sure that each predicate in body of a ground rule is 
% mapped. 
mapped(Predid) :- sbindit(Rid,Predid,Jpredid). 
unmapped(Predid1) :- 
  not mapped(Predid1), 
  % ground(Rid), % YYY 
  not head(Rid,Predid1),
  rulepred(Rid,Predid1). 

% For unmapped predicates, check their compatibility with the current mapping 
% If we get this, then it means that:
%
% There is an unampped predicate pred(Predid1,Pn) which refers 
% to a variable Vn, and 
% there is a binding to value Val via Jpredid2.
%
% This is a potentially conflicting case, it does not 
% emerge every time as it may that predicates are not 
% unmapped.  
%
potcflct(Predid1,Pn1,Vn,Val,Jpredid2) :- 
  unmapped(Predid1),                    % An unmapped predicate
  pred(Predid1,Pn1),                    % named Pn1
  % predvarexp(Predid1,Vid,Vn,N),         % referring to a variable  % Does not seem to work 
  predvar(Predid1,Vid), 		% referring to a variable 
  var(Vid,Vn),                          % named Vn
  vsbindit(Pn2,Predid2,Jpredid2),	% A current mapping 
  boundvv(Rid,Vn,Val,Predid2,Jpredid2), % for a predicate named Pn2, for the same variable
  Pn1 != Pn2.

predval(Aid,Pn,N,Val) :- 
  assert(Aid), 
  head(Aid,Predid), 
  pred(Predid,Pn),
  alist(Predid,N,Cid), 
  cnst(Cid,Val). 

% If there is a potential conflict flag it
% This conflict arises from an existing domain 
% predicate with different values. 
% inspection. 
% :- realcflct(Pn1,Vn,Predid1,N, Val1, Val2). 
% realcflct(Pn1,Vn,Predid1,N, Val1, Val2) :- 
%sbindcflct(Pn1,Vn,Predid1,N, Val1, Val2) :- 
%  potcflct(Predid1,Pn1,Vn,Val1,Jpredid1), 
%  predvarext(Predid1,Vid,Vn,N),
%  % Now find a domain predicate with a proper name 
%  predval(Aid,Pn1,N,Val2), 
%  Val1 != Val2.

% Same as above but now we want to to take one step further 
% and try to evaluate a potential rule with head of name Pn1 
% nonsbindcflct(Pn1,Vn,Predid1,N, Val1, Val2) :- 
%% nonsbindcflct(Pn1,Vn,Predid1,N) :- 
%  potcflct(Predid1,Pn1,Vn,Val1,Jpredid1), 
%  predvarext(Predid1,Vid,Vn,N),
%  % Is there a rule with head that is named 
%  % like the conflicting one and has only one item 
%  % in the body. 
%  abody(Rid,Predid), 
%  not manybodies(Rid), % only one item in body 
%  head(Rid,Headid), 
%  pred(Headid,Pn1),
%  % Can we not bind this single predicate to an assertion 
%  % in a consistent manner? 
%  assert(Aid), 
%  head(Aid,Jpredid2), 
%  pred(Jpredid2,Pn1), % same name 
%  alist(Jpredid,N,Cid), % same position 
%  cnst(Cid,Val2),
%  Val1 != Val2. 


% We can look at truerule() valuations 
%realcflct(Pn1,Vn,Predid1,N, Val1, Val2) :- 
%  potcflct(Predid1,Pn1,Vn,Val1,Jpredid1), 
%  predvarext(Predid1,Vid,Vn,N),
%  % Now find a domain predicate with a proper name 
%  atruerule(Rid). % XXX
  
% This is correct, but in case we do not 
% have any mkassigns, but only bindings in case 
% of the typed stuff, this may kill everything.
% Actually, we may want to say that, we deny this 
% for rules that have been grounded and have 
% variables which are outside of the typed list.  

% :- notunmapped(Rid).  % YYY
%notunmapped(Rid) :- 
   % need_var_bindings(Rid), 
   % need_conj_bindings(Rid), 

   % If there is a conjunction then not all are needed
   % This does not sound right, a conjunctive would leave
   % stuff not fully generated
   % not exists_mkassign_conj, 
%   mapped(PredidX),  % there cannot be a unmapped without a mapped 
                     % but if there is no mapped then this wont work 
%   unmapped(Predid), % This is want we want, but now we try to make it less global
   % All of below states that we should not count predicates inside conjunction 
   % to this constraint. 
%   rulepred(Rid,Predid), 
%   not qualpred(Predid). 

% There is a potential variable binding in the rule Rid
% This is just potential, this may be problematic when 
% later on we want to constrain this...
potbinding(Rid) :- potbindingpred(Rid,Predid,Pn). 
potbindingpred(Rid,Predid,Pn) :- 
    % First there is a relevant rule with a predicate
    need_var_bindings(Rid), 
    rulepred(Rid,Predid), % Thes two are a bit redundant, could be in need_*
    not qualpred(Predid),
    pred(Predid,Pn), 
    % Then there is a relevant ground predicate with th same name 
    assert(Aid), 
    rulepred(Aid,Jpredid), 
    pred(Jpredid,Pn). 

:- forcesbind(Rid).
forcesbind(Rid) :- 
   potbinding(Rid),
   not hasbind(Rid). 

% Now we want to say that it cant be that there is a potential 
% binding and there is no sbindit for it. 
% This may be useless as it is present in 
% otherwise OK answer sets. XXX
% 
% :- missedpotential(Rid). % YYY 
missedpotential(Rid) :- 
    not need_conj_bindings(Rid), 
    potbinding(Rid), 
    not sbindit(Rid,Predid,Jpredid), 
    rulepred(Rid,Predid), 
    assert(Aid),
    rulepred(Aid,Jpredid). 

% Can't be that there is missedpotential and unmapped predicates
% This forces us to generate mapped()'s (hence sbind's). 

% :- unsafeunmapped(Rid,Predid). % YYY 
unsafeunmapped(Rid,Predid) :- 
    missedpotential(Rid), 
    rulepred(Rid,Predid), 
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

mkassign_var(R,A,C) :- boundvv(R,A,C,Predid,Jpredid).

boundvn(Rid,Vn) :- boundv(Rid,Vn,Preid,Jpredid).

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

% EOF metaground_basic.lp 