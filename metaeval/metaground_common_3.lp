%
% Some common parts and the final aggregation of mkassigns and hides. 
% This is expected to be tha last file. 
%   
% Will produce the mkassign/3 used by the dereifier. 
%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% Assume that foo.lp contains the program.
% 1. Reify the program: ./aspreify foo.lp 
% 2. Combine this with the reified program: cat metaground.lp foo.lp.reified > toeval.lp
% 3. Calculate the answer sets: gringo toeval.lp | clasp --project -n 0 
% 4. For full grounding pipeline do:
% 4.1 gringo toval.lp | clasp --project -n 0 | python smodelsres.py
% 4.2 ./aspreify -b foo.lp.reified smres*.lp
% 4.3 for f in *.ground; do cat $f >> foo.lp.reified.res; done 

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

% This should eventually be in the reified result
% now we may miss deeper relations. 
% We could have the name Vn here as well. 
predvar(Predid,Vid) :- 
    alist(Predid,N,Vid),
    var(Vid,Vn). 

predvarext(Predid,Vid,Vn,N) :- 
    alist(Predid,N,Vid),
    var(Vid,Vn). 

% Distinguish predicates which are bound by a conjunction 
qualpred(Predid) :- 
  % rulepred(Rid,Predid), 
  rulecomposite(Rid,Cid), 
  tlist(Cid,N,Qid),
  qual(Qid,Predid).

qualvar(Rid,Vid) :- 
  rulevar(Rid,Vid), 
  var(Vid,Vn), 
  alist(Predid,N,Vid), 
  qual(Titem,Predid). 

% A rulevar that is not inside a conjunction 
nonqualvar(Rid,Vid,Vn) :- 
  rulevar(Rid,Vid),
  var(Vid,Vn), 
  not qualvar(Rid,Vid).

recursive(Rid,Pn) :- 
    head(Rid,Predid), 
    pred(Predid,Pn), 
    body(Rid,Bid), 
    pred(Bid,Pn). 


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
:- notmatching(R). % YYY
notmatching(R) :- 
   need_conj_bindings(R), 
   need_var_bindings(R), 
   mkassign_var(R,A,C1),
   mkassign_conj(R,A,C2),
   C1 != C2. 

% We should still say that both must be present. 
:- notboth(R). % YYY
notboth(R) :- 
   need_conj_bindings(R), 
   % need_var_bindings(R), 
   mkassign_var(R,A,C1),
   not mkassign_conj(R,A,C1), 
   cnstvar(R,Predid,N,A,Nt).

:- 
   not exists_mkassign_var,
   not exists_mkassign_conj. 

% Finally copy to mkassign
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

:- denyconflicting(R,A). 
denyconflicting(R,A) :- 
   exists_mkassign_var,
   exists_mkassign_conj,
   C1 != C2,
   mkassign_var(R,A,C1), 
   mkassign_conj(R,A,C2).

exists_mkassign_var :- mkassign_var(R,A,C).
exists_mkassign_conj :- mkassign_conj(R,A,C).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% #hide.

#show mkassign/3.
#show boundexpandvv/7.

#show truerule/1. 
#show falserule/1. 

#show ptrue/1. 
#show pfalse/1. 

#show indetrule/1. 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Debug

% #show truerule_nofalse/1. 

%#show trueprule/1. 
%#show singlebody/1. 

%#show truepredvarv/5. 
%#show truepredvar/3. 
%#show falsepredvar/3. 
%#show missingprojectvar/4. 
#show project/8. 

%#show ground/1. 
%#show sbindit/3. 


%#show truepred/1. 
%#show falsepred/1. 

%#show truepred_cmp/3. 
%#show falsepred_cmp/3. 


%#show mapped/1.
%#show unmapped/1. 
%#show qualpred/1.
%#show ground/1. 
%#show nonfact/1.
%#show fact/1.
%#show other/1. 

% EOF metaground_common.lp 

