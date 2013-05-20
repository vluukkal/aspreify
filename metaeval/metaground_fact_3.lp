%
% Metagrounder  for answer set programs as described in
% Janhunen, Luukkala. "Meta Programming with Answer Sets for Smart Spaces"
%
% This, unfinished, part of metagrounder aims specifically to handle
% generation of new facts, based on projecting ground predicates. 
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

% Make a Lua counter 
#begin_lua
local idctr = 0

function nxtctr(inc) 
  idctr = idctr + inc
  return idctr
end 

function nxtctr2(inc) 
  res = idctr 
  idctr = idctr + inc
  return res 
end 


function setctr(ctr)
  idctr = ctr
  return idctr
end 

function getctr()
  return idctr
end

#end_lua.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Now we try to ground all immediately groundable 
% or projected rules globally, not caring about the ground() rule.
% This is a preprocessing step. 
%
% We start by generating all possible mappings between the 
% (for now) single-predicate groundable rules.
% To be more precise, the predicate ID of the head predicate
% is mapped to a justifying predicate ID. 
% We want to create all of them like we do for the 
% conjunctions. 
% 
% Rid     - ruleid
% Pn      - name of the predicate
% Vn      - name of the variable in head
% Predid  - Predicateid of the head predicate
% *N1      - Position of Vn in Pn
% Jpredid - the ground predicate ID
% *N2      - position of the value in ground 
% *Cval    - value of the variable at Jpredid
%
% project(Rid,Pn,Vn,Predid,N1,Jpredid,N2) :- 
%project(Rid,Pn,Vn,Predid,N1,Jpredid,N2,Cval) :- 
%    singlebody(Rid), 
%    % Variable in the head 
%    head(Rid,Predid), 
%    pred(Predid,Pn), 
%    alist(Predid,N1,Vid1), 
%    var(Vid1,Vn), 
%    % The variable Vn in the predicate of body
%    body(Rid,Bid), 
%    pred(Bid,Pntmp), 
%    alist(Bid,N2,Vidtmp), 
%    var(Vidtmp,Vn), 
%    % A domain predicate that matches the name of the predicate in body
%    assert(Aid), 
%    head(Aid,Jpredid), 
%    pred(Jpredid,Pntmp),
%    alist(Jpredid,N2,Cid),
%    cnst(Cid,Cval). 

%project2(Rid,Pn,Vn,Predid,N1,Jpredid,N2,Cval) :- 
%    % singlebody(Rid), 
%    % Variable in the head 
%    head(Rid,Predid), 
%    pred(Predid,Pn), 
%    alist(Predid,N1,Vid1), 
%    var(Vid1,Vn), 
%    % The variable Vn in the predicate of body
%    body(Rid,Bid), 
%    pred(Bid,Pntmp), 
%    alist(Bid,N2,Vidtmp), 
%    var(Vidtmp,Vn), 
%    % A domain predicate that matches the name of the predicate in body
%    assert(Aid), 
%    head(Aid,Jpredid), 
%    pred(Jpredid,Pntmp),
%    alist(Jpredid,N2,Cid),
%    cnst(Cid,Cval). 

% pproject(Rid,Vn) :- project(Rid,Pn,Vn,Predid,N1,Jpredid,N2,Cval). % project(Rid,Pn,Vn,Predid,N1,Jpredid,N2). 



% For a rule, check that all variables have been projected
% Will this ever happen?
%notprojected(Rid) :- 
%    head(Rid,Predid),
%    alist(Predid,N,Vid),
%    var(Vid,Vn), 
%    not pproject(Rid,Vn).
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Generate a mock assertion for trueprule

%maxctr(X) :- 
%   freectr(Y),
%   freectr(X),
%   X > Y,
%   X < 100. % Limit somewhat 

%maxctr(X) :- freectr(X).

% This assumes we always have two freectr's, now we generate 
% it by the factrenderer, so that there always is freectr(0).
%maxctr(C) :-
%    freectr(C),
%    freectr(C1),
%    C > C1. 

%maxctr(C)  :- 
%    freectr(C),
%    not freectr(C1),
%    C != C2. 

% maxctr(@setctr(C)) :- freectr(C).
freectr(@setctr(C)) :- freectr(C).


% assert(Rid) :- trueprule(Rid). 

% This seems to have stopped stuff badly 
% 4 { cassert(Aid), chead(Aid,Aid+1), cpos(Aid+1), cpred(Aid + 2, Pn ) } 4 :- 

% This version counts on a single trueprule, but subsumed by the one below
% which does all of the stuff. 
%6 { hasrule(1,Aid), newfact(Aid), assert(Aid), head(Aid,Aid+1), pos(Aid+1), pred(Aid + 1, Pn ) } 6 :- 
%    trueprule(Rid), 
%    head(Rid,Predid), 
%    pred(Predid,Pn),
%    freectr(Aid).

% We use the unique IDs of the assertions to form 'namespaces' to avoid conflicts
% This may backfire if we create a new ground rule with so many bodies that the 
% incremented IDs overflow to the 'next' new ground rule. 
% 7 { hasrule(1,Aid+Hid), newfact(Aid+Hid), assert(Aid+Hid), head(Hid+Aid,Hid+Aid+1), pos(Hid+Aid+1), pred(Hid+ Aid + 1, Pn ), nxt(@nxtctr2(Aid)) } 7 :- 
% 8 { hasrule(1,@getctr()), newfact(@getctr(), Rid, Hid), assert(@getctr()), head(@getctr(),@getctr()+1), pos(@getctr()+1), pred(@getctr() + 1, Pn ), alist(@getctr() + 1,N1,Cid), nxt(@nxtctr2(Hid)) } 8 :-
7 { hasrule(1,@getctr()), newfact(@getctr(), Rid, Hid), assert(@getctr()), head(@getctr(),@getctr()+1), pos(@getctr()+1), pred(@getctr() + 1, Pn ), nxt(@nxtctr2(Hid)) } 7 :-
    % Hid will make Rid true 
    trueprules(Rid, Hid), 
    head(Rid,Predid), 
    pred(Predid,Pn),
    freectr(Aid). 
    % New stuff for alist here
%    alist(Predid,N1,Varid),
%    var(Varid,Vn), 
%    % Now the same variable in body 
%    body(Rid,Bid),
%    % Must have same variable name, but at position N2
%    var(BVarid,Vn), 
%    alist(Bid,N2,BVarid),
%    % Now we look at the ground fact at position N2
%    % Pn2 is the name of the ground fact. 
%    % pred(Hid,Pn2), 
%    alist(Hid,N2,Cid),               % get the constant ID responsible for this variables
%    cnst(Cid,Val). 
    
% We have generated head for a new ground fact.
% Here we generate the argument list for the head and for this
% we need a handle to the new ground fact source rule and justifying rule 
% We use newfact/3 here to trigger the generation.
alist(Id+1,N1,Cid) :- 
    % A new fact ID has been generated for 
    newfact(Id,Rid,Jid), 
    % This is the variable on the head of the generated rule
    % and this must be mapped to a constant.
    head(Rid,Predid), 
    pred(Predid,Pn),
    alist(Predid,N1,Varid),
    var(Varid,Vn), 
    % Now we look for the same variable in the body to know where 
    % (which position) we should look for the constant.
    body(Rid,Bid),
    % Must have same variable name, but at position N2
    var(BVarid,Vn), 
    alist(Bid,N2,BVarid),
    % Finally, we connect the constant from the ground fact 
    % with the variable in the head. 
    alist(Jid,N2,Cid),               % This is the actual constant 
    cnst(Cid,Val). 
    
pot_fact(Rid) :- 
    trueprule(Rid), 
    head(Rid,Predid), 
    pred(Predid,Pn),
    freectr(Aid).

% Generate alist for the new facts
% alist(Aid + Hid + 1,N1,Cid) :- 
%alist(@getctr() + 1,N1,Cid) :- 
%    % Hid is the one where we have the constant value
%    % Rid is where we access the variable information 
%    trueprules(Rid, Hid), 
%    % Pn is the name of the ground fact. 
%    pred(Hid,Pn), 
%    % Now we get the variable info, Vn is the variable in the head at position N1
%    head(Rid,Predid),
%    alist(Predid,N1,Varid),
%    var(Varid,Vn), 
%    % Now the same variable in body 
%    body(Rid,Bid),
%    % Must have same variable name, but at position N2
%    var(BVarid,Vn), 
%    alist(Bid,N2,BVarid),
%    % Now we look at the ground fact at position N2
%    alist(Hid,N2,Cid),               % get the constant ID responsible for this variables
%    cnst(Cid,Val), 
%    freectr(Aid).

% Generate alist for the new facts
%alist(Aid + Hid,N1,Cid) :- 
%    trueprules(Rid, Hid), 
%    boundvv(Rid,Vn,Val,Predid,Jpredid),  % trueprule means that there is only one Jpredid
%    alist(Jpredid,N,Cid),               % get the constant ID responsible for this variables
%    cnst(Cid,Val), 
%    head(Rid,Hpredid), 
%    Hpredid != Predid,                   % somewhat redundant 
%    alist(Hpredid,N1,Varid),               % get the position of variable named Vn
%    var(Varid,Vn), 
%    freectr(Aid).

% See if the rules can see them after the generation 
allmydpreds(Pn,Predid) :- 
    assert(Aid),
    head(Aid,Predid),
    pred(Predid,Pn). 

% Check the sbind consistency 
newnotbound(Jpredid) :- 
    assert(Aid),
    newfact(Aid,Arid,Hid),  
    head(Aid,Jpredid),
    ground(Rid), 
    body(Rid,Predid),
    not sbindit(Rid,Predid,Jpredid). 

%
pushbind(Rid,Predid,Jpredid) :- 
    rule(Rid),
    body(Rid,Predid),
    pred(Predid,Pn),
    assert(Aid), 
    head(Aid,Jpredid),
    pred(Jpredid,Pn).

vspushbind(Prednm,Predid,Jpredid) :- pushbind(Rid,Predid,Jpredid), pred(Predid,Prednm).

% Get the variables which have been assigned by sbindit 
pushbindv(Rid,Vn,Predid,Jpredid) :- 
   pushbind(Rid,Predid,Jpredid), 
   alist(Predid,N,Vid), 
   var(Vid,Vn). 

% Debugging to show name and value of a binding, not needed
pushbindvv(Rid,Vn,Val,Predid,Jpredid,N) :- 
   pushbindv(Rid,Vn,Predid,Jpredid),
   alist(Predid,N,Vid), 
   var(Vid,Vn),
   alist(Jpredid,N,Cid),
   cnst(Cid,Val).

% Which predicate arguments must have the same value 
% within due to variable named Vn.
mustbesame(Rid,Vn,Predid1,N1,Predid2,N2) :- 
    rule(Rid),
    body(Rid,Predid1),
    pred(Predid1,Pn1),
    alist(Predid1,N1,Vid1),
    var(Vid1,Vn), 
    Predid1 != Predid2,
    body(Rid,Predid2),
    pred(Predid2,Pn2),
    alist(Predid2,N2,Vid2),
    var(Vid2,Vn). 

constrained(Rid,Vn) :- mustbesame(Rid,Vn,Predid1,N1,Predid2,N2).

%mustbesameclosure() :- 
%    mustbesame(Rid,Vn,Predid1,N1,Predid2,N2), 

vardepends(Rid,Vn1,Vn2,Predid) :- 
     rulevar(Rid,Vid1), 
     rulevar(Rid,Vid2), 
     Vn1 != Vn2, 
     body(Rid,Predid), 
     alist(Predid,N1,Vid1),
     alist(Predid,N2,Vid2),
     N1 != N2, 
     Vid1 != Vid2,
     var(Vid1,Vn1),
     var(Vid2,Vn2). 

% Which two predicates Pn1, Pn2 in rule Rid must have same value 
% at indices N1 and N2 due to variable Vn
mustbesamed(Rid,Vn,Predid1,Pn1,N1,Predid2,Pn2,N2) :- 
    mustbesame(Rid,Vn,Predid1,N1,Predid2,N2),
    pred(Predid1,Pn1),
    pred(Predid2,Pn2). 

% Same as above but lists thoe domain predicates which match
mustbesamedtrue(Rid,Vn,Predid1,Pn1,N1,Predid2,Pn2,N2,Dp1,Dp2,Val) :- 
    mustbesamed(Rid,Vn,Predid1,Pn1,N1,Predid2,Pn2,N2), 
    assert(A1),
    head(A1,Dp1),
    pred(Dp1,Pn1), 
    alist(Dp1,N1,Cid1),
    cnst(Cid1,Val),
    assert(A2),
    head(A2,Dp2),
    pred(Dp2,Pn2), 
    alist(Dp2,N2,Cid2),
    cnst(Cid2,Val). 
    
notconstrained(Rid,Vn) :- 
    rulevar(Rid,Vid), 
    var(Vid,Vn), 
    not constrained(Rid,Vn). 

%boundbypred(Rid,Predid1,Vn1,Vn2) :- 
%    rule(Rid),
%    body(Rid,Predid1),
%    pred(Predid1,Pn1),
%    alist(Predid1,N1,Vid1),
%    var(Vid1,Vn1), 
%    N1 != N2,
%    alist(Predid1,N2,Vid2),
%    var(Vid2,Vn). 
    
   
% Which domain predicates are compatible wrt
% variable name Vn in rule Rid. 
compatible(Rid,Vn,J1,J2) :- 
    mustbesamed(Rid,Vn,Predid1,Pn1,N1,Predid2,Pn2,N2),
    assert(A1), 
    head(A1,J1), 
    pred(J1,Pn1),
    alist(J1,N1,C1), 
    cnst(C1,Val), 
    A1 != A2, 
    assert(A2), 
    head(A2,J2), 
    pred(J2,Pn2),
    alist(J2,N2,C2), 
    cnst(C2,Val). 

% Which domain predicates are not compatible wrt. variable Vn
% This may just blow up 
incompatible(Rid,Vn,J1,J2) :- 
    mustbesamed(Rid,Vn,Predid1,Pn1,N1,Predid2,Pn2,N2),
    assert(A1), 
    head(A1,J1), 
    pred(J1,Pn1),
    alist(J1,N1,C1), 
    cnst(C1,Val1), 
    A1 != A2, 
    assert(A2), 
    head(A2,J2), 
    pred(J2,Pn2),
    alist(J2,N2,C2), 
    cnst(C2,Val2),
    Val1 != Val2. 

% Now choose from pushbind 
% This does not seem to bring any advances 
2 {pushbind2(Rid,Predid1,Jpredid1), pushbind2(Rid,Predid2,Jpredid2) } 2 :- 
    manybodies(Rid), 
    pushbind(Rid,Predid1,Jpredid1), 
    pushbind(Rid,Predid2,Jpredid2), 
    Predid1 != Predid2,
    mustbesame(Rid,Vn,Predid1,N1,Predid2,N2),
    compatible(Rid,Vn,Jpredid1,Jpredid2). 

% We want to cut or name a subset of the variables in here 
% so that it can be recognized by other rules as something 
% that can be constructed into a new fact. 
% What we want: a sensible mapping between the variables in head
hdvbind(Rid,Pn,Predid,Vn,Val,N1,Jpredid) :- 
    head(Rid,Hid),
    pred(Hid,Pn), 
    alist(Hid,N1,Vid),
    var(Vid,Vn),
    % A binding 
    % pushbindv(Rid,Vn,Predid,Jpredid). 
    pushbindvv(Rid,Vn,Val,Predid,Jpredid,N2).

% Now get the relative compatibility for variable X
% as expressed by the eventual source domain predicate of them. 
comppushbind(Rid,Vn1,Vn2,Jpred1) :- 
    compatible(Rid,Vn1,Jpred1,Jpred2), 
    pushbindvv(Rid,Vn2,Val,Predid,Jpred1,N2),
    Vn1 != Vn2. 

% Keep a mapping between a value at a position in the head to 
% a value at a position in the body. 
headtopred(Rid,Vn,Hpredid,N1,Pn,Predid,N2) :-
    head(Rid,Hpredid),
    alist(Hpredid,N1,Vid1),
    var(Vid1,Vn),
    body(Rid,Predid),
    pred(Predid,Pn),
    alist(Predid,N2,Vid2),
    var(Vid2,Vn).


% Our dream rule would be 
%assign(Id1,Vn,Val) :- 
%    assert(A1),
%    pred(A1,Pn1), 
%    assert(A2),
%    pred(A2,Pn2). 

nxtval(Rid,Predid1,Vn1,Val1,Vn2,Val2) :- 
    hdvbind(Rid,Pn1,Predid1,Vn1,Val1,N1,Justid1), 
    hdvbind(Rid,Pn1,Predid1,Vn2,Val2,N2,Justid2), 
    N1 + 1 == N2, 
    notconstrained(Rid,Vn1), 
    notconstrained(Rid,Vn1). 

%nxtval(Rid,Vn1,Val1,Vn2) :- 
%    hdvbind(Rid,Pn1,Predid1,Vn1,Val1,N1,Justid1), 
%    hdvbind(Rid,Pn1,Predid1,Vn2,Val2,N2,Justid2), 
%    N1 + 1 == N2, 
%    constrained(Rid,Vn1), 
%    notconstrained(Rid,Vn1),
% 
%    We need to look at the inside structure of the rule 
%    to determine if there is a path of mustbesame() which 
%    reaches from Vn1 to Vn2.
%
%    mustbesame(Rid,Vn1,P11,N11,P21,N21), 
%    mustbesame(Rid,Vnt1,P21,N12,P22,N22),
%    ...
%    mustbesame(Rid,Vn2,P2[i],N1[j],P2[k],N2[k]). 
%
%    This needs to be done by a conjunctive list where 
%    all of these would be real values.
% 
%     
%
%    Is there any way we could "record" the occurring P[i][j]
%    to act as a unique key. Some kind of power series
%    expansion?
% 
%    On the other hand for each rule we need to setup the chain 
%    of relations between the variables; the required reachability of 
%    variables in the head by means of predicates, which can then 
%    be associated with domain predicates. 
%

% Are two assignments in the variables of the head 
% compatible with values.
cmpassgn(Vn1,Val1,Vn2,Val2) :- 
    hdvbind(R,Pn,Predid1,Vn1,Val1,N1,Jpredid1),
    hdvbind(R,Pn,Predid2,Vn2,Val2,N2,Jpredid2),
    N1 != N2,
    % Now observe the innards of the rule to make sure that 
    % these two are compatible. 
    % Compatible only checks the compatibility of a contested 
    % variable indicated by mustbesame()
    compatible(R,Vn1,Jpredid1,Jpredid2), 
    compatible(R,Vn2,Jpredid1,Jpredid2). % XXX we should continue here 

% Variables Vn1 and Vn2 depend on each other in the sense that 
% associating a domain predicate with Predid forces both values. 
vardepends(Rid, Vn1, Vn2, Predid) :- 
    body(Rid,Predid), 
    alist(Predid,N1,Vid1), 
    alist(Predid,N2,Vid2), 
    N1 != N2, 
    var(Vid1,Vn1), 
    var(Vid2,Vn2). 

% Is there a forced dependency between variables named 
% Vn1, Vn3.
% This is within one predicate.
depchain(R,Vn1,Vn3) :- 
    vardepends(R, Vn1, Vn2, Predid1), 
    vardepends(R, Vn2, Vn3, Predid2),
    Vn1 != Vn3. 

% Depchain closure
depchain(R,Vn1,Vn3) :- 
    depchain(R,Vn1,Vn2),
    depchain(R,Vn2,Vn3),
    Vn1 != Vn3,
    Vn1 != Vn2.

% This checks variable dependencies between predicates 
depchain(R,Vn1,Vn3) :- 
    vardepends(R, Vn1, Vn2, Predid1), 
    vardepends(R, Vn2, Vn3, Predid4),
    mustbesamed(R,Vn2,Predid1, Pn1, N1, Predid4,Pn2,N2), 
    Vn1 != Vn3. 

% Value Val of variable Vn in predicate Pn, Predid
% position N, given domain predicate Jpredid. 
varvalue(R,Vn,Pn,Predid,N,Val,Jpredid) :- 
    assert(A1),
    A1 != R, 
    head(A1,Jpredid),
    pred(Jpredid,Pn), 
    alist(Jpredid,N,Cid), 
    cnst(Cid,Val),
    rulepred(R,Predid),
    pred(Predid,Pn),
    alist(Predid,N,Vid),
    var(Vid,Vn).

% Replicate depchain with valchain, where we bind two variables and 
% their values together. 
valchain(R,Vn1,Val1,Vn2,Val2) :-  
    mustbesamedtrue(R,Vn1,Predid1,Pn1,N1,Predid2,Pn2,N2,Dp1,Dp2,Val1), 
    vardepends(R, Vn1, Vn2, Predid2), 
    Vn1 != Vn2, 
    varvalue(R,Vn2,Pn2,Predid2,N3,Val2,Dp2). 
    
valchain(R,Vn1,Val1,Vn2,Val2) :-  
    not mustbesame(R,Vn1,Predid1,N3,Predid2,N4), 
    vardepends(R, Vn1, Vn2, Predid2), 
    Vn1 != Vn2, 
    varvalue(R,Vn1,Pn1,Predid1,N4,Val1,Dp1),
    varvalue(R,Vn2,Pn2,Predid2,N3,Val2,Dp2).

valchain(R,Vn1,Val1,Vn3,Val3) :- 
    valchain(R,Vn1,Val1,Vn2,Val2),
    valchain(R,Vn2,Val2,Vn3,Val3),
    Vn1 != Vn3. 

headvar(Rid,Vn) :- 
    head(Rid,Predid),
    alist(Predid,N,Vid), 
    var(Vid,Vn). 

% Is this variable only occurring in the 
% body of the rule?
internalvar(Rid,Vn,Predid1) :- 
    rulepred(Rid,Predid1), 
    alist(Predid1,N,Vid),
    var(Vid,Vn), 
    not headvar(Rid,Vn). 

heads(Rid,Vn1,Val1,Vn2,Val2) :- 
    headvar(Rid,Vn1),
    headvar(Rid,Vn2),
    Vn1 != Vn2, 
    % We cant count on this being 
    % really true, as we'd need to 
    % record the path we encounter. 
    valchain(Rid,Vn1,Val1,Vn2,Val2).
       

%foo() :- 
%     eligible(Vn,Val,), 
%     mustbesamed(Rid,Vn,9,"edge",2,6,"edge",1).

%EOF metaground_fact.lp 