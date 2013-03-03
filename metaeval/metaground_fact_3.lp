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

% assert(Rid) :- trueprule(Rid). 

% This seems to have stopped stuff badly 
% 4 { cassert(Aid), chead(Aid,Aid+1), cpos(Aid+1), cpred(Aid + 2, Pn ) } 4 :- 
6 { hasrule(1,Aid), newfact(Aid), assert(Aid), head(Aid,Aid+1), pos(Aid+1), pred(Aid + 1, Pn ) } 6 :- 
    trueprule(Rid), 
    head(Rid,Predid), 
    pred(Predid,Pn),
    freectr(Aid).

% We generate a balist instead of alist and point it 
% to the variables assigned. 
% calist(Aid + 2,N1,Cid) :- 
alist(Aid + 1,N1,Cid) :- 
    trueprule(Rid), 
    boundvv(Rid,Vn,Val,Predid,Jpredid),  % trueprule means that there is only one Jpredid
    alist(Jpredid,N,Cid),               % get the constant ID responsible for this variables
    cnst(Cid,Val), 
    head(Rid,Hpredid), 
    Hpredid != Predid,                   % somewhat redundant 
    alist(Hpredid,N1,Varid),               % get the position of variable named Vn
    var(Varid,Vn), 
    freectr(Aid).

% See if the rules can see them after the generation 
allmydpreds(Pn,Predid) :- 
    assert(Aid),
    head(Aid,Predid),
    pred(Predid,Pn). 

% Check the sbind consistency 
newnotbound(Jpredid) :- 
    assert(Aid),
    newfact(Aid), 
    head(Aid,Jpredid),
    ground(Rid), 
    body(Rid,Predid),
    not sbindit(Rid,Predid,Jpredid). 



%EOF metaground_fact.lp 