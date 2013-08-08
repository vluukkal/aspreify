% A very simple grounder type of thing

% Make a Lua counter 
#begin_lua
local idctr = 0
local compid = 0
local compids = {}

local lists = {}

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

function mklist(lid,len)
  check = lists[lid]  
  if check == nil then 
    lists[lid] = length 
  else
    msg = "mklist: list id " .. tostring(lid) .. " exists already."
    print(msg)
  end
end

function listlen(id)
  check = lists[lid]  
  if check == nil then 
    msg = "listlen: list id " .. tostring(lid) .. " does not exist."
    print(msg)
    return 0
  else
    length = lists[lid]
    return length 
  end
end

#end_lua.

% Set the counter properly, but it seems we 
% need to have this _lexicographically_ before the 
% points of use in the file, for this to work. Ugh. 
freectr(@setctr(C)) :- freectr(C).

%
% The variable 'Vn' in the head
% of rule 'Rid' is in predicate 'Pn'
% at position 'Idx'.
% It is assigned by body 'Bidx' in 
% position 'Bpredidx'.
%
% No mention of the predicate providing the variable. 
%
headvarval(Rid,Pn,Idx,Vn,Bidx,Bpredidx) :- 
  rule(Rid), 
  head(Rid,Pid),
  pred(Pid,Pn), 
  alist(Pid,Idx,Vid), 
  var(Vid,Vn),
  bodyvarpos(Rid,Vn,Bidx,Bpredidx).

%
% Variable 'Vn' in rule 'Rid' is assigned
% by body index 'Bidx' in position 'Idx'.
%
% No mention about 
%
bodyvarpos(Rid,Vn,Bidx,Idx) :- 
  rule(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 

% Map between bodies and eligible justifications 
% Give these a new identity. 
2 { map(@getctr(),Rid,Bidx,Jid), nxt(@nxtctr(1)) } 2 :-
  rule(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  assert(Aid), 
  head(Aid,Jid),
  % freectr(Ctr), 
  pred(Jid,Pn).

% Which two maps pertain to same variables on different bodies
mapsonvar(Rid,Mapid1,Mapid2,Vn) :- 
  map(Mapid1,Rid,Bidx1,Jid1),
  map(Mapid2,Rid,Bidx2,Jid2), 
  Mapid1 != Mapid2, 
  % Bidx1 != Bidx2, % This seems to kill all?
  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2). 

% Next try to deduce which two maps combined 
% give same results for variables. 
mapsagreeonvar(Rid,Mapid1,Mapid2,Vn, Val1) :- 
  map(Mapid1,Rid,Bidx1,Jid1),
  map(Mapid2,Rid,Bidx2,Jid2), 
  Mapid1 != Mapid2, 
  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2), 
  alist(Jid1,Bpredidx1,Vid1), 
  cnst(Vid1,Val1), 
  alist(Jid2,Bpredidx2,Vid2), 
  cnst(Vid2,Val2), 
  Val1 == Val2.

% mapsdisagreeonvar(Rid,Mapid1,Mapid2,Vn) :- 
foo :- % avoid clutter for now 
  map(Mapid1,Rid,Bidx1,Jid1),
  map(Mapid2,Rid,Bidx2,Jid2), 
  Mapid1 != Mapid2, 
  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2), 
  alist(Jid1,Bpredidx1,Vid1), 
  cnst(Vid1,Val1), 
  alist(Jid2,Bpredidx2,Vid2), 
  cnst(Vid2,Val2), 
  Val1 != Val2.
    
% litem(id,val,0,nxt)

% id   - ID of this list item 
% val  - points to the contained value 
% nxt  - points to the next list item 
% len  - the length of the list in the tail

% Make each mapitem into a list of length one. 
%2 { 
%  litem(@getctr(), Mapid, 0, 1), 
%  % lst(@mklist(@getctr(),1)), 
%  nxt(@nxtctr(1))
%} 2 :- 
%  map(Mapid,Rid,N,Predid). 

% Make each mapitem into a list of length one for a particular rule 
%2 { 
%  litem(@getctr(), Rid, Mapid, 0, 1), 
%  % lst(@mklist(@getctr(),1)), 
%  nxt(@nxtctr(1))
%} 2 :- 
%  map(Mapid,Rid,N,Predid). 

% Make each mapitem for position one into a list of length one for a particular rule 
2 { 
  litem(@getctr(), Rid, Mapid, 0, 1), 
  nxt(@nxtctr(1))
} 2 :- 
  map(Mapid,Rid,1,Predid). 

2 { 
  litem(@getctr(), Rid, Mapid, Lid1, N), 
  nxt(@nxtctr(1))
} 2 :- 
  % We have a map item for body position N
  map(Mapid,Rid,N,Predid),
  % We have an existing list for position M ...
  % litem(Lid1,Rid,Mapid1, Nxt, N+1),  
  litem(Lid1,Rid,Mapid1, Nxt, M),  
  % ... where M is one less than N
  bodycount(Rid,Maxn), 
  N == M+1, 
  M <= Maxn. 


%isinlist(Parentid,Listid,Mapid) :- 
%  litem(Listid,Mapid,Next,_),
%  Next != 0, 
%  isinlist(Parentid,Next,Mapid). 

%2 { lc2(Listid, Mapid1), lc2(Listid, Mapid2) } 2  :- 
% chunga :- 

% List closure 
lc2(Listid,Mapid1) :- 
  litem(Listid,Rid,Mapid1,Nxt,Len), 
  litem(Nxt,Rid,Mapid2,Nxt2,Len2). 

lc2(Listid,Mapid2) :- 
  litem(Listid,Rid,Mapid1,Nxt,Len), 
  litem(Nxt,Rid,Mapid2,Nxt2,Len2). 

lc2(Listid,Mapid2) :- 
  lc2(Listid,Mapid1), 
  litem(Listid2, Rid,Mapid1, Nxt, Len), 
  litem(Nxt, Rid, Mapid2, Nxt2, Len). 

isinlist(L,M) :- lc2(L,M). 
% This is for lists of length 1, singletons 
isinlist(L,M) :- litem(L, Rid, M, 0, 1).

%foo :- 
% listclosure(Listid,Mapid,Mapid2) :- 
%  litem(Listid,Mapid,Nxt,Len), 
%  litem(Nxt,Mapid2,Nxt2,Len2). 

%foo :- 
% listclosure(Listid,Mapid1,Mapid3) :- 
%  litem(Lid1,Mapid2, Lid2,Len1), 
%  litem(Lid2,Mapid3,Lid3,Len2), 
%  listclosure(Listid,Mapid1,Mapid2). 

%listclosure(Listid,Mapid,Mapid2) :- 
%  litem(Listid,Mapid,Nxt,Len), 
%  litem(Nxt,Mapid2,Nxt2,Len2),
%  listclosure(Listid,Mapid1,Mapid2), 
%  litem(Nxt,Mapid3,Nxt3,Len3).
%  litem(Nxt,Mapid3,Nxt3,Len3).


listlen(Listid,N) :- 
  litem(Listid,Rid, Mapid,Next,N). 

% Each inlist/4 of length bodycount/2 should now be evaluated 
% to produce an OK wrt. the rules and produced variables. 
% Potentials are those lists that have the same length
% as indicated by bodycount. 
% This should no longer be needed, lists are potential by construction 
potential(Rid,Lid) :- 
  bodycount(Rid,N), 
  litem(Lid,Rid,Mapid,Nxt,N). 



% Now we assign the N'th bodypredicate of Rid according to Lid
% This is just renaming the information in the list for now. 
mkassign(Lid,Rid,Predid,Mapid,Jid,N) :- 
  potential(Rid,Lid), 
  bodylist(Rid,N,Predid), 
  % There is a mapid in this list 
  isinlist(Lid,Mapid),
  litem(Lid2,Rid,Mapid,Nxt,N), % now the index is matched to bodylist ...
  % Which pertains to this N'th bodypredicate 
  map(Mapid, Rid, N, Jid). 

tstassign(Lid,Rid,Vn,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  bodyvarpos(Rid,Vn,N,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

assignat(Lid,Rid,Bpredidx,Vn,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  bodyvarpos(Rid,Vn,N,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

% ---------------------

% Derive a simple position, value assignment for a rule 
% to be compared with groundassign/3.
assign(Lid,Rid,N,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  headvarval(Rid,Pn,N,Vn,Bidx,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

% Could also use nxt(X) and X instead of getctr. 
%timedassign(Lid,@getctr(),Rid,N,Val) :- 
%  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
%  headvarval(Rid,Pn,N,Vn,Bidx,Bpredidx), 
%  alist(Jid,Bpredidx,Cid), 
%  cnst(Cid,Val).


% Derive a simple position, value assignment for an existing
% ground predicate to be compared with assign/5.  
groundassign(Jid,N,Val) :- 
  assert(Jid),
  head(Jid,Predid),
  alist(Predid,N,Cid), 
  cnst(Cid,Val). 

%timedgroundassign(Jid,@getctr(),N,Val) :- 
%  assert(Jid),
%  head(Jid,Predid),
%  alist(Predid,N,Cid), 
%  cnst(Cid,Val). 

% ---------------------
% Start comparing the potential, list based assignments (internal facts) with the 
% existing ground facts (external facts). 

onediffext(Lid,Rid,Jid,N) :- 
  assign(Lid,Rid,N,Val1), 
  groundassign(Jid,N,Val2), 
  Val1 != Val2, 
  % Same predicate name 
  head(Rid,Headid), 
  head(Jid,JHeadid), 
  pred(Headid,Pn), 
  pred(JHeadid,Pn). 

onesameext(Lid,Rid,Jid,N) :- 
  assign(Lid,Rid,N,Val1), 
  groundassign(Jid,N,Val2), 
  Val1 == Val2, 
  % Same predicate name 
  head(Rid,Headid), 
  head(Jid,JHeadid), 
  pred(Headid,Pn), 
  pred(JHeadid,Pn). 

fulldiffext(Lid,Rid,Jid) :- 
  assign(Lid,Rid,_,_), 
  groundassign(Jid,_,_), 
  % Different predicate name 
  head(Rid,Headid), 
  head(Jid,JHeadid), 
  pred(Headid,Pn1), 
  pred(JHeadid,Pn2),
  Pn1 != Pn2. 
  
% One differing argument is enough to make it completely different 
fulldiffext(Lid,Rid,Jid) :- 
  onediffext(Lid,Rid,Jid,N).

%novel(Lid,Rid,@getctr()) :- 
%  assert(Jid), 
%  assign(Lid,Rid,_,_),      % we have an assignment, but we ignore the values, could be a projection ...
%  not fullsameext(Lid,Rid,Jid). 

% These are attempts to bring 'time' in sense of the current counter in 
% the equivalence checking. 
%onesame(Lid,Rid,@getctr()) :- 
%  fullsameext(Lid,Rid,Jid). 

%novelext(Lid,Rid,@getctr()) :- 
%  assign(Lid,Rid,_,_), 
%  not onesame(Lid,Rid,@getctr()).

% Pick one of internal to be a representative
%novelinternal(Lid1)
%:- 
%  fullsameint(Lid1,Rid,Lid2),
%  not novelinternal(Lid1).

% We create a cluster of equivalent lists
% XXX 
% This is not used, but left here as an attempt 
% to create a new 'namespace' for equivalent lists.
% XXX
% 
%4 {
%eqcluster(@getctr(), Lid1, Rid),
%eqcluster(@getctr(), Lid2, Rid),
%primus(@getctr(),Lid1), 
%nxt(@nxtctr(1))
%} 4 :- 
%  fullsameint(Lid1,Rid,Lid2), 
%  not prprimus(Lid2).        
%  % not prprimus(Lid1).        % This unsats
%  % not primus(X,Lid1),        % These two diverge 
%  % nxt(X).		       % ...

%prprimus(Lid) :- primus(X,Lid). 

%smallestsame(Lid1,Rid) :- 
%  fullsameint(Lid1,Rid,Lid2), 
%  fullsameint(Lid2,Rid,Lid3),
%  Lid1 < Lid3,
%  Lid1 < Lid2.

%largestsame(Lid3,Rid) :- 
%  fullsameint(Lid1,Rid,Lid2),
%  fullsameint(Lid2,Rid,Lid3),
%  Lid3 > Lid1,
%  Lid3 > Lid2.

% Now try to attach other equivalent ones to this cluster 
%eqcluster(X,LidSame,Rid) :- 
%  primus(X,Lid),
%  fullsameint(Lid,Rid,LidSame). 

% Clusters of same values may be built on different 
% primuses. 
%samecluster(C1,C2) :- 
%  primus(C1,Lid1), 
%  primus(C2,Lid2), 
%  not samecluster(C2,C1), 
%  fullsameint(Lid1,Rid,Lid2).

%fse(Lid,Rid,Jid,@getctr()) :- fullsameext(Lid,Rid,Jid).

%tassert(Jid,@getctr()) :- assert(Jid). 

% This does not pertain to predicates with more than one argument
fullsameext(Lid,Rid,Jid) :- 
  onesameext(Lid,Rid,Jid,N1), 
  assert(Jid), 
  not fulldiffext(Lid,Rid,Jid).

% For cases with one argument
fullsameext(Lid,Rid,Jid) :- 
  head(Rid,Hid), 
  arity(Hid,1), 
  onesameext(Lid,Rid,Jid,N). 

% ---------------------
% Compare the potential, list based assignments (internal facts) with themselves
% replicating the structure of the external comparisons. 

% Note that since both refer to same Rid, 
% we dont have to check the predicate. 
onediffint(Lid1,Rid,Lid2,N) :- 
  assign(Lid1,Rid,N,Val1), 
  assign(Lid2,Rid,N,Val2), 
  Lid1 != Lid2, 
  Val1 != Val2. 

onesameint(Lid1,Rid,Lid2,N) :- 
  assign(Lid1,Rid,N,Val1), 
  assign(Lid2,Rid,N,Val2), 
  Lid1 != Lid2, 
  Val1 == Val2. 

fulldiffint(Lid1,Rid,Lid2) :- 
  onediffint(Lid1,Rid,Lid2,N).

% This does not pertain to predicates with more than one argument
fullsameint(Lid1,Rid,Lid2) :- 
  onesameint(Lid1,Rid,Lid2,N1), 
  % goodassign(Lid1,Rid), % XXX kills all new facts 
  Lid1 < Lid2,
  not fulldiffint(Lid1,Rid,Lid2).

% Tag the leading argument of a fullsameint cluster 
% with justified/2 if there is one goodassign in the cluster
% The first term is the equivalence ID, second is the 
% justifying predicate. 
justified(Lid1,Lid1) :- 
  onesameint(Lid1,Rid,Lid2,N1),
  goodassign(Lid1,Rid). 
justified(Lid1,Lid2) :- 
  onesameint(Lid1,Rid,Lid2,N1),
  goodassign(Lid2,Rid). 



% For cases with one argument
% This seems to be precisely as the general case...
% However since there is only one of these, we at the 
% same time pick the internal one. 
2 {
  fullsameint(Lid,Rid,Jid), 
  pickinternal(Lid,Rid) 
} 2 :- 
  head(Rid,Hid), 
  arity(Hid,1), 
  onesameint(Lid,Rid,Jid,N),
  Lid < Jid.

% Make a closure of fullsameint's 
% We tag those which are not the 'smallest'
% XXX SHouldn't this be fullsameint rather than 
% onesameint?
2 {
fullsameint(Lid1,Rid,Lid3),
subcluster(Lid2,Rid)
} 2 :- 
  fullsameint(Lid1,Rid,Lid2), 
  fullsameint(Lid2,Rid,Lid3), 

  Lid1 < Lid3,
  % goodassign(Lid1,Rid),    % XXX
  not fulldiffint(Lid1,Rid,Lid3),
  not fullsameint(Lid3,Rid,Lid1).
  %not fullsameint(Lid3,Rid,Tmp),
  %nxt(Tmp).

% We assume that the closure has been constructed. 
% We have one 'main' cluster, which has more than one
% Lid1s. It could only have been constructed transitively 
% so it is identified as the source of the closure.
% The first term of fullsameint/3 is the key or identity of
% the cluster and all but the 'main' cluster have been 
% tagged with subcluster/2 by comparison. 

%pickinternal(Lid,Rid) :- 
%  fullsameint(Lid,Rid,Lid2),     % The 'main' cluster
%  not subcluster(Lid,Rid),
%  fullsameint(Lid2,Rid,Lid3).

pickinternal(Lid,Rid) :- 
  fullsameint(Lid1,Rid,Lid2),     % The 'main' cluster, identified by Lid1
  not subcluster(Lid1,Rid),
  justified(Lid1,Lid),            % There must be a justified/2 tagged entry associated with Lid1
  fullsameint(Lid2,Rid,Lid3).


% pickexternal(Lid,Rid) :- 
foo :- 
  fullsameint(Lid1,Rid,Lid2),     % The 'main' cluster, identified by Lid1
  not subcluster(Lid1,Rid),
  justified(Lid1,Lid),            % There must be a justified/2 tagged entry associated with Lid1
  % and now check the tags 
  Jid > Lid, 
  not fullsameext(Lid,Rid,Jid),
  assert(Jid).

pickexternal(Lid1,Rid) :- 
  fullsameint(Lid1,Rid,Lid2),
  not deny(Lid1,Rid).

goodorder(Lid,Rid,Aid) :- 
    assert(Aid), 
    fullsameext(Lid,Rid,Aid),
    Aid > Lid. 

deny(Lid,Rid) :- 
    assert(Jid),
    fullsameext(Lid,Rid,Jid),
    not goodorder(Lid,Rid,Jid). 


% Is something that is same still free?
%unused(Lid,Rid,Jid) :- 
%  fullsameext(Lid,Rid,Jid), 
%  not prassigned(Lid).




% ---------------------

% ---------------------



visibleassign(Lid,Rid,Vn,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  headvarval(Rid,Pn,N,Vn,Bidx,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

% If any two items in a list are same at same indexes
% we get novelfact
% novelfact(Lid,Rid) :- 

% If any two items in a list are different at same indexes
% we get nonnovelfact. 
%nonnovelfact(Lid,Rid,N) :- 
  % Find a predicate with the same name
  % as the derivation of this rule. 
%  assert(Aid), 
%  head(Aid,Hid), 
%  pred(Hid,Pn),      % 1. Pn must match 
%  alist(Hid,N,Cid),
%  cnst(Cid,Cval), 
%  % Now get the value from the assignment 
%  head(Rid,Nid),
%  pred(Nid,Pn),       % [1] Must match Pn 
  

% Sameassign
% samealids(Lid1,Rid,Lid2,N) :- 
samealids(Lid1,Rid,Vn,Lid2) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
  visibleassign(Lid1,Rid,Vn,Val1),   
  visibleassign(Lid2,Rid,Vn,Val2),
  Lid1 != Lid2,
  Val1 = Val2. 

diffalids(Lid1,Rid,Vn,Lid2) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
  visibleassign(Lid1,Rid,Vn,Val1),   
  visibleassign(Lid2,Rid,Vn,Val2),
  Lid1 != Lid2,
  Val1 != Val2. 

projectdiffalid(Lid1,Rid,Lid2) :- diffalids(Lid1,Rid,Vn,Lid2).


% Is there an assignment to position N 
% of Rid in ground predicate Aid. 
sameassign(Lid,Rid,Aid,N) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
  visibleassign(Lid,Rid,Vn,Val1),   
  head(Rid,Hid1), 
  alist(Hid1,N,Vid1), 
  var(Vid1,Vn), 
  arity(Hid1,A1), 
  pred(Hid1,Pn), 
  % Now compare to existing facts 
  assert(Aid), 
  head(Aid,Hid2), 
  % Same predicate name with same Value at the same place
  pred(Hid2,Pn), 
  alist(Hid2,N,Cid1),
  cnst(Cid1,Val1). 

% Negation of sameassign/4
% Meaning that at least one argument is different, so at least 
% one argument of Aid is incomaptible with Lid. 
diffassign(Lid,Rid,Aid,N) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
  visibleassign(Lid,Rid,Vn,Val1),   
  head(Rid,Hid1), 
  alist(Hid1,N,Vid1), 
  var(Vid1,Vn), 
  arity(Hid1,A1), 
  pred(Hid1,Pn), 
  % Now compare to existing facts 
  assert(Aid), 
  head(Aid,Hid2), 
  % Same predicate name with different Value at the same place
  pred(Hid2,Pn), 
  alist(Hid2,N,Cid1),
  cnst(Cid1,Val2),
  Val1 != Val2. 

% This enumerates those ground predicates 
% which may be pertinent for this List of assignments. 
feasibleground(Lid,Rid,Aid) :- 
  visibleassign(Lid,Rid,Vn,Val), 
  head(Rid,Predid),
  pred(Predid,Pn), 
  % There is an assertion with same predicatename
  assert(Aid),
  head(Aid,Justid),
  pred(Justid,Pn).

% For any two Ground facts the Lid is different or not same 
% reallynow(Lid,Rid,Aid,N) :- 
% alldiffer(Lid,Rid) :- 
%  diffassign(Lid,Rid,Aid1,N), 

  % There is an assignment list 
%  potential(Rid,Lid),
  % The predicate names of Rid and Aid must be same 
%  head(Rid,Predid),
%  pred(Predid,Pn), 
  % There is an assertion
%  assert(Aid1),
%  head(Aid1,Justid1),
%  pred(Justid1,Pn1),
%  not reallysame(Lid,Rid,Aid1). 

% Another way:
% 1. There cannot be an assertion
% 2.1 that would be the same
% 2.2 that would be the same

% Tag each assertion with differ or same... 
% differ(Rid,Aid,Lid)
% same(Rid,Aid,Lid)


% Something is really same, if there are no diffassign/4 
% associated with it, but there is a sameassign. 
reallysame(Lid,Rid,Aid) :- 
  sameassign(Lid,Rid,Aid,N1), 
  head(Aid,Predid),
  alist(Predid,N2,Cid), 
  not diffassign(Lid,Rid,Aid,N2), 
  % And the assertion has not been produced by this lid
  not assigned(Lid,Aid).

projectreallysame(Lid,Rid) :- reallysame(Lid,Rid,Aid).


reallydiff(Lid,Rid,Aid) :- 
  projectdiff(Lid,Rid,Aid),
  not projectreallysame(Lid,Rid). 


projectsame(Lid,Rid,Aid) :- sameassign(Lid,Rid,Aid,N). 

% If there is a single projectdiff, then they are different 
projectdiff(Lid,Rid,Aid) :- diffassign(Lid,Rid,Aid,N). 

% All arguments are same and there is no single 
% differing argument. So Lid and Aid are the same. 
samelistground(Rid,Lid,Aid) :- 
  projectsame(Lid,Rid,Aid), 
  not projectdiff(Lid,Rid,Aid).
  
projectsameground(Rid,Lid) :- samelistground(Rid,Lid,Aid). 

% Find a differing one which is not same with anything 
% Truly novel
%reallydiff(Lid,Rid) :-
%  projectdiff(Lid,Rid,Aid),
%  not projectsameground(Rid,Lid). 

% Mod 1 
%goodassign(Lid,Rid) :-  
%  not fsame(Lid,Rid), % XXX
%  not prassigned(Lid), 
%  projectdiff(Lid,Rid,Aid),
%  not badassign(Lid,Rid).

% Do we have two assignments with different values to the same variable name 
badassign(Lid,Rid) :- 
  tstassign(Lid,Rid,Vn,Val1),   
  tstassign(Lid,Rid,Vn,Val2), 
  Val1 != Val2. 

iststassigned(Lid,Rid,Vn) :-   tstassign(Lid,Rid,Vn,Val1). 

badassign(Lid,Rid) :- 
  potential(Rid,Lid), 
  headvarval(Rid,Pn,N,Vn,X1,X2),
  not iststassigned(Lid,Rid,Vn).

% What case does this cover? If this is not here no multiple arguments
goodassign(Lid,Rid) :- 
  % tstassign 		   
  % not prassigned(Lid), 
  visibleassign(Lid,Rid,Vn,Val), 
  not badassign(Lid,Rid). 

% Handle the single body case here; it is always good. 
%goodassign(Lid,Rid) :- 
%  not prassigned(Lid), 
%  tstassign(Lid,Rid,Vn,Val), 
%  bodycount(Rid,1). 


% Each time we create a new 
%2 {
%  nxtassign(@getctr(), Lid, Rid), 
% nxt(@nxtctr(1))
%} 2 :- 
%  % not prassigned(Lid), 
%  visibleassign(Lid,Rid,Vn,Val), 
%  not badassign(Lid,Rid). 
  

% For any good assignment that has been picked from the internal 
% candidates we make a new head. 
9 {   
  hasrule(1,@getctr()), 
  newname(@getctr(),Lid,"JOPI"), 
  newpotfact(@getctr(), Rid), 
  head(@getctr(),@getctr()+1), 
  pos(@getctr()+1), 
  pred(@getctr() + 1, Pn ),
  assigned(Lid,@getctr()), 
  fse2(Lid,Rid,@getctr()), 
  nxt(@nxtctr(N+2))
} 9 :- 
% oink :- % XXX 
  % goodassign(Lid,Rid), % XXX 28. maybe this is not needed 
  pickinternal(Lid,Rid), 
  pickexternal(Lid,Rid), 
  % not projectreallysame(Lid,Rid), % will generate a large amount of answer sets, but cuts also away some valid solutions
  % not banishalid(Lid,Rid), % will stop everything ...
  % not prassigned(Lid), % will stop everything 
  head(Rid,Hid), 
  arity(Hid,N), 
  pred(Hid,Pn). 

pickedandgood(Lid,Rid) :- 
  goodassign(Lid,Rid),
  pickinternal(Lid,Rid).

prassigned(Lid) :- assigned(Lid,New). 

% fsame(Lid,Rid) :- fullsameext(Lid,Rid,New). 

% Once we have assigned one 
% we tag all Lists with same values 
% as assigned as well. 
assigned(Lid2,New) :- 
  assigned(Lid,New),
  fullsameint(Lid,Rid,Lid2). 

% Get the external ones. 
assigned(Lid2,New) :- 
  assigned(Lid1,New),
  fullsameext(Lid1,Rid,New), 
  fullsameext(Lid2,Rid,New).



% An attempt to exclude some alids, may be needed when dealing
% with external conflicts. 
%banishalid(Lid2,Rid) :- 
%  goodassign(Lid1,Rid), 
%  samealids(Lid1,Rid,Vn,Lid2), 
%  not projectdiffalid(Lid1,Rid,Lid2). 

4 { 
  % alist(New+1,N,New+N+A),
  % cnst(New+N+A,Val), % A or N?
  alist(New+1,N,New+1+N),
  cnst(New+1+N,Val), % A or N?
  assert(New),
  arity(New+1,A)
} 4
:- 
  newname(New,Lid,Ignore),    % we have two free IDs after New 
  % goodassign(Lid,Rid),
  pickinternal(Lid,Rid), 
  head(Rid,Hid), 
  arity(Hid,A), 
  % tstassign(Lid,Rid,Vn,Val), 
  visibleassign(Lid,Rid,Vn,Val), 
  alist(Hid,N,Vid), 
  var(Vid,Vn). 

% Now for any good assignment take the stuff 
% that is for headvarvals. 
%  litem(@getctr(), Mapid1, Listid2, N), 
%  nxt(@nxtctr(1))

%  goodassign(Lid,Rid),
%  headvarval(Rid,Pn,Pidx,Vn,X1,X2).

% #hide. 

#show rule/1. 
#show hasrule/2.
#show head/2.
#show pred/2. 
#show assert/1.
#show pos/1.
#show neg/1.
#show arity/2. 
#show alist/3.
#show var/2. 
#show cnst/2. 
#show body/2. 
