% A very simple grounder type of thing

% Make a Lua counter 
#begin_lua
local idctr = 0
local compid = 0
local compids = {}

local lists = {}

-- function nxtctr(inc) 
--  idctr = idctr + inc
--  return idctr
--end 

-- 1750 is still OK
function nxtctr2(inc) 
  if idctr > 1750 then 
     -- return idctr
     -- os.exit()     -- stops the application 
     
     return "Urgh"     

     -- break -- no loop to break
     -- return        -- nope, "got nil
     -- coroutine.yield() -- "ERROR: attempt to yield across metamethod/C-call boundary"
  else 
     idctr = idctr + inc
     return idctr
  end
end 


function nxtctr(inc) 
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

bodyvarpospre(Rid,Vn,Predid,Idx) :- 
  rule(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 

one(1). 

% This produces the same value for nxtctr many times over. 
% map(@nxtctr(One),Rid,Bidx,Jid) :-
busted :- 
  %nxt(X),
  %X < 2048, 
  % nxt(@nxtctr(1)),  % We cant use this as 
  % one(X), 
  % rule(Rid), 
  % onerule(Rid,One), 

  % This seems to be redudant to replicate the body of onerulemap, but it is not 
  onerulemap(Rid,Bidx,Predid,Jid,One), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  assert(Aid), 
  head(Aid,Jid),
  % freectr(Ctr), 
  pred(Jid,Pn).

% Auxiliary to force constants via variables assignments
onerule(Rid,One) :- 
  one(One),
  rule(Rid). 

onerulemap(Rid,Bidx,Predid,Jid,One) :- 
  one(One),
  rule(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn),
  assert(Aid), 
  head(Aid,Jid),
  % freectr(Ctr), 
  pred(Jid,Pn).
  


% Which two maps pertain to same variables on different bodies
%mapsonvar(Rid,Mapid1,Mapid2,Vn) :- 
%  map(Mapid1,Rid,Bidx1,Jid1),
%  map(Mapid2,Rid,Bidx2,Jid2), 
%  Mapid1 != Mapid2, 
%  % Bidx1 != Bidx2, % This seems to kill all?
%  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
%  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2). 

% Next try to deduce which two maps combined 
% give same results for variables. 
%mapsagreeonvar(Rid,Mapid1,Mapid2,Vn, Val1) :- 
%  map(Mapid1,Rid,Bidx1,Jid1),
%  map(Mapid2,Rid,Bidx2,Jid2), 
%  Mapid1 != Mapid2, 
%  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
%  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2), 
%  alist(Jid1,Bpredidx1,Vid1), 
%  cnst(Vid1,Val1), 
%  alist(Jid2,Bpredidx2,Vid2), 
%  cnst(Vid2,Val2), 
%  Val1 == Val2.

% mapsdisagreeonvar(Rid,Mapid1,Mapid2,Vn) :- 
%foo :- % avoid clutter for now 
%  map(Mapid1,Rid,Bidx1,Jid1),
%  map(Mapid2,Rid,Bidx2,Jid2), 
%  Mapid1 != Mapid2, 
%  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
%  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2), 
%  alist(Jid1,Bpredidx1,Vid1), 
%  cnst(Vid1,Val1), 
%  alist(Jid2,Bpredidx2,Vid2), 
%  cnst(Vid2,Val2), 
%  Val1 != Val2.
    
% ----------------------

% litem(id,val,0,nxt)

% id   - ID of this list item 
% val  - points to the contained value 
% nxt  - points to the next list item 
% len  - the length of the list in the tail


litem(@nxtctr(One), Rid, Mapid, 0, 1)  :- 
  % onerulemap(Rid,Bidx,Predid,Jid,One), 
  % one(One), 
  litemmapper(One,Rid,Mapid,N,Predid), 
  map(Mapid,Rid,1,Predid). 

litemmapper(One,Rid,Mapid,N,Predid) :- 
  one(One), 
  map(Mapid,Rid,N,Predid). 



litem(@nxtctr(One), Rid, Mapid, Lid1, N) :- 
  % We have a map item for body position N
  map(Mapid,Rid,N,Predid),
  % We have an existing list for position M ...
  litem(Lid1,Rid,Mapid1, Nxt, M),  
  % ... where M is one less than N
  bodycount(Rid,Maxn), 
  litemmapper(One,Rid,Mapid,Z,Predid), 
  N == M+1, 
  M <= Maxn. 




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

% Try construct list using function symbols

% The first item is the first mapping 
%zlist(1,c(1,Predid,Jid,n)) :- 
%  % onerulemap(Rid,Bidx,Predid,Jid,One). 
%  onerulemap(Rid,1,Predid,Jid,One). 

% Lets create an entry for the max bodylist 
zlist(Rid,1,c(1,Predid,Jid,nil)) :-
  onerulemap(Rid,1,Predid,Jid,One). 

% Recursively grow the list 
zlist(Rid, N+1, c(N+1,Predid,Jid,c(N, Predidold,Jidold,X)) ) :- 
  zlist(Rid, N,c(N,Predidold,Jidold,X)),
  onerulemap(Rid,N+1,Predid,Jid,One),
  bodycount(Rid,Bc), 
  consistentassignments(Rid,N+1,Jid,N,Jidold), 
  % Consistency should check that the predicate names match 
  N < Bc. 

% We keep the whole list in the last argument 
nthinzlist(Rid, c(N, Predid,Jid,X), c(N, Predid,Jid,X) ) :- 
  zlist(Rid, N ,c(N, Predid,Jid,X)),
  bodycount(Rid,N). 

nthinzlist(Rid, c(N-1, Predid,Jid,X), c(Nconst, Predidconst,Jidconst,Xconst) ) :- 
  nthinzlist(Rid, c(N, Predidprev,Jidprev,c(N-1,Predid,Jid,X)), c(Nconst, Predidconst,Jidconst,Xconst) ), 
  N > 0. 

nthinzlist(Rid, N-1, Predid, Jid, c(N, Predidorig, Jidorig, X) ) :- 
  nthinzlist(Rid, N, Predid, Jid, c(N, Predidorig,Jidorig,X) ), 
  zlist(Rid, N, c(N,Predidold,Jidold, c(N-1,Predid,Jid,X) )). 

% For each bodyvarpos, produce a variable assignment.
% In case of conflicting assignments, we get two values for same
% variable, otherwise they are folded to one. 
% zassign(Rid,Vn,Val,c(M,Predidorig,Jidorig,X)) :- 
%zassign(Rid,Vn,Val,c(N,Predid,Jid,X)) :- 
foo :- 
  % bodycount(Rid,Bc), 
  % bodylist(Rid,N,Predid), 
  % zlist(Rid,Bc,c(N,Predid,Jid,X)),
  nthinzlist(Rid, c(N, Predid, Jid, Y), c(M, Predidorig, Jidorig, X) ), 
  % bodyvarpos(Rid,Vn,N,Varpos),
  bodyvarpospre(Rid,Vn,Predid,Varpos),
  alist(Jid,Varpos,Cid),
  cnst(Cid,Val).

zassign(Rid,Predid,Vn,Val, X) :- 
  % Here's the Jid associated with a Predidid,
  nthinzlist(Rid, c(N, Predid, Jid, Y), X ),
  % We need the variables bound by Predid. 
  bodyvarpospre(Rid,Vn,Predid,Pos),
  % We need to get the value from Jid
  alist(Jid,Pos,Cid),
  cnst(Cid,Val).

visiblezassign(Rid,Vn,Val,X) :- 
  zassign(Rid,Predid,Vn,Val, X), 
  headvarval(Rid,Pn,Bidx,Vn,A,B). 

diffzassign(X1,X2) :- 
  visiblezassign(Rid,Vn,Val1,X1),
  visiblezassign(Rid,Vn,Val2,X2),
  Val1 != Val2. 

samezassign(X1,X2) :- 
  visiblezassign(Rid,Vn1,Val1,X1), 
  visiblezassign(Rid,Vn2,Val2,X2), 
  % X1 != X2, 
  not diffzassign(X1,X2). 

inconsistentzlist(Rid,X) :- 
  zassign(Rid,Predid1,Vn,Val1,X), 
  zassign(Rid,Predid2,Vn,Val2,X),
  Val1 != Val2. 

consistentzlist(Rid,X) :- 
  not inconsistentzlist(Rid, X), 
  bodycount(Rid,Len), 
  zlist(Rid,Len,X).

% Next check whether the two lists have the same external values 

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

%%assignat(Lid,Rid,Bpredidx,Vn,Val) :- 
%%  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
%%  bodyvarpos(Rid,Vn,N,Bpredidx), 
%%  alist(Jid,Bpredidx,Cid), 
%%  cnst(Cid,Val).

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

%% onediffext(Lid,Rid,Jid,N) :- 
fulldiffext(Lid,Rid,Jid) :- 
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
%%fulldiffext(Lid,Rid,Jid) :- 
%%  onediffext(Lid,Rid,Jid,N).


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
%% onediffint(Lid1,Rid,Lid2,N) :- 
fulldiffint(Lid1,Rid,Lid2) :- 
  assign(Lid1,Rid,N,Val1), 
  assign(Lid2,Rid,N,Val2), 
  Lid1 != Lid2, 
  Val1 != Val2. 

onesameint(Lid1,Rid,Lid2,N) :- 
  assign(Lid1,Rid,N,Val1), 
  assign(Lid2,Rid,N,Val2), 
  Lid1 != Lid2, 
  Val1 == Val2. 

%%fulldiffint(Lid1,Rid,Lid2) :- 
%%  onediffint(Lid1,Rid,Lid2,N).

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

% Why would this be needed at all?
%justified(Lid1,Lid1) :- 
%  onesameint(Lid1,Rid,Lid2,N1),
%  goodassign(Lid1,Rid). 

justified(Lid1,Lid2) :- 
  onesameint(Lid1,Rid,Lid2,N1),
  goodassign(Lid2,Rid). 



% For cases with one argument
% This seems to be precisely as the general case...
% However since there is only one of these, we at the 
% same time pick the internal one. 
%2 {
%  fullsameint(Lid,Rid,Jid), 
%  pickinternal(Lid,Rid) 
%} 2 :- 
fullsameint(Lid,Rid,Jid) :- 
  head(Rid,Hid), 
  arity(Hid,1), 
  onesameint(Lid,Rid,Jid,N),
  Lid < Jid.

% Why is this used?
% Having this removed doubles the execution time!
pickinternal(Lid,Rid) :- 
  fullsameint(Lid,Rid,Jid), 
  head(Rid,Hid), 
  arity(Hid,1), 
  onesameint(Lid,Rid,Jid,N),
  Lid < Jid.




% Make a closure of fullsameint's 
% We tag those which are not the 'smallest'
% XXX Shouldn't this be fullsameint rather than 
% onesameint?
%2 {
%fullsameint(Lid1,Rid,Lid3),
%subcluster(Lid2,Rid)
%} 2 :- 
subcluster(Lid2,Rid) :- 
  fullsameint(Lid1,Rid,Lid2), 
  fullsameint(Lid2,Rid,Lid3), 

  Lid1 < Lid3,
  % goodassign(Lid1,Rid),    % XXX
  not fulldiffint(Lid1,Rid,Lid3),
  not fullsameint(Lid3,Rid,Lid1).
  %not fullsameint(Lid3,Rid,Tmp),
  %nxt(Tmp).

fullsameint(Lid1,Rid,Lid3) :- 
  subcluster(Lid2,Rid), 
  fullsameint(Lid1,Rid,Lid2), 
  fullsameint(Lid2,Rid,Lid3), 
  Lid1 < Lid3,
  not fulldiffint(Lid1,Rid,Lid3),
  not fullsameint(Lid3,Rid,Lid1).



% We assume that the closure has been constructed. 
% We have one 'main' cluster, which has more than one
% Lid1s. It could only have been constructed transitively 
% so it is identified as the source of the closure.
% The first term of fullsameint/3 is the key or identity of
% the cluster and all but the 'main' cluster have been 
% tagged with subcluster/2 by comparison. 

pickinternal(Lid1,Rid) :- 
  fullsameint(Lid1,Rid,Lid2),     % The 'main' cluster, identified by Lid1
  not subcluster(Lid1,Rid),
  % justified(Lid1,Lid),            % There must be a justified/2 tagged entry associated with Lid1
  fullsameint(Lid2,Rid,Lid3).

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

visibleassign(Lid,Rid,Vn,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  headvarval(Rid,Pn,N,Vn,Bidx,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

% Sameassign
% samealids(Lid1,Rid,Lid2,N) :- 
%samealids(Lid1,Rid,Vn,Lid2) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
%  visibleassign(Lid1,Rid,Vn,Val1),   
%  visibleassign(Lid2,Rid,Vn,Val2),
%  Lid1 != Lid2,
%  Val1 = Val2. 

%diffalids(Lid1,Rid,Vn,Lid2) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
%  visibleassign(Lid1,Rid,Vn,Val1),   
%  visibleassign(Lid2,Rid,Vn,Val2),
%  Lid1 != Lid2,
%  Val1 != Val2. 

% projectdiffalid(Lid1,Rid,Lid2) :- diffalids(Lid1,Rid,Vn,Lid2).


% Is there an assignment to position N 
% of Rid in ground predicate Aid. 
%sameassign(Lid,Rid,Aid,N) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
%  visibleassign(Lid,Rid,Vn,Val1),   
%  head(Rid,Hid1), 
%  alist(Hid1,N,Vid1), 
%  var(Vid1,Vn), 
%  arity(Hid1,A1), 
%  pred(Hid1,Pn), 
  % Now compare to existing facts 
%  assert(Aid), 
%  head(Aid,Hid2), 
  % Same predicate name with same Value at the same place
%  pred(Hid2,Pn), 
%  alist(Hid2,N,Cid1),
%  cnst(Cid1,Val1). 

% Negation of sameassign/4
% Meaning that at least one argument is different, so at least 
% one argument of Aid is incomaptible with Lid. 
%diffassign(Lid,Rid,Aid,N) :- 
  % Get the index of the argument number 
  % for the new candidate:
  % predicate Pn has value Val1 at position N.
  % tstassign(Lid,Rid,Vn,Val1),   
%  visibleassign(Lid,Rid,Vn,Val1),   
%  head(Rid,Hid1), 
%  alist(Hid1,N,Vid1), 
%  var(Vid1,Vn), 
%  arity(Hid1,A1), 
%  pred(Hid1,Pn), 
%  % Now compare to existing facts 
%  assert(Aid), 
%  head(Aid,Hid2), 
  % Same predicate name with different Value at the same place
%  pred(Hid2,Pn), 
%  alist(Hid2,N,Cid1),
%  cnst(Cid1,Val2),
%  Val1 != Val2. 

% This enumerates those ground predicates 
% which may be pertinent for this List of assignments. 
%feasibleground(Lid,Rid,Aid) :- 
%  visibleassign(Lid,Rid,Vn,Val), 
%  head(Rid,Predid),
%  pred(Predid,Pn), 
%  % There is an assertion with same predicatename
%  assert(Aid),
%  head(Aid,Justid),
%  pred(Justid,Pn).


% Something is really same, if there are no diffassign/4 
% associated with it, but there is a sameassign. 
%reallysame(Lid,Rid,Aid) :- 
%  sameassign(Lid,Rid,Aid,N1), 
%  head(Aid,Predid),
%  alist(Predid,N2,Cid), 
%  not diffassign(Lid,Rid,Aid,N2), 
%  % And the assertion has not been produced by this lid
%  not assigned(Lid,Aid).

% projectreallysame(Lid,Rid) :- reallysame(Lid,Rid,Aid).


%reallydiff(Lid,Rid,Aid) :- 
%  projectdiff(Lid,Rid,Aid),
%  not projectreallysame(Lid,Rid). 


%projectsame(Lid,Rid,Aid) :- sameassign(Lid,Rid,Aid,N). 

% If there is a single projectdiff, then they are different 
%projectdiff(Lid,Rid,Aid) :- diffassign(Lid,Rid,Aid,N). 

% All arguments are same and there is no single 
% differing argument. So Lid and Aid are the same. 
%samelistground(Rid,Lid,Aid) :- 
%  projectsame(Lid,Rid,Aid), 
%  not projectdiff(Lid,Rid,Aid).
  
% projectsameground(Rid,Lid) :- samelistground(Rid,Lid,Aid). 


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


% newpotfact(@nxtctr(N+2), Rid, Lid, Pn) :- 
% 2 {newpotfact(@nxtctr(N+3), Rid, Pn, c(Idx,Predid,Jid,X)), assigned(c(Idx,Predid,Jid,X)) } 2 :- 
2 {newpotfact(@nxtctr(N+3), Rid, Pn, c(Idx,Predid,Jid,X)), assigned(c(Idx,Predid,Jid,X)) } 2 :- 
  consistentzlist(Rid, c(Idx,Predid,Jid,X)), 
  % Now pick a representative among the zlists which are the same
  pickzassign(c(Idx,Predid,Jid,X)), 
  evaluable(Rid), 
  head(Rid,Hid), 
  arity(Hid,N), 
  pred(Hid,Pn). 

assigned(X) :- 
  assigned(Y), 
  samezassign(Y,X).

pickzassign(c(Idx,Predid1,Jid1,X1)) :- 
  samezassign(c(Idx,Predid1,Jid1,X1),c(Idx,Predid2,Jid2,X2)),
  Jid1 < Jid2. 


hasrule(1,NF) :- 
  newpotfact(NF, Rid, Pn, X). 

pos(NF+1) :- 
  newpotfact(NF, Rid, Pn, X). 

newname(NF,"JOPI") :- 
  newpotfact(NF, Rid, Pn, X). 

head(NF,NF+1) :- 
  newpotfact(NF, Rid, Pn, X). 

pred(NF + 1, Pn ) :- 
  newpotfact(NF, Rid, Pn, X). 

%assigned(NF) :- 
%  newpotfact(NF, Rid, Pn, X). 

%assert(NF) :- 
%  newpotfact(NF, Rid, Pn, X). 

pickedandgood(Lid,Rid) :- 
  goodassign(Lid,Rid),
  pickinternal(Lid,Rid).

%% prassigned(Lid) :- assigned(Lid,New). 

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

lsttmp(NF,N,Val,A, Rid) :- 
  newpotfact(NF, Rid, Pn, X),
  head(Rid,Hid), 
  arity(Hid,A), 
  visiblezassign(Rid,Vn,Val,X), 
  alist(Hid,N,Vid), 
  var(Vid,Vn). 

alist(NF+1,N,NF+1+N) :- 
  lsttmp(NF,N,Val,A,Rid).

cnst(NF+1+N,Val) :- 
  lsttmp(NF,N,Val,A, Rid).

arity(NF+1,A) :- 
  lsttmp(NF,N,Val,A, Rid).

assert(NF) :- 
  lsttmp(NF,N,Val,A, Rid).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% Trial here generated rule-specific rules which 
% tie together the skeleton of the reified rules. 
% This is a bit of a cop out, though, we generate 
% another version of the same rule. 
%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% The variable 'Vn' in the head
% of rule 'Rid' is in predicate 'Pn'
% at position 'Idx'.
% It is assigned by body 'Bidx' in 
% position 'Bpredidx'.
%
% No mention of the predicate providing the variable. 
% E.g. 
% headvarval(2,"node",1,"X",1,1).
% headvarval(8,"reach",2,"Z",2,2).
% headvarval(8,"reach",1,"X",1,1).
%
headvarval(Rid,Pn,Idx,Vn,Bidx,Bpredidx) :- 
  rule(Rid), 
  head(Rid,Pid),
  pred(Pid,Pn), 
  alist(Pid,Idx,Vid), 
  var(Vid,Vn),
  bodyvarpos(Rid,Vn,Bidx,Bpredidx).

%rulevarval(Rid,Vn,Bidx,Bpredidx) :- 
%  rule(Rid), 
%  bodyvarpos(Rid,Vn,Bidx,Bpredidx).
  
  

%
% Variable 'Vn' in rule 'Rid' is assigned
% by body index 'Bidx' in position 'Idx'.
%
% bodyvarpos(8,"Y",1,2).
% bodyvarpos(8,"X",1,1).
% bodyvarpos(8,"Z",2,2).
% bodyvarpos(8,"Y",2,1).
% bodyvarpos(2,"Y",1,2).
% bodyvarpos(2,"X",1,1).
%
bodyvarpos(Rid,Vn,Bidx,Idx) :- 
  rule(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 

mapsagreeonvar(Rid,Predid1,Jid1,Predid2,Jid2,Vn,Val1) :- 
  onerulemap(Rid, Bidx1, Predid1, Jid1, One1),
  onerulemap(Rid, Bidx2, Predid2, Jid2, One2),
  Predid1 != Predid2, 
  % 
  headvarval(Rid,Pn,Idx,Vn,Bidx1,Bpredidx1), 
  headvarval(Rid,Pn,Idx,Vn,Bidx2,Bpredidx2), 
  alist(Jid1,Bpredidx1,Vid1), 
  cnst(Vid1,Val1), 
  alist(Jid2,Bpredidx2,Vid2), 
  cnst(Vid2,Val2), 
  Val1 == Val2.

consistentassignments(Rid,Bidx1,Jid1,Bidx2,Jid2) :- 
  bodyvarpos(Rid,Vn,Bidx1,Pos1),
  bodyvarpos(Rid,Vn,Bidx2,Pos2),
  Bidx1 != Bidx2,
  % Now any two mappings must match for values on Bidx1/Pos1 Bidx2/Pos2
  % Here we get two mappings for these Bidx's 
  onerulemap(Rid, Bidx1, Predid1, Jid1, One1),
  onerulemap(Rid, Bidx2, Predid2, Jid2, One2),
  % Now we need to get the corresponding positions from the ground fact 
  alist(Jid1,Pos1,Vid1),
  cnst(Vid1,Val1), 
  alist(Jid2,Pos2,Vid2),
  cnst(Vid2,Val2),
  Val1 == Val2. 

% Agree on variables in the head
% Target: chunga(Rid,Vn,Val1,Predid1,Jid1,Val2,Predid2,Jid2) :- 
% XXX not used yet 
headconsistentvariable(Rid,Vn,Val1,Jid1,Predid1,Val2,Predid2,Jid2) :- 
  onerulemap(Rid, Bidx1, Predid1, Jid1, One1),
  onerulemap(Rid, Bidx2, Predid2, Jid2, One2),
  Predid1 != Predid2, 
  % Agree on all variables in the head
  headvarval(Rid,Pn,Idx1,Vn,Bidx1,Bpredidx1), 
  % headvarval(Rid,Pn,Idx2,Vn,Bidx2,Bpredidx2),    % XXXX This may be bad news 
  alist(Jid1,Bpredidx1,Vid1),
  cnst(Vid1,Val1), 
  alist(Jid2,Bpredidx2,Vid2),
  cnst(Vid2,Val2),
  Val1 == Val2.

% A rule has a body which is negated
nonevaluable(Rid,Bid) :- 
  body(Rid,Bid), 
  neg(Bid). 

% A rule refers to a nonevaluable rule 
nonevaluable(Rid1,Bid1) :- 
  body(Rid1,Bid1), 
  pred(Bid1,Pn), 
  rule(Rid2), 
  head(Rid2,Hid2),
  pred(Hid2,Pn), 
  nonevaluable(Rid2,Bid2).

prnonevaluable(Rid) :- nonevaluable(Rid,Bid). 

evaluable(Rid) :- 
  body(Rid,Bid), 
  not prnonevaluable(Rid). 

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
