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
2 { 
  litem(@getctr(), Mapid, 0, 1), 
  % lst(@mklist(@getctr(),1)), 
  nxt(@nxtctr(1))
} 2 :- 
  map(Mapid,Rid,N,Predid). 

% Make each mapitem into a list of length one. 
%2 { 
%  litem2(@getctr(), @getctr(), Mapid, 0, 1), 
%  % lst(@mklist(@getctr(),1)), 
%  nxt(@nxtctr(1))
%} 2 :- 
%  map(Mapid,Rid,N,Predid). 


%blargisinlist(Listid,Listid,Mapid) :- 
%  litem(Listid,Mapid,_,_).

%isinlist(Parentid,Listid,Mapid) :- 
%  litem(Listid,Mapid,Next,_),
%  Next != 0, 
%  isinlist(Parentid,Next,Mapid). 

%2 { lc2(Listid, Mapid1), lc2(Listid, Mapid2) } 2  :- 
% chunga :- 
lc2(Listid,Mapid1) :- 
  litem(Listid,Mapid1,Nxt,Len), 
  litem(Nxt,Mapid2,Nxt2,Len2). 

lc2(Listid,Mapid2) :- 
  litem(Listid,Mapid1,Nxt,Len), 
  litem(Nxt,Mapid2,Nxt2,Len2). 

lc2(Listid,Mapid2) :- 
  lc2(Listid,Mapid1), 
  litem(Listid2, Mapid1, Nxt, Len), 
  litem(Nxt, Mapid2, Nxt2, Len). 

isinlist(L,M) :- lc2(L,M). 
% This is for lists of length 1, singletons 
isinlist(L,M) :- litem(L, M, 0, 1).

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
  litem(Listid,Mapid,Next,N). 


% Now for any two singleton map(list)s put them to another list 
2 { 
  litem(@getctr(), Mapid1, Listid2, 2), 
  nxt(@nxtctr(1))
} 2 :- 
  % Three next lines are generic
  litem(Listid1,Mapid1,0,1),
  litem(Listid2,Mapid2,0,1),
  Mapid1 != Mapid2. 

% We keep growing the lists, for any list of N-1,
% we recombine it to a list of N. 
% What if no N-1 available. 
2 { 
  litem(@getctr(), Mapid1, Listid2, N), 
  nxt(@nxtctr(1))
} 2 :- 
  % Three next lines are generic
  litem(Listid1,Mapid1,0,1),
  litem(Listid2,Mapid2,Nxt2,N-1),
  % Mapid1 != Mapid2, 
  not isinlist(Listid2,Mapid1),
  % Now we make some constraints about the list 
  bodycount(Rid,N),       % only up to N 
  map(Mapid1,Rid,N1,_),   % must have same RID, maybe diferent N1,N2
  map(Mapid2,Rid,N2,_). 

% We should be able to grow, or shrink, generate list items for N > 1 up to 
% N. This would be kind of like starting a recursion up or down. 

% Each inlist/4 of length bodycount/2 should now be evaluated 
% to produce an OK wrt. the rules and produced variables. 
% Potentials are those lists that have the same length
% as indicated by bodycount. 
potential(Rid,Lid) :- 
  bodycount(Rid,N), 
  litem(Lid,Mapid,Nxt,N). 



% Now we assign the N'th bodypredicate of Rid according to Lid
mkassign(Lid,Rid,Predid,Mapid,Jid,N) :- 
  potential(Rid,Lid), 
  bodylist(Rid,N,Predid), 
  % There is a mapid in this list 
  isinlist(Lid,Mapid),
  litem(Lid2,Mapid,Nxt,N), % now the index is matched to bodylist ...
  % Which pertains to this N'th bodypredicate 
  map(Mapid, Rid, N, Jid). 

tstassign(Lid,Rid,Vn,Val) :- 
  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
  bodyvarpos(Rid,Vn,N,Bpredidx), 
  alist(Jid,Bpredidx,Cid), 
  cnst(Cid,Val).

badassign(Lid,Rid) :- 
  tstassign(Lid,Rid,Vn,Val1),   
  tstassign(Lid,Rid,Vn,Val2), 
  Val1 != Val2. 

iststassigned(Lid,Rid,Vn) :-   tstassign(Lid,Rid,Vn,Val1). 

badassign(Lid,Rid) :- 
  potential(Rid,Lid), 
  headvarval(Rid,Pn,N,Vn,X1,X2),
  not iststassigned(Lid,Rid,Vn).

goodassign(Lid,Rid) :- 
  tstassign(Lid,Rid,Vn,Val), 
  not badassign(Lid,Rid). 

% Handle the single body case here; it is always good. 
goodassign(Lid,Rid) :- 
  tstassign(Lid,Rid,Vn,Val), 
  bodycount(Rid,1). 

% For any good assignment we make a new head
7 {   
  hasrule(1,@getctr()), 
  newname(@getctr(),Lid,"JOPI"), 
  newpotfact(@getctr(), Rid), 
  head(@getctr(),@getctr()+1), 
  pos(@getctr()+1), 
  pred(@getctr() + 1, Pn ),
  nxt(@nxtctr(N+2))
} 7 :- 
  goodassign(Lid,Rid),
  head(Rid,Hid), 
  arity(Hid,N), 
  pred(Hid,Pn). 

4 { 
  alist(New+1,N,New+1+A),
  cnst(New+1+A,Val), % A or N?
  assert(New),
  arity(New+1,A)
} 4
:- 
  newname(New,Lid,Ignore), 
  goodassign(Lid,Rid),
  head(Rid,Hid), 
  arity(Hid,A), 
  tstassign(Lid,Rid,Vn,Val), 
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
