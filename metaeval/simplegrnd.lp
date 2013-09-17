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

zpredlst(Rid, X, Pn, v(1,Val,nil) ) :- 
  visiblezassign(Rid,Vn,Val,X),
  bodyvarpospre(Rid,Vn,Predid,1),
  head(Rid,Hid),
  pred(Hid,Pn). 
  % pred(Predid,Pn).

%
% zpredlst(8,c(2,12,27,c(1,15,31,nil)),"edge",v(2,"1",v(1,"1",nil))).
%              ^                                ^
% If these two are equal to bodycount(Rid,N) then this is valid
%
zpredlst(Rid, Z, Pn, v(N+1,Val,v(N,Valold,X)) ) :- 
  zpredlst(Rid, Z, Pn, v(N,Valold,X) ), 
  visiblezassign(Rid,Vn,Val,Z),
  bodyvarpospre(Rid,Vn,Predid,N+1), 
  % pred(Predid,Pn).
  head(Rid,Hid),
  pred(Hid,Pn). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% We construct a list from assertions,
% starting with the first element. 
apredlst(Aid,Pn,v(1,Val,nil)) :- 
  assert(Aid), 
  head(Aid,Hid), 
  pred(Hid,Pn), 
  alist(Hid,1,Cid),
  cnst(Cid,Val). 

% We grown the list built on other lists 
% ... problem may be here, we may link  ZZZ
% the old list to the current list rather than 
% recombining two lists. 
apredlst(Aid,Pn,v(N+1,Val,v(N,Valold,X))) :- 
  apredlst(Aid,Pn,v(N,Valold,X)), 
  assert(Aid), 
  head(Aid,Hid), 
  pred(Hid,Pn), 
  alist(Hid,N+1,Cid),
  cnst(Cid,Val). 

% Base case, the highest number  
nthinapredlst(Aid, Pn, N, v(N,Val,X) , v(N,Val,X) ) :- 
  apredlst(Aid,Pn,v(N,Val,X)), 
  head(Aid,Hid),
  arity(Hid,N).

nthinapredlst(Aid, Pn, N-1, v(N-1,Val2,Y), v(M,Valold,X) ) :- 
  nthinapredlst(Aid, Pn, N, v(N,Val1,v(N-1,Val2,Y)), v(M,Valold,X) ), 
  N - 1 > 0. 


% Associate bodypredicates with id Predid and name Pn 
% with apredlst, which has the same Pn. 
lmap(Rid,Predid,v(N,Val1,X)) :- 
  apredlst(Aid,Pn,v(N,Val1,X)), 
  bodylist(Rid,I,Predid),
  pred(Predid,Pn),
  arity(Predid,N).

% We assign a variable Vn with Val at bodyitem 
% predid. This comes from a single lmap and hence
% single apredlst. 
xassign(Rid,Predid,Vn,Val, v(N,Val1,Rest)) :- 
  % The assignment list from a ground predicate 
  lmap(Rid,Predid,v(N,Val1,Rest)), 
  % We need the variables bound by Predid. 
  bodyvarpospre(Rid,Vn,Predid,Pos),
  % We need to get the value at position Pos and it is 
  % coming from some ground fact Aid
  nthinapredlst(Aid,Pn,Pos, v(Pos,Val,X), v(N,Val1,Rest)).


xconflict(Rid,Vn, Val1, Predid1, Val2, Predid2, X1, X2) :- 
  xassign(Rid,Predid1,Vn,Val1, X1),
  xassign(Rid,Predid2,Vn,Val2, X2),
  Val1 != Val2. 

% Conflicting is always relative
xconflicting(Rid,X1,X2) :- xconflict(Rid,Vn, Val1, Predid1, Val2, Predid2, X1, X2).

% Something wrong with this below 
%xcompatible(Rid,Vn, Val1, X1, X2) :- 
%  xassign(Rid,Predid1,Vn,Val1, X1),
%  xassign(Rid,Predid2,Vn,Val2, X2),
%  X1 != X2,
%  Val1 == Val2. 

visiblexassign(Rid,Vn,Val,X) :- 
  xassign(Rid,Predid,Vn,Val, X), 
  % not xconflicting(Rid,X), 
  headvarval(Rid,Pn,Bidx,Vn,A,B). 

diffxassign(X1,X2) :- 
  visiblexassign(Rid,Vn,Val1,X1),
  visiblexassign(Rid,Vn,Val2,X2),
  Val1 != Val2. 

samexassign(X1,X2) :- 
  visiblexassign(Rid,Vn,Val1,X1),
  visiblexassign(Rid,Vn,Val2,X2),
  % X1 != X2, 
  not diffzassign(X1,X2). 

inconsistentxlist(Rid,X) :- 
  xassign(Rid,Predid1,Vn,Val1,X), 
  xassign(Rid,Predid2,Vn,Val2,X),
  Val1 != Val2. 

%consistentxlist(Rid,X) :- 
%  not inconsistentxlist(Rid, X), 
%  bodycount(Rid,Len), 
%  zlist(Rid,Len,X).

% Now we need to tag one assigned xassign 
% as a selection.   


% And now form visiblexassign's we collect a new list for the head
% with predicate name Pn. 
% This list has index and value Val 
% 
% We start with the first item. 
% We may have to carry the source list with us and then later 
% project it away. 
% Actually we may not need to do that, but we may need 
% to check that the lists used are compatible. 
vlist(Rid,Pn,v(1, Val, nil), X ) :- 
  visiblexassign(Rid,Vn,Val,X),
  % We need the variables bound by Predid. 
  bodyvarpospre(Rid,Vn,Predid,Pos), 
  Pos == 1, 
  head(Rid,Hid),
  pred(Hid,Pn).

% Build iteratively 
vlist(Rid,Pn,v(N+1, Valnew, v(N, Val, Rest) ), X) :- 
  vlist(Rid,Pn,v(N, Val, Rest), X ), 
  visiblexassign(Rid,Vn,Valnew,X),
  bodyvarpospre(Rid,Vn,Predid,N+1), 
  head(Rid,Hid),
  pred(Hid,Pn).

% We combine 'visibleassign/' which relates a variable name (occurring in the head)
% to a value with other visibleassign/
% Structure is as follows:
% Rid			ruleid
% Pn			name of the predicate 
% z(Idx,Vn,Val,Predid,Just,Rest) where 
% Idx 		        index of the list position; this is also the position of the variable in the head
% Vn			name of the variable 
% Val 			value of the variable 
% Predid		the ID of the predicate in the body of Rid
% X                     the assignment list which produced this assignment,
%                       maybe needed when the conflicts are resolved
% nil                   marker for the rest of the v() list.
%
% Example of list length 1, the initial list: 
% 
% vlist2(8,"reach",z(1,"X","2",15,v(2,"1",v(1,"2",nil)),nil)).
%
vlist2(Rid,Pn,z(1, Vn, Val, Predid, X, nil) ) :- 
  visiblexassign(Rid,Vn,Val,X),
  % We need the variables bound by Predid. 
  bodyvarpospre(Rid,Vn,Predid,Pos), 
  Pos == 1, 
  head(Rid,Hid),
  pred(Hid,Pn).

% Build a list iteratively based on the earlier indexes
%
% Structure is as follows:
% Rid			ruleid
% Pn			name of the predicate 
% z(N+1, Vnnew, Valnew, Predidnew, X, z(N, Vnold, Valold, Predidold, L, Rest) )
% N+1 		        index of the new list position
% Vnnew			name of the variable at this position 
% Valnew		value of the variable 
% Predidnew		the ID of the predicate in the body of Rid
% X                     the assignment list which produced this assignment,
%                       maybe needed when the conflicts are resolved
% 
% The nested z() is the rest of the list, the previous entry based on which 
% we build the new step
% z(N, Vnold, Valold, Predidold, L, Rest)
% N 		        index of the previous list item, must be one smaller than the new one
% Vnold			name of the variable at this position 
% Valold		value of the variable 
% Predidold 		the ID of the predicate in the body of Rid
% L                     the assignment list which produced this assignment,
% Rest                  other nested v() lists, may be a nil
%
% Example of list length 2
% vlist2(8,"reach",z(2,"Z","2",12,v(2,"2",v(1,"1",nil)),z(1,"X","1",15,v(2,"2",v(1,"1",nil)),nil))).
%
% Some notes: 
% 1. By construction the Predid is unique to the list and actually specifies the index as
%    well. 
% 2. The length of this vlist2 is determined by the number of bodies in the rule Rid. 
% 3. Two similar variable valuations could come from different assignment lists; the assignmnt 
%    lists are actually argument lists of ground predicates which are associated with the predid. 
% 4. The result may still be conflicting. By this construction two consecutive list items 
%    must have compatible valuation, but the compatibility does not extend through all variable 
%    valuations; it may be possible to obtain a list with two different values for the same 
%    variable name. 
% 5. The assignment list from the ground predicate carries essentially the provenence information. 
%
vlist2(Rid,Pn,z(N+1, Vnnew, Valnew, Predidnew, X, z(N, Vnold, Valold, Predidold, L, Rest) ) ) :- 
  vlist2(Rid,Pn,z(N, Vnold, Valold, Predidold, L, Rest) ), 
  visiblexassign(Rid,Vnnew,Valnew,X),
  bodyvarpospre(Rid,Vnnew,Predidnew,N+1), 
  head(Rid,Hid),
  pred(Hid,Pn), 
  % Now make sure that both lists are mutually compatible 
  not xconflict(Rid,Vnnew, Valnew, Predidnew, Predidold, X, L). 
  %xcompatible(Rid,Vnnew,Valnew, X, L), 
  %xcompatible(Rid,Vnold,Valold, L, X). 





% And finally, project to apredlst
%apredlst(Rid,Pn,L) :- 
%  vlist(Rid,Pn, L, Y ). 

%
% We need to convert apredlst to vlist2, the forms are like 
% 
% apredlst(48,"edge",v(2,"1",v(1,"2",nil))).
% vlist2(8,"reach",v(2,"Z","2",12,v(2,"2",v(1,"1",nil)),v(1,"X","2",15,v(2,"1",v(1,"2",nil)),nil))).
%

% Item accessors for vlist2, this is the starting point of the 'iteration', the largest 
% list item. 
% 
% Rid			ruleid
% Pn			name of the predicate 
% N                     The index of the following values in the list at indicated position 
% Vn			name of the variable for this list item  
% Val 			value of the variable for this list item  
% Predid		the ID of the predicate in the body of Rid for this list item  
% SrcL                  the vlist which produced this entry 
% z(N, Vn, Val, Predid, SrcL, z(N-1, Vnnxt, Valnxt, Predidnxt,SrcLnxt,Rest)) is the copy of the full list. 
%                       with the next item unfolded. 
% N                     The index of the last item of the list, i.e the one with 
%                       the largest bodyindex in the rule Rid. 
% Vn, Val, Predid, SrcL as above
% N-1                   The index of the next step, we need to carry this information as cursor
%                       to the next step. 
% Vnnxt, Valnxt, Predidnxt, SrcLnxt as above
% Rest                  Rest of the list unfolded
% 
% Example:
% nthinvlist2(8,"reach",1,"X","2",15,v(2,"3",v(1,"2",nil)),z(2,"Z","2",12,v(2,"2",v(1,"1",nil)),z(2,"X","2",15,v(2,"3",v(1,"2",nil)),nil))). 
% 
nthinvlist2(Rid, Pn, N, Vn, Val, Predid, SrcL, 
	    z(N-1, Vnnxt, Valnxt, Predidnxt,SrcLnxt,Rest), z(N, Vn, Val, Predid, SrcL, z(N-1, Vnnxt, Valnxt, Predidnxt,SrcLnxt,Rest) ) ) 
:- 
  vlist2(Rid, Pn, z(N, Vn, Val, Predid, SrcL, z(N-1, Vnnxt, Valnxt, Predidnxt,SrcLnxt,Rest))),
  bodycount(Rid,N). 

% Here we do the next step, using the previous item as base 
nthinvlist2(Rid, Pn, N-1, Vn, Val, Predid, SrcL, Rest, Orig )
:- 
  nthinvlist2(Rid, Pn, N, Vnold, Valold, Predidold, SrcLold, z(N-1, Vn, Val, Predid,SrcL,Rest), Orig),
  N > 0. 

% Finally, we need to handle the case of lists of length one 
nthinvlist2(Rid, Pn, 1, Vn, Val, Predid, SrcL, 
	    nil, z(1, Vn, Val, Predid, SrcL, nil ) ) 
:- 
  vlist2(Rid, Pn, z(1, Vn, Val, Predid, SrcL, nil )),
  bodycount(Rid,1). 



% Here we search for two consecutive versions of the same list 
%samenthvlist2(Rid,N,M, X,Y) :- 
%  nthinvlist2(Rid, Pn, N, Vn, Val, Predid, SrcL, Cursor1, X), 
%  nthinvlist2(Rid, Pn, M, Vn2, Val2, Predid2, SrcL2, Cursor2, Y),
%  N != M, 
%  X == Y.

%
% Now construct vlist3, which removes extra stuff from vlist2, so that
% we can regenerate apredlst.
%
% vlist3(Rid,Pn,v(N,Val,v(N-1,Val,nil)), L)
% Rid			ruleid
% Pn			name of the predicate 
% v(N,Val,v(N-1,Val,nil))  a nested list 
% L                     The source of this valuation, which we use to 
%                       glue two items of vlist2

% The first item 
vlist3(Rid,Pn,v(1,Val,nil), L) :- 
  nthinvlist2(Rid,Pn,1,Vn,Val,Predid,GroundL,Item,L). 

%vlist3(Rid,Pn, v(N,Val,v(N-1,Valprev,Rest)) ,L) :- 
%  vlist3(Rid,Pn,v(N-1,Valprev,Rest), L), 
%  nthinvlist2(Rid,Pn,N,Vn,Val,Predid,L1,L). 

vlist3(Rid,Pn,v(N+1,Val,v(N,Prevval,Rest)), L) :- 
  % Get the previous value for this list 
  vlist3(Rid,Pn,v(N,Prevval,Rest),L),
  % Get the current values for this list 
  nthinvlist2(Rid,Pn,N+1,Vn,Val,Predid,GroundL,Item,L). 

% Next project vlist3 to apredlst to be available 
% as a ground fact. 
% This also removes duplicate value assignments. 
apredlst(Rid,Pn,L) :- 
  vlist3(Rid,Pn, L, Y ). 

% And if the rule is evaluable, we project it to ground rule,
% we could also mkassign it, perhaps to reuse old code of the dereifier
% ... but we still continue with the abstract plan so that we dont have 
% to take into account duplicate removal. 
groundrule(Pn,v(N,Val,Rest)) :- 
  apredlst(Rid,Pn,v(N,Val,Rest)),
  head(Rid,Hid),
  arity(Hid,N), 
  evaluable(Rid). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Duplicate of what? XXX
duplicate(Rid,Y) :- 
  apredlst(Aid,Pn, v(N,Valold,X) ),
  zpredlst(Rid, Y, Pn, v(N,Valold,X) ),
  bodycount(Rid,N). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


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
% 2 {newpotfact(@nxtctr(N+3), Rid, Pn, c(Idx,Predid,Jid,X)), assigned(c(Idx,Predid,Jid,X)) } 2 :- 
boogol :- 
  consistentzlist(Rid, c(Idx,Predid,Jid,X)), 
  % Now pick a representative among the zlists which are the same
  pickzassign(c(Idx,Predid,Jid,X)), 
  not duplicate(Rid,X), 
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
