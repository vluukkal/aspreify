% 
% simplegrnd.lp 
%
% A no longer very simple grounder for reified answer set programs. 
% 
% Copyright 2013 Vesa Luukkala
% 


% Set the counter properly, but it seems we 
% need to have this _lexicographically_ before the 
% points of use in the file, for this to work. Ugh. 
% freectr(@setctr(C)) :- freectr(C).

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

% These are particular to the typed lists or parametrized 
% conjucntions. 
tvarpos(Compid,Vn,Bidx,Idx) :- 
  composite(Compid), 
  tlist(Compid,Bidx,Qid),
  qual(Qid,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 

tvarpospre(Compid,Vn,Predid,Idx) :- 
  composite(Compid), 
  tlist(Compid,Bidx,Qid),
  qual(Qid,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 



% Make one for constraints 
bodyvarpospre(Rid,Vn,Predid,Idx) :- 
  constraint(Rid), 
  bodylist(Rid,Bidx,Predid),
  pred(Predid,Pn), 
  alist(Predid,Idx,Vid), 
  var(Vid,Vn). 


one(1). 


% Auxiliary to force constants via variables assignments
onerule(Rid,One) :- 
  one(One),
  rule(Rid). 

% Each inlist/4 of length bodycount/2 should now be evaluated 
% to produce an OK wrt. the rules and produced variables. 
% Potentials are those lists that have the same length
% as indicated by bodycount. 
% This should no longer be needed, lists are potential by construction 
%potential(Rid,Lid) :- 
%  bodycount(Rid,N), 
%  litem(Lid,Rid,Mapid,Nxt,N). 

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

% Associate an entry on the conjunction list here 
lmap(Conjid, Predid, v(N,Val1,X)) :- 
  apredlst(Aid,Pn,v(N,Val1,X)), 
  composite(Conjid),
  tlist(Conjid,I,Qid),
  qual(Qid,Predid), 
  pred(Predid,Pn),
  arity(Predid,N).

% Mark a negated bodyitem with list nil. 
lmap(Rid,Predid,nil) :- 
  bodylist(Rid,I,Predid),
  neg(Predid). 

% Mark a bexpr/ bodyitem as nil
lmap(Rid,Predid,nil) :- 
  bodylist(Rid,I,Predid),
  bexpr(Rid,Predid). 

% Mark a composite bodyitem with list nil. 
lmap(Rid,Predid,nil) :- 
  bodylist(Rid,I,Predid),
  composite(Predid). 



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
  % Or anything associated with apredlst. 
  % Starting up Aid is an existing assertion, but later 
  % on it may be a generated ID. 
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
  not diffxassign(X1,X2). 

inconsistentxlist(Rid,X) :- 
  xassign(Rid,Predid1,Vn,Val1,X), 
  xassign(Rid,Predid2,Vn,Val2,X),
  Val1 != Val2. 

%consistentxlist(Rid,X) :- 
%  not inconsistentxlist(Rid, X), 
%  bodycount(Rid,Len), 
%  zlist(Rid,Len,X).

% A version of tassign for conjunctive lists 
tassign(Rid,Predid,Vn,Val, v(N,Val1,Rest)) :- 
  % The assignment list from a ground predicate 
  lmap(Rid,Predid,v(N,Val1,Rest)), 
  % We need the variables bound by Predid. 
  tvarpospre(Rid,Vn,Predid,Pos),
  % Starting up Aid is an existing assertion, but later 
  % on it may be a generated ID. 
  nthinapredlst(Aid,Pn,Pos, v(Pos,Val,X), v(N,Val1,Rest)).

tconflict(Rid,Vn, Val1, Predid1, Val2, Predid2, X1, X2) :- 
  tassign(Rid,Predid1,Vn,Val1, X1),
  tassign(Rid,Predid2,Vn,Val2, X2),
  Val1 != Val2. 




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
%vlist(Rid,Pn,v(1, Val, nil), X ) :- 
%  visiblexassign(Rid,Vn,Val,X),
%  % We need the variables bound by Predid. 
%  bodyvarpospre(Rid,Vn,Predid,Pos), 
%  Pos == 1, 
%  head(Rid,Hid),
%  pred(Hid,Pn).

% Build iteratively 
%vlist(Rid,Pn,v(N+1, Valnew, v(N, Val, Rest) ), X) :- 
%  vlist(Rid,Pn,v(N, Val, Rest), X ), 
%  visiblexassign(Rid,Vn,Valnew,X),
%  bodyvarpospre(Rid,Vn,Predid,N+1), 
%  head(Rid,Hid),
%  pred(Hid,Pn).

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
  % We'd need 
  not xconflict(Rid,Vnnew, Valnew, Predidnew, Valold, Predidold, X, L).  % XXXXXXXXXXXXXXXXX
  %xcompatible(Rid,Vnnew,Valnew, X, L), 
  %xcompatible(Rid,Vnold,Valold, L, X). 


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

%%%%%%%%%%%%%%%%%%%%
% Below we have essentially the same as vlist2, but with all the variables
% not just those in the head.
% xassign(8,12,"Y","1",v(2,"2",v(1,"1",nil))).
%%%%%%%%%%%%%%%%%%%%

% First make a list of mappings for each of the 
% bodies in a rule.
% We handle the first case here. 
flist(Rid,f(1, Bpredid, Vlist, nil) ) :- 
  bodylist(Rid,1,Bpredid), 
  lmap(Rid,Bpredid,Vlist). 

% Then combine with others
% This contains all of the possible permutations,
% we might want to check the immediate compatibility 
% at ths step.
% There is xconflicting, but we'd need to access the 
% lists via xconflict. 
% Other, easier, way is to check the conflict between 
% the Predid,Groundid pairs. This could exist. 
flist(Rid, f(N+1, Bpredidnew, Vlistnew, f(N, Bpredidold, Vlistold, Rest) ) ) :- 
  flist(Rid,f(N, Bpredidold, Vlistold, Rest) ), 
  bodylist(Rid,N+1,Bpredidnew), 
  lmap(Rid,Bpredidnew,Vlistnew). 

% Accessors for the flist/
nthinflist(Rid, N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest), 
	     f(N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest)))
:- 
  flist(Rid, f(N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest))),
  bodycount(Rid,N). 

% Here we do the next step, using the previous item as base 
nthinflist(Rid, N-1, Predid, SrcL, Rest, Orig )
:- 
  nthinflist(Rid, N, Bpredidold, Srclold, f(N-1,Predid,SrcL,Rest), Orig),
  N > 0. 

% Finally, we need to handle the case of lists of length one 
nthinflist(Rid, 1, Predid, SrcL, nil, f(1, Predid, SrcL, nil ) ) 
:- 
  flist(Rid, f(1, Predid, SrcL, nil )),  % Not working due to z()
  bodycount(Rid,1). 

% Now we replicate flist for the typed list thingy 

% First make a list of mappings for each of the 
% predicates in typed lists. 
% We handle the first case here. 
typedlist(Rid,f(1, Bpredid, Vlist, nil) ) :- 
  tlist(Rid,1,Qid), 
  qual(Qid,Bpredid), 
  lmap(Rid,Bpredid,Vlist). 

% Then combine with others
% This contains all of the possible permutations,
% we might want to check the immediate compatibility 
% at ths step.
% There is xconflicting, but we'd need to access the 
% lists via xconflict. 
% Other, easier, way is to check the conflict between 
% the Predid,Groundid pairs. This could exist. 
typedlist(Rid, f(N+1, Bpredidnew, Vlistnew, f(N, Bpredidold, Vlistold, Rest) ) ) :- 
  typedlist(Rid,f(N, Bpredidold, Vlistold, Rest) ), 
  tlist(Rid,N+1,Qid), 
  qual(Qid,Bpredidnew),
  lmap(Rid,Bpredidnew,Vlistnew). 

% Accessors for the flist/
nthintypedlist(Rid, N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest), 
	     f(N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest)))
:- 
  typedlist(Rid, f(N, Bpredid, Vlist, f(N-1, Bpredidnxt, Vlistnxt, Rest))),
  % bodycount(Rid,N). 
  compositenum(Rid,N). 

% Here we do the next step, using the previous item as base 
nthintypedlist(Rid, N-1, Predid, SrcL, Rest, Orig )
:- 
  nthintypedlist(Rid, N, Bpredidold, Srclold, f(N-1,Predid,SrcL,Rest), Orig),
  N > 0. 

% Finally, we need to handle the case of lists of length one 
%nthintypedlist(Rid, 1, Predid, SrcL, nil, f(1, Predid, SrcL, nil ) ) 
%:- 
%  nthintypedlist(Rid, f(1, Predid, SrcL, nil )),  % Not working due to z()
%  compositenum(Rid,1). 




%
% Now produce a variable mapping which may be inconsistent
% Rid 	      		 rule ID
% Vn			 variable name 
% Val			 variable value
% L			 the source flist, which contains all 
% 			 of the mappings to rulebodies. 
% 
rassign(Rid,Vn,Val,L) :- 
  xassign(Rid,Predid,Vn,Val,GL), % GL is the list produced by a ground fact 
  nthinflist(Rid,N,Predid,GL,Tmp,L). 
  % bodycount(Rid,N). % We force this to use a list which has assignments for all 
  % perhaps not a good idea 

% Compatibility between two assignments 
% cflctrassign(Rid,Vn,Val1,Val2,L) :- 
cflctrassign(Rid,L) :- 
  rassign(Rid,Vn,Val1,L), 
  rassign(Rid,Vn,Val2,L),
  Val1 != Val2.

% Purpose made for !=, could we modularize?
cflctrassign(Rid,L) :- 
  rassign(Rid,Vnl,Vall,L), 
  rassign(Rid,Vnr,Valr,L),
  % Get the bexpr 
  bexpr(Rid,Bid), 
  larg(Bid,Left), 
  rarg(Bid,Right), 
  var(Left,Vnl),
  var(Right,Vnr), 
  bop(Bid,"!="),
  Vall == Valr. 

cflctrassign(Rid,L) :- 
  rassign(Rid,Vnl,Vall,L), 
  rassign(Rid,Vnr,Valr,L),
  % Get the bexpr 
  bexpr(Rid,Bid), 
  larg(Bid,Left), 
  rarg(Bid,Right), 
  var(Left,Vnl),
  var(Right,Vnr), 
  bop(Bid,"=="),
  Vall != Valr. 

cflctrassign(Rid,L) :- 
  rassign(Rid,Vnl,Vall,L), 
  rassign(Rid,Vnr,Valr,L),
  % Get the bexpr 
  bexpr(Rid,Bid), 
  larg(Bid,Left), 
  rarg(Bid,Right), 
  var(Left,Vnl),
  var(Right,Vnr), 
  bop(Bid,">"),
  Vall <= Valr. 

cflctrassign(Rid,L) :- 
  rassign(Rid,Vnl,Vall,L), 
  rassign(Rid,Vnr,Valr,L),
  % Get the bexpr 
  bexpr(Rid,Bid), 
  larg(Bid,Left), 
  rarg(Bid,Right), 
  var(Left,Vnl),
  var(Right,Vnr), 
  bop(Bid,"<"),
  Vall >= Valr. 


% Debugging tool, not really needed ...
cleanrassign(Rid,L) :- 
  rassign(Rid,Vn,Val1,L), 
  not cflctrassign(Rid,L). 

%
% Now produce a variable mapping for the conjunctions. This 
% mirrors rassign/. 
% The assignments may be inconsistent internally or wrt. 
% rassign.
% 
% Rid 	      		 rcomposite ID
% Vn			 variable name 
% Val			 variable value
% L			 the source flist, which contains all 
% 			 of the mappings to rulebodies. 
% 
testassign(Rid,Vn,Val,L) :- 
  tassign(Rid,Predid,Vn,Val,GL), % GL is the list produced by a ground fact 
  nthintypedlist(Rid,N,Predid,GL,Tmp,L). 
  % bodycount(Rid,N). % We force this to use a list which has assignments for all 
  % perhaps not a good idea 

cflcttestassign(Rid,L) :- 
  testassign(Rid,Vn,Val1,L), 
  testassign(Rid,Vn,Val2,L),
  Val1 != Val2.

% Now we match testassign/ s with xassigns
% which provide the binding within the rule.
compatibletandx(Rid,Compoundid,Xa,Ta) :- 
  testassign(Compoundid,Vn,Val1,Ta), 
  not cflcttestassign(Compoundid,Ta),
  rassign(Rid,Vn,Val1,Xa), 
  not cflctrassign(Compoundid,Ta),
  % They agree on varaibles
  % They must be connected 
  rulecomposite(Rid,Compoundid). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Now we are ready to try to tackle nonevaluable rules
% hamilton_toground.lp.reified as example. 

% First let's generate a head 
hasrule(1,id(Id,0)) :- 
  prnonevaluable(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id).      % This is needed to access the ID 

rule(id(Id,0)) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id).      % This is needed to access the ID 

constraint(id(Id,0)) :- 
  prnonevaluable(Rid), 
  constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id).      % This is needed to access the ID 
  
ground(id(Id,0)) :- 
  prnonevaluable(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id). 

newname(id(Id,0),"HUU",Rid) :- 
  prnonevaluable(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id). 

pos(id(Id,1)) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id). 

head(id(Id,0),id(Id,1)) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id). 

pred(id(Id,1), Pn ) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id),
  head(Rid,Hid), 
  pred(Hid,Pn). 

% Now dig the variables and combine with rassign 
alist(id(Id,1),N,id(Id,1+N)) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  head(Rid,Hid), 
  alist(Hid,N,Vid),
  var(Vid,Vn),
  rassign(Rid,Vn,Val1,Id). 

cnst(id(Id,1+N),Val1) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id),
  head(Rid,Hid), 
  alist(Hid,N,Vid),
  var(Vid,Vn).
  
% Make an apredlist still out of this. 
apredlst(Id,Pn,v(1,Val1,nil) ) :- 
  prnonevaluable(Rid), 
  not constraint(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id),
  head(Rid,Hid), 
  pred(Hid,Pn),
  alist(Hid,1,Vid),
  var(Vid,Vn).

apredlst(Id,Pn,v(N+1,Val1,v(N,Valold,Rest)) ) :- 
  apredlst(Id,Pn,v(N,Valold,Rest) ), 
  not constraint(Rid), 
  prnonevaluable(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id),
  head(Rid,Hid), 
  pred(Hid,Pn),
  alist(Hid,N+1,Vid),
  var(Vid,Vn).



%arity(id(Id,1),A) :- 
%  prnonevaluable(Rid), 
%  not cflctrassign(Rid,Id), 
%  head(Rid,Hd), 
%  arity(Hd,A), 
%  rassign(Rid,Vn,Val1,Id). 

% Next an item in the body
% In order to be able to count the values of the 
% new indexes we must know the previous ones.
% When we start from the first one, there are no 
% unknowns. 
% Later we project bodylist/3 to body/2. 
protobodylist(Rid, N, A2, Predid, id(Id,1), id(Id,Predid), Id) :- 
  prnonevaluable(Rid), 
  not cflctrassign(Rid,Id), 
  rassign(Rid,Vn,Val1,Id),
  %head(Rid,Hd), 
  %arity(Hd,A),              % Arity A means that there been 1+A new IDs for the head
  bodylist(Rid,N,Predid),   % we start with the first item of the bodylist 
  arity(Predid,A2). 

bodylist(id(Id,0), N, id(Id,X) ) :- 
  protobodylist(Rid, N, A2, Predid, id(Id,Z), id(Id,X), Id). 

body(id(Id,0),id(Id,X)) :- 
  protobodylist(Rid, N, A2, Predid, id(Id,Z), id(Id,X), Id). 

% Now create the predicate
pred(id(Id,Bodyctr), Pn ) :- 
  protobodylist(Rid, N, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id), 
  pred(Predid,Pn). 

pos(id(Id,Bodyctr)) :- 
  protobodylist(Rid, N, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id), 
  pos(Predid). 

neg(id(Id,Bodyctr)) :- 
  protobodylist(Rid, N, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id), 
  neg(Predid). 

% Copy the argument list 
% zalist(id(Id,Bodyctr),N,id(Id,Bodyctr+N)) :- 
alist(id(Id,Bodyctr),N,id(Id,Vid)) :- 
  protobodylist(Rid, Bodyid, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id),
  alist(Predid,N,Vid).

cnst(id(Id,Bodyctr+N),Val1) :- 
  protobodylist(Rid, Bodyid, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id), 
  rassign(Rid,Vn,Val1,Id),
  alist(Predid,N,Vid), 
  var(Vid,Vn).

% Handle the compound or typed list tlist/. Out of this we produce 
% an amount of predicates, which are specified by the first item 
% of the tlist. We do not tie this to the tlist index or the bodylist index.
typedbody(id(Id,0), id(Id,Ta,Compoundid) ) :- 
  protobodylist(Rid, Bodyid, Arity, Predid, id(Id,Rlctr), id(Id,Bodyctr), Id), 
  compatibletandx(Rid,Compoundid,Id,Ta). 

% Now produce the body 
body( id(Id,0), id(Id,Ta,Compoundid) ) :- 
  typedbody(id(Id,0), id(Id,Ta,Compoundid) ).

% Next the predicate 
% pred(id(Id,Ta,Compoundid), Pn, N, Cid) :- 
pred(id(Id,Ta,Compoundid), Pn) :- 
  typedbody(id(Id,0), id(Id,Ta,Compoundid) ),
  tlist(Compoundid,1,Form), 
  qual(Form, Predid),
  alist(Predid,N,Cid),
  pred(Predid,Pn).   % The end of original


neg(id(Id,Ta,Compoundid)) :- 
  typedbody(id(Id,0), id(Id,Ta,Compoundid) ),
  tlist(Compoundid,1,Form), 
  qual(Form, Predid),
  neg(Predid).

% zneg(
%  id(
%   f(2,61,v(1,"1",nil),f(1,63,nil,nil)),
%   f(2,69,v(2,"1",v(1,"2",nil)),f(1,65,v(2,"1",v(1,"2",nil)),nil)),
%   63)).
% 
% nthintypedlist(63,1,65,v(2,"3",v(1,"3",nil)),nil,f(2,69,v(2,"2",v(1,"1",nil)),f(1,65,v(2,"3",v(1,"3",nil)),nil))).

% alist(id(Id,Ta,Compoundid),N,id(Id,Ta,Vid), Vlist, Predid) :- 
alist(id(Id,Ta,Compoundid),N,id(Id,Ta,Vid)) :- 
  typedbody(id(Id,0), id(Id,Ta,Compoundid)),
  nthintypedlist(Compoundid,1,Qid,Vlist,Tmp1,Ta), % Compoundid: 63 
  % The source platform 
  tlist(Compoundid,1,Form), 
  qual(Form, Predid),
  % pred(Predid,Pn), 
  alist(Predid,N,Vid).

cnst(id(Id,Ta,Vid), Val) :- 
  typedbody(id(Id,0), id(Id,Ta,Compoundid)),
  nthintypedlist(Compoundid,1,Qid,Vlist,Tmp1,Ta), % Compoundid: 63 
  tlist(Compoundid,1,Form), 
  qual(Form, Predid),
  % pred(Predid,Pn), 
  alist(Predid,N,Vid),
  nthinapredlst(R2,Pn,N,v(N,Val,Rest),Vlist). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Now we assign the N'th bodypredicate of Rid according to Lid
% This is just renaming the information in the list for now. 
%mkassign(Lid,Rid,Predid,Mapid,Jid,N) :- 
%  potential(Rid,Lid), 
%  bodylist(Rid,N,Predid), 
% % There is a mapid in this list 
%  isinlist(Lid,Mapid),
%  litem(Lid2,Rid,Mapid,Nxt,N), % now the index is matched to bodylist ...
%  % Which pertains to this N'th bodypredicate 
%  map(Mapid, Rid, N, Jid). 

%tstassign(Lid,Rid,Vn,Val) :- 
%  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
% bodyvarpos(Rid,Vn,N,Bpredidx), 
%  alist(Jid,Bpredidx,Cid), 
%  cnst(Cid,Val).

%%assignat(Lid,Rid,Bpredidx,Vn,Val) :- 
%%  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
%%  bodyvarpos(Rid,Vn,N,Bpredidx), 
%%  alist(Jid,Bpredidx,Cid), 
%%  cnst(Cid,Val).

% ---------------------

% Derive a simple position, value assignment for a rule 
% to be compared with groundassign/3.
%assign(Lid,Rid,N,Val) :- 
%  mkassign(Lid,Rid,Predid,Mapid,Jid,N), 
%  headvarval(Rid,Pn,N,Vn,Bidx,Bpredidx), 
%  alist(Jid,Bpredidx,Cid), 
% cnst(Cid,Val).

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





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% The funcsym based solutions
% are below
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

hasrule(1,id(Id,0)) :- 
  groundrule(Pn,Id).

pos(id(Id,1)) :- 
  groundrule(Pn,Id). 

ground(id(Id,0)) :- 
  groundrule(Pn,Id). 

newname(id(Id,0),"JOPI") :- 
  groundrule(Pn,Id). 

head(id(Id,0),id(Id,1)) :- 
  groundrule(Pn,Id). 

pred(id(Id,1), Pn ) :- 
  groundrule(Pn,Id). 

alist(id(Id,1),N,id(Id,1+N)) :- 
  groundrule(Pn,Id), 
  nthinapredlst(Rid,Pn,N,Item,Id ). 

cnst(id(Id,1+N),Val) :- 
  groundrule(Pn,Id), 
  nthinapredlst(Rid,Pn,N,v(N,Val,Rest),Id ). 

arity(id(Id,1),A) :- 
  head(Rid,Hd), 
  arity(Hd,A), 
  groundrule(Pn,Id), 
  nthinapredlst(Rid,Pn,N,v(N,Val,Rest),Id ). 

assert(id(Id,0)) :- 
  groundrule(Pn,Id). 


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

% A rule has a body which is negated
nonevaluable(Rid,Bid) :- 
  body(Rid,Bid), 
  neg(Bid). 

% The negated body may also be inside the typed list 
nonevaluable(Rid,Bid) :- 
  body(Rid,Bid), 
  composite(Bid), 
  tlist(Bid,1,Qid),
  qual(Qid,Predid), 
  neg(Predid). 

% Constraint is always noneval
nonevaluable(Rid,Bid) :- 
  body(Rid,Bid), 
  constraint(Rid). 

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

#hide. 

#show rule/1. 
#show ground/1. 
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
#show bexpr/2.
#show bop/2.
#show larg/2.
#show rarg/2.
#show constraint/1. 

