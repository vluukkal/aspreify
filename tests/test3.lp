ready(A) :- 
	"rdf:type"(A,"wp1:Activity"),
	not missing_commit(A).

missing_commit(A) :- 
	"rdf:type"(A,"wp1:Activity"),
	"wp1:uses"(A,Cap),
	not "wp1:commits"(Cap,A). 

notready(A) :- 
	"rdf:type"(A,"wp1:Activity"),
        missing_commit(A).

2{i(A,"wp1:active","yes"),d(A,"wp1:active","no")}2 :- 
	"rdf:type"(A,"wp1:Activity"),
        ready(A).

2{d(A,"wp1:active","yes"),i(A,"wp1:active","no")}2 :- 
	"rdf:type"(A,"wp1:Activity"),
        notready(A).

conflict(A1,A2,Type) :-
	"rdf:type"(A1,"wp1:Activity"),
	"rdf:type"(A2,"wp1:Activity"),
	neq(A1,A2),
	"wp1:uses"(A1,Cap1),
	"wp1:uses"(A2,Cap2),
	"rdf:type"(Cap1,Type),
	"rdf:type"(Cap2,Type),
	eq("dcs:AcousticOutputModalityCapability",Type).

waitingfor(A1,A2) :- 
	M{"wp1:commits"(Cap,A3):"rdf:type"(A3,"wp1:Activity")},
	"rdf:type"(A1,"wp1:Activity"),
	"rdf:type"(A2,"wp1:Activity"),
	neq(A1,A2),
	"wp1:uses"(A1,Cap),
	"rdf:type"(Cap,"dcs:Capability"),
	not "wp1:commits"(Cap,A1),
	"wp1:uses"(A2,Cap),
	"wp1:commits"(Cap,A2),
	max_users(Cap,M).

waiting_closure(A1,A2) :-
	"rdf:type"(A1,"wp1:Activity"),
	"rdf:type"(A2,"wp1:Activity"),
	waitingfor(A1,A2).   

deadlock(A):-
	"rdf:type"(A,"wp1:Activity"),
	waiting_closure(A,A).   
	

ssls_print(A1,"waits for",A2) :- 
	"rdf:type"(A1,"wp1:Activity"),
	"rdf:type"(A2,"wp1:Activity"),
	neq(A1,A2),
	waitingfor(A1,A2).


pot_waitingfor(A1,A2) :-
       "rdf:type"(A1,"wp1:Activity"),
       "rdf:type"(A2,"wp1:Activity"),
       neq(A1,A2),
       "wp1:uses"(A1,Cap),
       "rdf:type"(Cap,"dcs:Capability"),
       not "wp1:commits"(Cap,A1),
       "wp1:uses"(A2,Cap),
       "wp1:commits"(Cap,A2).

waiting_closure(A1,A3) :-
       "rdf:type"(A1,"wp1:Activity"),
       "rdf:type"(A2,"wp1:Activity"),
       "rdf:type"(A3,"wp1:Activity"),
       pot_waitingfor(A1,A2),
       waitingfor(A1,A2),
       waiting_closure(A2,A3).



2{d(A,"wp1:uses",Cap1),i(A,"wp1:pends",Cap1)}2 :-
   "rdf:type"(A,"wp1:Activity"),
   "wp1:uses"(A,Cap1), 
   banish(A).

2{d(A,"wp1:pends",Cap1),i(A,"wp1:uses",Cap1)}2 :-
   "rdf:type"(A,"wp1:Activity"),
   "wp1:pends"(A,Cap1).
   

1{banish(A):"rdf:type"(A,"wp1:Activity")}1 :-
   "rdf:type"(A1,"wp1:Activity"),
   deadlock(A1).

:- banish(A), 
   "rdf:type"(A,"wp1:Activity"),
   not deadlock(A).

show waitingfor(_,_).
show deadlock(_).
show conflict(_,_,_).
show banish(_).
