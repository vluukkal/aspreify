% sample3.lp.reified.ground
% Source key: "91"
edge(1 , 2).

% Source key: "95"
edge(2 , 3).

% Source key: "99"
edge(3 , 1).

% Source key: "103"
edge(1 , 3).

% Source key: "107"
edge(3 , 2).

% Source key: "111"
edge(2 , 1).

% Source key: "115"
node(1).

% Source key: "118"
node(2).

% smres1.lp.ground
% Vars for "79" : ("X": "2")
% Source key: "79"
:- 
	 not oncycle(3 , 2) ,
	 not oncycle(1 , 2) ,
	 % ctlist for "82" with initial ("1","83") ,
	 node(2).

% smres2.lp.ground
% Vars for "79" : ("X": "1")
% Source key: "79"
:- 
	 not oncycle(3 , 1) ,
	 not oncycle(2 , 1) ,
	 % ctlist for "82" with initial ("1","83") ,
	 node(1).

