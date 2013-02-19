% sample2.lp.reified.ground
% Source key: "14"
edge(1 , 2).

% Source key: "18"
edge(2 , 3).

% Source key: "22"
edge(3 , 1).

% Source key: "26"
edge(1 , 3).

% Source key: "30"
edge(3 , 2).

% Source key: "34"
edge(2 , 1).

% Source key: "38"
node(1).

% smres1.lp.ground
% Vars for "2" : ("X": "1")
% Source key: "2"
:- 
	 not oncycle(3 , 1) ,
	 not oncycle(2 , 1) ,
	 % ctlist for "5" with initial ("1","6") ,
	 node(1).

