% sample2.lp.reified.ground
% Source key: "51"
edge(1 , 2).

% Source key: "55"
edge(2 , 3).

% Source key: "59"
edge(3 , 1).

% Source key: "63"
edge(1 , 3).

% Source key: "67"
edge(3 , 2).

% Source key: "71"
edge(2 , 1).

% Source key: "75"
node(1).

% smres1.lp.ground
% Vars for "39" : ("X": "1")
% Source key: "39"
:- 
	 not oncycle(3 , 1) ,
	 not oncycle(2 , 1) ,
	 % ctlist for "42" with initial ("1","43") ,
	 node(1).

