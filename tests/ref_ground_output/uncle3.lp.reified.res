% smres1.lp.ground
% Vars for "2" : ("U": "zeus")("P": "poseidon")("C": "theseus")
% Source key: "2"
uncle(zeus , theseus) :- 
	 child(poseidon , theseus) ,
	 sibling(poseidon , zeus) ,
	 male(zeus).

% smres2.lp.ground
% Vars for "2" : ("U": "poseidon")("P": "zeus")("C": "athena")
% Source key: "2"
uncle(poseidon , athena) :- 
	 child(zeus , athena) ,
	 sibling(zeus , poseidon) ,
	 male(poseidon).

% smres3.lp.ground
% Vars for "2" : ("U": "poseidon")("P": "zeus")("C": "apollo")
% Source key: "2"
uncle(poseidon , apollo) :- 
	 child(zeus , apollo) ,
	 sibling(zeus , poseidon) ,
	 male(poseidon).

% uncle3.lp.reified.ground
% Source key: "14"
male(zeus).

% Source key: "17"
male(poseidon).

% Source key: "20"
child(zeus , athena).

% Source key: "24"
child(zeus , apollo).

% Source key: "28"
sibling(zeus , poseidon).

% Source key: "32"
sibling(poseidon , zeus).

% Source key: "36"
child(poseidon , theseus).

