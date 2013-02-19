%
% sample1.lp 
%
% This is a development time test case for grounding; this
% rule does not do any sensible calculation. 
% This rule may not be groundable at all as explained below,
% there should be a warning or no grounding. 
% 
% We have a conjunctive constraint requiring presence of 
% ground edge-predicates. There is another predicate 
% node outside of the conjunction. As there are no 
% ground node-predicates, nothing should be generated.
% However, we reverse the flow of this stuff and produce
% a valuation for the X inside of node-predicate by first 
% producing all possible valuations produced by edge-predicates.
%

:- 
 	 not oncycle(Y , X)  :  edge(Y , X) ,
 	 node(X).
 
edge(1 , 2).
edge(2 , 3).
edge(3 , 1).
edge(1 , 3).
edge(3 , 2).
edge(2 , 1).


