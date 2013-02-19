%
% sample2.lp
% 
% This is a development time test case for grounding; this
% rule does not do any sensible calculation. 
% This rule may not be groundable at all as explained below,
% there should be a warning or no grounding. 
% 
% This is a modification of the sample.lp, where we now
% have two ground node-predicates, which constrain the 
% values for oncycle. At this point we cannot distinguish 
% the potential problem in sample1.lp. 
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

node(1).
node(2).

