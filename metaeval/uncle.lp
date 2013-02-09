%
% Simplistic rules and ground facts for a short ASP example,
% of grounding. 
%
% > gringo -t uncle.lp 
% 
% male(zeus).
% male(poseidon).
% child(zeus,athena).
% child(zeus,apollo).
% sibling(zeus,poseidon).
% sibling(poseidon,zeus).
% child(poseidon,theseus).
% uncle(zeus,theseus).
% uncle(poseidon,apollo).
% uncle(poseidon,athena).


uncle(U,C) :- 
  child(P,C), 
  sibling(P,U), 
  male(U). 

male(zeus).
male(poseidon).
child(zeus,athena).
child(zeus,apollo).
sibling(zeus,poseidon). % This is two way 
% We could make another rule to generate this, but we remain simplistic
sibling(poseidon,zeus). 

child(poseidon,theseus).

% The above should be the bare minimum to get Poseidon as uncle for Athena and Apollo
%male("Hades").
%sibling("Zeus","Hades"). % This is two way 

% sibling("Hera","Zeus"). % This also two way 
% sibling("Hestia","Zeus"). % This also two way 
% sibling("Demeter","Zeus"). % This also two way 