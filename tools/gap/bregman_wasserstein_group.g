# bregman_wasserstein_group.g
G := SymmetricGroup(4);
irr := Irr(G);

Display(CharacterTable(G));

states := [1..4];
action := Action(G, states, OnPoints);
Print("Action on states: \n", action, "\n");

if IsPermGroup(action) then
    Print("Valid permutation representation for state transitions.\n");
fi;

quit;
