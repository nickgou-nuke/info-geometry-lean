# GAP witness for the finite spinorial monodromy parity group.
# Run with the GAP executable from the Sage environment.

# The one-loop spinorial transport is the nontrivial element of C2.
G := CyclicGroup(IsPermGroup, 2);
g := GeneratorsOfGroup(G)[1];

if g^2 <> One(G) then Error("double loop is not identity"); fi;
if g = One(G) then Error("single loop is not the parity flip"); fi;

# Signed readout: identity -> +1, nontrivial one-loop -> -1.
sign := function(a)
  if a = One(G) then return 1; fi;
  if a = g then return -1; fi;
  Error("unexpected element");
end;

if sign(g) <> -1 then Error("one-loop sign is not -1"); fi;
if sign(g^2) <> 1 then Error("two-loop sign is not +1"); fi;
if sign(g) + sign(One(G)) <> 0 then Error("boundary pair did not cancel"); fi;

Print("gap spinorial monodromy parity certificate: ok\n");
QUIT;
