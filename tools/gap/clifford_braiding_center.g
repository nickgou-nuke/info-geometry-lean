# GAP finite group witness for the Clifford central-core packet.
# Checks only the abstract Z2 central core and preservation by conjugation in D8.

RequireTrue := function(name, cond)
  if not cond then Error(Concatenation("[FAIL] ", name)); fi;
  Print("[OK] ", name, "\n");
end;

Z2 := CyclicGroup(2);;
RequireTrue("central core has order 2", Size(Z2) = 2);

D8 := DihedralGroup(IsPermGroup, 8);;
r := (1,2,3,4);;
s := (2,4);;
centerCore := Group(r^2);;
RequireTrue("D8 central sign core has order 2", Size(centerCore) = 2);
RequireTrue("rotation centralizes sign core", ForAll(Elements(centerCore), z -> r^-1 * z * r = z));
RequireTrue("reflection preserves sign core", ForAll(Elements(centerCore), z -> s^-1 * z * s in centerCore));
RequireTrue("nontrivial sign squares to identity", ForAll(Elements(centerCore), z -> z^2 = One(D8)));

Print("GAP_CLIFFORD_BRAIDING_CENTER_OK\n");
