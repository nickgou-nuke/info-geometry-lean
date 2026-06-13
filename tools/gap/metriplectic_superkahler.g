# Finite grading smoke test for central-core / Z_n phase bookkeeping.
# This does not prove super-Kahler geometry or metriplectic thermodynamics.

RequireTrue := function(name, cond)
  if not cond then Error(Concatenation("[FAIL] ", name)); fi;
  Print("[OK] ", name, "\n");
end;

C3 := CyclicGroup(3);;
g3 := GeneratorsOfGroup(C3)[1];;
RequireTrue("Z3 grading generator cubes to identity", g3^3 = One(C3));
RequireTrue("Z3 grading has order 3", Order(g3) = 3);

Z2 := CyclicGroup(2);;
g2 := GeneratorsOfGroup(Z2)[1];;
RequireTrue("Z2 central sign generator squares to identity", g2^2 = One(Z2));
RequireTrue("Z2 central sign has order 2", Order(g2) = 2);

Print("FINITE_CENTER_GRADING_GAP_OK\n");
