# GAP script to check split octonion automorphism group size and stabilizer over GF(2)
T := EmptySCTable(8, Zero(GF(2)));;

SetEntrySCTable(T, 1, 1, [One(GF(2)), 1]);
SetEntrySCTable(T, 2, 2, [One(GF(2)), 2]);

for i in [1..3] do
  SetEntrySCTable(T, 1, 2 + i, [One(GF(2)), 2 + i]);
  SetEntrySCTable(T, 2 + i, 2, [One(GF(2)), 2 + i]);
  SetEntrySCTable(T, 2, 5 + i, [One(GF(2)), 5 + i]);
  SetEntrySCTable(T, 5 + i, 1, [One(GF(2)), 5 + i]);
  SetEntrySCTable(T, 2 + i, 5 + i, [One(GF(2)), 1]);
  SetEntrySCTable(T, 5 + i, 2 + i, [One(GF(2)), 2]);
od;

# up0 * up1 = down2
SetEntrySCTable(T, 3, 4, [One(GF(2)), 8]);
# up1 * up2 = down0
SetEntrySCTable(T, 4, 5, [One(GF(2)), 6]);
# up2 * up0 = down1
SetEntrySCTable(T, 5, 3, [One(GF(2)), 7]);

# up1 * up0 = down2
SetEntrySCTable(T, 4, 3, [One(GF(2)), 8]);
# up2 * up1 = down0
SetEntrySCTable(T, 5, 4, [One(GF(2)), 6]);
# up0 * up2 = down1
SetEntrySCTable(T, 3, 5, [One(GF(2)), 7]);

# down0 * down1 = up2
SetEntrySCTable(T, 6, 7, [One(GF(2)), 5]);
# down1 * down2 = up0
SetEntrySCTable(T, 7, 8, [One(GF(2)), 3]);
# down2 * down0 = up1
SetEntrySCTable(T, 8, 6, [One(GF(2)), 4]);

# down1 * down0 = up2
SetEntrySCTable(T, 7, 6, [One(GF(2)), 5]);
# down2 * down1 = up0
SetEntrySCTable(T, 8, 7, [One(GF(2)), 3]);
# down0 * down2 = up1
SetEntrySCTable(T, 6, 8, [One(GF(2)), 4]);

A := AlgebraByStructureConstants(GF(2), T);;
Print("Algebra dimension: ", Dimension(A), "\n");

G := AutomorphismGroup(A);;
Print("Automorphism group size: ", Size(G), "\n");

basis := Basis(A);;
J := basis[3] + basis[6];;
stab := Stabilizer(G, J);;
Print("Stabilizer group size: ", Size(stab), "\n");
Print("Structure description of stabilizer: ", StructureDescription(stab), "\n");
Print("Stabilizer generators:\n", GeneratorsOfGroup(stab), "\n");

QUIT;
