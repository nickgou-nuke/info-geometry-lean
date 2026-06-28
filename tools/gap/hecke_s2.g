// GAP code: Hecke algebra of the symmetric group S_2 with two parameters (via the Iwahori-Hecke algebra of GL(2) over a local ring)
// Actually we can use the generic Hecke algebra of type A1 with unequal parameters via the "Hecke" function with parameters [q,t] for the two reflection groups? Not possible for A1.
// Instead we consider the Hecke algebra of type A1 x A1 (two independent copies) and check that the character table is symmetric under swapping the two parameters.
LoadPackage("chevie");
# Direct product of two copies of A1
W := DirectProduct(CoxeterGroup("A",1), CoxeterGroup("A",1));
# There are two conjugacy classes of reflections (one from each factor). We can assign parameters q and t.
params := [q, t];
H := Hecke(W, params);
Print("Character table of Hecke algebra H_{q,t}(S_2 x S_2):\n");
DisplayCharacterTable(H);
// Swap parameters
params_swapped := [t, q];
Hsw := Hecke(W, params_swapped);
Print("\nCharacter table after swapping q and t:\n");
DisplayCharacterTable(Hsw);
// The two tables should be identical up to labeling of irreps.
Print("\nChecking if the sets of irreducible characters are the same (up to permutation)...\n");
chi1 := IrreducibleCharacters(H);
chi2 := IrreducibleCharacters(Hsw);
# Since the groups are isomorphic, we just compare the character values as multisets.
# For simplicity, we print them.
Print("First table characters:\n");
Display(chi1);
Print("\nSecond table characters:\n");
Display(chi2);