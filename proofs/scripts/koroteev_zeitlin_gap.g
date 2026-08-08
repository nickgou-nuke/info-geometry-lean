# GAP algebraic structure for the 3D mirror self-duality Weyl group action
n := 4;;
W := SymmetricGroup(n);;
Z_twist := [1, -1, I, -I];;
# Action of the Weyl group on the Z-twisted Miura opers
orbit := Orbit(W, Z_twist, Permuted);;
Print("Orbit size of Z-twist under Weyl group: ", Size(orbit), "\n");
