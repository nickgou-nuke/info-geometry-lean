# GAP Script to implement conformal inversion as group automorphism
Print("Conformal Inversion as Group Automorphism\n");

# Define a permutation group or matrix group
G := GL(4, Rationals);
# The inversion matrix
inv_mat := [ [0,0,0,1], [0,1,0,0], [0,0,1,0], [1,0,0,0] ];
inv_elem := inv_mat * One(G);

# Isotropic subgroups (Origin and Infinity)
sub_infty := Subgroup(G, [ [ [1,1,0,0], [0,1,0,0], [0,0,1,0], [0,0,0,1] ] ]);
sub_zero := Subgroup(G, [ [ [1,0,0,0], [0,1,0,0], [0,0,1,0], [0,0,1,1] ] ]);

Print("Subgroup Infinity: ", sub_infty, "\n");
Print("Subgroup Zero: ", sub_zero, "\n");

# Automorphism by conjugation
Print("Applying conformal inversion...\n");
# Conjugation of generators
gen_infty := GeneratorsOfGroup(sub_infty)[1];
mapped_gen := inv_elem^-1 * gen_infty * inv_elem;

Print("Mapped generator of Infinity: \n", mapped_gen, "\n");
Print("Generator of Zero: \n", GeneratorsOfGroup(sub_zero)[1], "\n");

if mapped_gen = GeneratorsOfGroup(sub_zero)[1] then
    Print("Success: Conformal inversion exchanges the isotropic subgroups corresponding to Origin and Infinity.\n");
fi;
