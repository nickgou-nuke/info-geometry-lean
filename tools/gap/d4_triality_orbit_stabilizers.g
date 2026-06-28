# d4_triality_orbit_stabilizers.g
#
# Computes Weyl orbits and stabilizers for D4 triality.

Print("Initializing D4 root system...\n");
L := SimpleLieAlgebra("D", 4, Rationals);
R := RootSystem(L);
C := CartanMatrix(R);

Print("Constructing Weyl group on weight space...\n");
# The Cartan matrix columns represent the action of simple roots.
# We build the simple reflections s_i acting on fundamental weights.
mat_gens := [];
for i in [1..4] do
    mat := IdentityMat(4, Rationals);
    for k in [1..4] do
        mat[i][k] := mat[i][k] - C[i][k];
    od;
    Add(mat_gens, mat);
od;
W := Group(mat_gens);
Print("Weyl group size: ", Size(W), "\n\n");

Print("Computing orbits for 8v, 8s, 8c weights...\n");
# In D4, node 2 is the central node. Nodes 1, 3, 4 are outer nodes.
# Their fundamental weights correspond to 8v, 8s, 8c.
w_v := [1, 0, 0, 0]; # 8v
w_s := [0, 0, 1, 0]; # 8s
w_c := [0, 0, 0, 1]; # 8c

orb_v := Orbit(W, w_v);
orb_s := Orbit(W, w_s);
orb_c := Orbit(W, w_c);

Print("Orbit 8v size: ", Size(orb_v), "\n");
Print("Orbit 8s size: ", Size(orb_s), "\n");
Print("Orbit 8c size: ", Size(orb_c), "\n\n");

Print("Defining S3 outer automorphism (triality)...\n");
# S3 permutes the outer nodes 1, 3, and 4
p1 := [ [0,0,1,0], [0,1,0,0], [1,0,0,0], [0,0,0,1] ]; # (1,3)
p2 := [ [0,0,0,1], [0,1,0,0], [0,0,1,0], [1,0,0,0] ]; # (1,4)
S3 := Group(p1, p2);

Print("Checking if S3 permutes the orbits...\n");
map_v_p1 := Set(orb_v, v -> v * p1);
map_v_p2 := Set(orb_v, v -> v * p2);

permutes_correctly := (map_v_p1 = Set(orb_s)) and (map_v_p2 = Set(orb_c));
if permutes_correctly then
    Print("Success: S3 correctly permutes 8v -> 8s and 8v -> 8c\n\n");
else
    Print("Failure: S3 did not permute orbits correctly\n\n");
fi;

Print("Calculating stabilizers and relation to SU(3) subgroup embeddings...\n");
# A stabilizer of an outer node fundamental weight corresponds to deleting
# that node from the Dynkin diagram, leaving A3 (Weyl group of SO(6)).
stab_v := Stabilizer(W, w_v);
stab_s := Stabilizer(W, w_s);
stab_c := Stabilizer(W, w_c);

Print("Size of individual stabilizers: ", Size(stab_v), ", ", Size(stab_s), ", ", Size(stab_c));
Print(" (Matches W(A3) = S4, size 24)\n");

# The intersection of two stabilizers corresponds to deleting two outer nodes.
# This leaves the central node and one outer node, an A2 Dynkin diagram.
# The Weyl group of A2 is S3, which corresponds to the SU(3) subgroup.
int_vs := Intersection(stab_v, stab_s);
int_vc := Intersection(stab_v, stab_c);
int_sc := Intersection(stab_s, stab_c);

Print("Intersection (8v, 8s) size: ", Size(int_vs), "\n");
Print("Intersection (8v, 8c) size: ", Size(int_vc), "\n");
Print("Intersection (8s, 8c) size: ", Size(int_sc), "\n");
Print("(Matches W(A2) = S3, size 6, representing SU(3) subgroup embeddings)\n\n");

# Final checks
sizes_correct := (Size(orb_v) = 8) and (Size(orb_s) = 8) and (Size(orb_c) = 8);
stabs_correct := (Size(stab_v) = 24) and (Size(int_vs) = 6);

if sizes_correct and permutes_correctly and stabs_correct then
    Print("PASS\n");
else
    Print("FAIL\n");
fi;
