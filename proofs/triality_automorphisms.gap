# triality_automorphisms.gap
# Formulate the discrete S3 group action on the Spin(8) representations

# Define the outer automorphism group S3
S3 := SymmetricGroup(3);

# The three representations 8_v, 8_s, 8_c can be thought of as a set of 3 objects
reps := ["8_v", "8_s", "8_c"];

# Action of S3 on the set of representations
Print("Action of S3 on the representations {8_v, 8_s, 8_c}:\n");
for g in Elements(S3) do
    Print(g, " acts as: \n");
    for i in [1..3] do
        Print("  ", reps[i], " -> ", reps[i^g], "\n");
    od;
od;
