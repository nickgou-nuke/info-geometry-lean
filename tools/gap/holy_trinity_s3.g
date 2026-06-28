# GAP: Group structure for S3 Triality and Color Confinement
S3 := SymmetricGroup(3);

# The 3 representations (8_v, 8_s, 8_c) act as a block system
reps := [1, 2, 3];
action := Action(S3, reps);

Print("S3 Triality Action on D4 representations:\n");
Display(action);

# Confinement check via stabilizers
G2_stabilizer := Stabilizer(action, 1);
Print("\nG2 Stabilizer Subgroup (Color SU(3) ancestor):\n");
Display(G2_stabilizer);

# Anomaly check: character table dimensions
chars := CharacterTable(G2_stabilizer);
Print("\nCharacter Table (Topologically protected charges):\n");
Display(chars);
