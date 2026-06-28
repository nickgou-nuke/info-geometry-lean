########################################################
# GAP Verification: Mirror Swap Involution
########################################################

Print("=== GAP: Mirror Clifford Bridge ===\n");

# Permutation representing the swap of compass coordinates
# (x0, x1, x2, x3) mapped to indices (1, 2, 3, 4)
# Swap: 1 <-> 3, 2 <-> 4
mirror_perm := (1,3)(2,4);

# Involution check
if mirror_perm * mirror_perm = () then
    Print("  [PASS] Mirror permutation is an involution.\n");
else
    Print("  [FAIL] Not an involution.\n");
fi;

# Metric signature vector for Cl(2,2): [1, -1, 1, -1]
sig := [1, -1, 1, -1];

# Verify signature is invariant under the mirror permutation
sig_mirror := Permuted(sig, mirror_perm);

if sig = sig_mirror then
    Print("  [PASS] Cl(2,2) signature (+,-,+,-) is invariant under chiral sheet exchange.\n");
else
    Print("  [FAIL] Signature not invariant.\n");
fi;
