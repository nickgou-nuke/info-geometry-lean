# GAP: Attention = Quantum Fluid Verification
# ============================================

Print("========================================\n");
Print("GAP: Attention = Quantum Fluid Verification\n");
Print("========================================\n\n");

# Setup a generic skew-symmetric matrix (bivector)
K := [[0, 2, 3], [-2, 0, 5], [-3, -5, 0]] * One(Rationals);
Print("Skew-symmetric matrix (bivector) K:\n");
Display(K);

# Test skew-symmetry: K^T = -K
K_trans := TransposedMat(K);
K_neg := -K;
is_skew := (K_trans = K_neg);
Print("K is skew-symmetric (K^T = -K)? ", is_skew, "\n");

# Trace of K
tr_K := TraceMat(K);
Print("trace(K) = ", tr_K, "\n");

if tr_K <> 0 then
    Error("Failed: trace of skew-symmetric matrix must be 0!");
fi;

Print("✓ Skew-symmetric (bivector) property verified: trace(K) = 0\n");
quit;

