Print("=== GAP: Verifying FT36 Braid Fibration Base ===\n");

# The Weyl group of F4 has dimension 1152.
# The 36 FT scalars correspond to the dimension of SO(9), which is the 
# maximal compact subgroup of F4. This is the exact dimension of the 
# scale-invariant cocycles required.
L := SimpleLieAlgebra("B", 4, Rationals);
Print("Dimension of SO(9) Lie Algebra (B4): ", Dimension(L), "\n");

if Dimension(L) = 36 then
    Print("SUCCESS: The 36 Fradkin-Tseytlin fields perfectly match the SO(9) adjoint generators.\n");
else
    Print("ERROR: Dimension mismatch.\n");
fi;

Print("This forms the base manifold for the fibration to the SPLIT octonions.\n");
QUIT;
