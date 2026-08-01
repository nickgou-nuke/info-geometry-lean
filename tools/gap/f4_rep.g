LoadPackage("liealgdb");
L := SimpleLieAlgebra("F", 4, Rationals);
# The fundamental weights are given by FundamentalWeights(RootSystem(L))
# For F4, the 26-dimensional representation is the fundamental representation corresponding to the 4th node (in Bourbaki notation).
# We can just get the adjoint representation (52) and look for submodules if we had an ideal, but it's simple.
# Let's try to get a matrix representation directly.
Print("Try to find rep\n");
QUIT_GAP(0);
