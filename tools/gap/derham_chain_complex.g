# derham_chain_complex.g
# Define the homology/cohomology group H^1_dR algebraically using GAP.
# Construct a simple chain complex representing a punctured Riemann surface
# (e.g., a twice-punctured plane or a punctured torus, which retracts to a wedge of two circles).

Print("Constructing chain complex for a punctured Riemann surface...\n");

# Let's use a 1D graph with 2 vertices and 3 edges (figure-8 graph with 2 vertices)
# Vertices: v1, v2
# Edges: e1 (v1 -> v2), e2 (v1 -> v2), e3 (v2 -> v1)
# C_0 is 2-dimensional.
# C_1 is 3-dimensional.

# The chain boundary \partial_1: C_1 -> C_0
# e1 -> v2 - v1
# e2 -> v2 - v1
# e3 -> v1 - v2
# In GAP, row vectors multiply from the left.
P1 := [
  [-1,  1],
  [-1,  1],
  [ 1, -1]
];

Print("Chain boundary matrix P1 (C_1 -> C_0):\n");
Display(P1);

# Coboundary d^0: C^0 \to C^1
# For cochains, the matrix is the transpose of P1.
D0 := TransposedMat(P1);

Print("Coboundary matrix D0 (C^0 -> C^1):\n");
Display(D0);

# Exact 1-forms are the image of D0 (row space of D0)
exact_1_forms := VectorSpace(Rationals, D0);
Print("Dimension of exact 1-forms (B^1): ", Dimension(exact_1_forms), "\n");

# Closed 1-forms are kernel of d^1. Since C^2 = 0, D1 = 0, all 1-forms are closed.
# The space of closed 1-forms Z^1 is C^1.
Z1 := VectorSpace(Rationals, [ [1,0,0], [0,1,0], [0,0,1] ]);
Print("Dimension of closed 1-forms (Z^1): ", Dimension(Z1), "\n");

# The first de Rham cohomology group H^1_dR is Z^1 / B^1.
dim_H1 := Dimension(Z1) - Dimension(exact_1_forms);
Print("Dimension of first de Rham cohomology group H^1_dR: ", dim_H1, "\n");

Print("The non-zero dimension of H^1_dR isolating the first cohomology group maps the score function potentials.\n");

QUIT;
