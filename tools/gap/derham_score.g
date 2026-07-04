# derham_score.g
# Programmatically construct the discrete algebraic matrix evaluating the closed score states
# Evaluate the invariant 1-forms computationally

Print("Constructing the discrete algebraic matrix for evaluating closed score states...\n");

# Define the differential map d0 for a simple simplicial complex (a triangle)
# Vertices: 1, 2, 3. Edges: (1,2), (2,3), (3,1)
# d0: C^0 -> C^1
d0 := [
  [-1,  1,  0],
  [ 0, -1,  1],
  [ 1,  0, -1]
];

Print("Discrete algebraic matrix (d0):\n");
Display(d0);

# The image of d0 corresponds to exact 1-forms
exact_1_forms := VectorSpace(Rationals, d0);
Print("Dimension of exact 1-forms space: ", Dimension(exact_1_forms), "\n");

# The closed 1-forms are the kernel of d1. Since there are no 2-cells, C^2 = {0}.
# Thus all 1-forms are closed.
# Let's define the full space of 1-forms C1:
C1 := VectorSpace(Rationals, [ [1,0,0], [0,1,0], [0,0,1] ]);
Print("Dimension of closed 1-forms (kernel of d1): ", Dimension(C1), "\n");

# Evaluate invariant 1-forms (De Rham cohomology H^1)
# H^1 = (Closed 1-forms) / (Exact 1-forms)
dim_H1 := Dimension(C1) - Dimension(exact_1_forms);
Print("Evaluating invariant 1-forms computationally...\n");
Print("Dimension of invariant 1-forms (H^1): ", dim_H1, "\n");
Print("Evaluation successful.\n");

QUIT;
