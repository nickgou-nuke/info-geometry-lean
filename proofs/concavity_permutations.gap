# GAP Script for Concavity Permutations

# Define variables for coordinates
x1 := Indeterminate(Rationals, "x1");
y1 := Indeterminate(Rationals, "y1");
x2 := Indeterminate(Rationals, "x2");
y2 := Indeterminate(Rationals, "y2");
x3 := Indeterminate(Rationals, "x3");
y3 := Indeterminate(Rationals, "y3");

# The determinant formula for the 3x3 orientation matrix
det := x1*y2 - x1*y3 - y1*x2 + y1*x3 + x2*y3 - x3*y2;

# Symmetric group on 3 elements
S3 := SymmetricGroup(3);

# Action of permutation on determinant
# A permutation acts by swapping the indices of the coordinates.
# We will demonstrate the sign swap by evaluating permutations.

Print("Original determinant: ", det, "\n");

# For (1,2) -> swap p1 and p2 -> x1<->x2, y1<->y2
det_12 := x2*y1 - x2*y3 - y2*x1 + y2*x3 + x1*y3 - x3*y1;
Print("Under permutation (1,2): ", det_12, "\n");
Print("Is det_12 = -det? ", det_12 = -det, "\n");

# For (1,2,3) -> p1->p2, p2->p3, p3->p1 -> x1->x2, x2->x3, x3->x1, y1->y2, y2->y3, y3->y1
det_123 := x2*y3 - x2*y1 - y2*x3 + y2*x1 + x3*y1 - x1*y3;
Print("Under permutation (1,2,3): ", det_123, "\n");
Print("Is det_123 = det? ", det_123 = det, "\n");
