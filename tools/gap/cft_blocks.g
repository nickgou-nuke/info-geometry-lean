# Conformal Block Invariant Ratio (Cross-Ratio) Evaluation
# Proves that the cross-ratio x = (z1-z2)*(z3-z4) / ((z1-z3)*(z2-z4))
# is invariant under translation and scaling.

R := Rationals;
z1 := Indeterminate(R, "z1");
z2 := Indeterminate(R, "z2");
z3 := Indeterminate(R, "z3");
z4 := Indeterminate(R, "z4");
c  := Indeterminate(R, "c");
k  := Indeterminate(R, "k");

Print("Defining cross-ratio x = (z1-z2)*(z3-z4) / ((z1-z3)*(z2-z4))\n");
x := (z1 - z2) * (z3 - z4) / ((z1 - z3) * (z2 - z4));
Print("x = ", x, "\n\n");

Print("Evaluating translation: z_i -> z_i + c\n");
z1_c := z1 + c;
z2_c := z2 + c;
z3_c := z3 + c;
z4_c := z4 + c;
x_trans := (z1_c - z2_c) * (z3_c - z4_c) / ((z1_c - z3_c) * (z2_c - z4_c));
Print("x_trans = ", x_trans, "\n");
Print("Proving invariant under translation (x_trans = x): ", x_trans = x, "\n\n");

Print("Evaluating scaling: z_i -> k * z_i\n");
z1_k := k * z1;
z2_k := k * z2;
z3_k := k * z3;
z4_k := k * z4;
x_scale := (z1_k - z2_k) * (z3_k - z4_k) / ((z1_k - z3_k) * (z2_k - z4_k));
Print("x_scale = ", x_scale, "\n");
Print("Proving invariant under scaling (x_scale = x): ", x_scale = x, "\n\n");

QUIT;
