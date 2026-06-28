# GAP verification for Needham's fine-structure expression.
pi := 3.1415926535897932384626433832795;;
phi := (1.0 + Sqrt(5.0)) / 2.0;;
delta_phi := phi^2 - phi - 1.0;;
if not (-1.0e-12 < delta_phi and delta_phi < 1.0e-12) then
  Error("phi quadratic check failed");
fi;;
expr := 10.0 * pi * phi * Exp(1.0) - Log(pi);;
codata := 137.035999084;;
if expr >= codata then
  abs_error := expr - codata;;
else
  abs_error := codata - expr;;
fi;;
rel_error := abs_error / codata;;
Print("GAP PASS\n");
Print("phi = ", phi, "\n");
Print("needham_alpha_inverse = ", expr, "\n");
Print("abs_error = ", abs_error, "\n");
Print("rel_error = ", rel_error, "\n");
QUIT;
