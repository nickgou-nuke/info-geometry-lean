# Wareham Conformal Geometric Algebra in GAP

F := Rationals;;
A := FreeAlgebra( F, ["e1", "e2", "e", "e_bar"] );;
e1 := A.1;; e2 := A.2;; e := A.3;; e_bar := A.4;;

# Defining null vectors for the point at infinity and origin
n := e + e_bar;;
n_bar := e - e_bar;;

# Point representation
# F(x) = 1/2(x^2 n + 2x - n_bar)
# Note: For GAP we implement this as a function of the vector and its scalar square
F_point := function(x, x_sq)
  return 1/2 * (x_sq * n + 2 * x - n_bar);
end;;

# Circle Dual representation
# C* = B - 1/2 rho^2 n
circle_dual := function(B, rho)
  return B - 1/2 * rho^2 * n;
end;;

Print("GAP CGA definitions loaded.\n");
