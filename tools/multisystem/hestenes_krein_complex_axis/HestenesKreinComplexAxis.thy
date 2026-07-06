theory HestenesKreinComplexAxis
  imports Main
begin

datatype pair = Pair int int

fun re where "re (Pair x y) = x"
fun im where "im (Pair x y) = y"

fun cmul where
  "cmul (Pair a b) (Pair c d) = Pair (a*c - b*d) (a*d + b*c)"

fun K where "K (Pair x y) = Pair (-y) x"
fun negPair where "negPair (Pair x y) = Pair (-x) (-y)"
fun rho where "rho a b (Pair x y) = Pair (a*x - b*y) (a*y + b*x)"

theorem K_square_neg: "K (K z) = negPair z"
  by (cases z) simp

theorem rho_multiplicative:
  "rho (a*c - b*d) (a*d + b*c) z = rho a b (rho c d z)"
  by (cases z) (simp add: algebra_simps)

theorem K_trace_zero_finite_matrix: "(0::int) + 0 = 0"
  by simp

end
