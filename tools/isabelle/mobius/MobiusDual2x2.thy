theory MobiusDual2x2
  imports Complex_Main
begin

definition pairing :: "rat => rat => rat => rat => rat" where
  "pairing e1 e2 x y = e1 * x + e2 * y"

definition fixed_poly :: "rat => rat => rat => rat => rat => rat" where
  "fixed_poly a b c d z = c * z^2 + (d - a) * z - b"

definition multiplier_at_zero :: "rat => rat => rat" where
  "multiplier_at_zero c d = 1 / (d^2)"

definition multiplier_at_infinity :: "rat => rat" where
  "multiplier_at_infinity a = 1 / (a^2)"

theorem hyperbolic_pairing_example:
  "pairing ((1/2) * 3 - 0 * 5) (- 0 * 3 + 2 * 5) (2 * 7 + 0 * 11) (0 * 7 + (1/2) * 11) = pairing 3 5 7 11"
  by (simp add: pairing_def)

theorem hyperbolic_fixed_zero:
  "fixed_poly 2 0 0 (1/2) 0 = 0"
  by (simp add: fixed_poly_def)

theorem hyperbolic_fixed_polynomial_factor:
  "fixed_poly 2 0 0 (1/2) z = (-3/2) * z"
  by (simp add: fixed_poly_def algebra_simps)

theorem hyperbolic_multiplier_zero_readback:
  "multiplier_at_zero 0 (1/2) = 1 / ((1/2)^2)"
  by (simp add: multiplier_at_zero_def)

theorem hyperbolic_multiplier_infinity_readback:
  "multiplier_at_infinity 2 = 1 / (2^2)"
  by (simp add: multiplier_at_infinity_def)

end
