theory Zorn_Determinant_Ratio_Flow_Scaling
  imports Main
begin

definition detZ ::
  "'a::comm_ring => 'a => 'a => 'a => 'a => 'a => 'a => 'a => 'a" where
  "detZ a b u1 u2 u3 v1 v2 v3 =
    a * b - (u1 * v1 + u2 * v2 + u3 * v3)"

lemma detZ_scale:
  fixes r a b u1 u2 u3 v1 v2 v3 :: "'a::comm_ring"
  shows "detZ (r*a) (r*b) (r*u1) (r*u2) (r*u3) (r*v1) (r*v2) (r*v3) =
    r*r * detZ a b u1 u2 u3 v1 v2 v3"
  by (simp add: detZ_def algebra_simps)

lemma common_scaling_ratio_cleared:
  fixes r a b u1 u2 u3 v1 v2 v3 c d x1 x2 x3 y1 y2 y3 :: "'a::comm_ring"
  shows "detZ (r*c) (r*d) (r*x1) (r*x2) (r*x3) (r*y1) (r*y2) (r*y3) *
      detZ a b u1 u2 u3 v1 v2 v3 =
    detZ c d x1 x2 x3 y1 y2 y3 *
      detZ (r*a) (r*b) (r*u1) (r*u2) (r*u3) (r*v1) (r*v2) (r*v3)"
  by (simp add: detZ_def algebra_simps)

lemma unequal_scaling_ratio_factor_cleared:
  fixes s t a b u1 u2 u3 v1 v2 v3 c d x1 x2 x3 y1 y2 y3 :: "'a::comm_ring"
  shows "s*s * detZ (t*c) (t*d) (t*x1) (t*x2) (t*x3) (t*y1) (t*y2) (t*y3) *
      detZ a b u1 u2 u3 v1 v2 v3 =
    t*t * detZ c d x1 x2 x3 y1 y2 y3 *
      detZ (s*a) (s*b) (s*u1) (s*u2) (s*u3) (s*v1) (s*v2) (s*v3)"
  by (simp add: detZ_def algebra_simps)

end
