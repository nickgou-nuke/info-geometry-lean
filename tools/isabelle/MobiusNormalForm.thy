theory MobiusNormalForm
  imports Main
begin

locale MobiusMatrix =
  fixes k :: "'a::comm_ring_1"
    and g1 :: "'a"
    and g2 :: "'a"
begin

definition a :: "'a" where "a = g1 - k * g2"
definition b :: "'a" where "b = (k - 1) * g1 * g2"
definition c :: "'a" where "c = 1 - k"
definition d :: "'a" where "d = k * g1 - g2"

lemma det_factorization:
  "a * d - b * c = k * (g1 - g2)^2"
  unfolding a_def b_def c_def d_def
  by (simp add: algebra_simps power2_eq_square)

end

end
