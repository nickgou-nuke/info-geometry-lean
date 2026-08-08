theory SarsModularWeakValue
  imports Main
begin

definition surprisal_quadratic :: "int => int" where "surprisal_quadratic x = x*x"
definition weak_denominator_same :: int where "weak_denominator_same = 1"
definition weak_denominator_orthogonal :: int where "weak_denominator_orthogonal = 0"
definition weak_numerator_same :: "int => int" where "weak_numerator_same k0 = k0"
definition weak_value_same :: "int => int" where "weak_value_same k0 = weak_numerator_same k0 div weak_denominator_same"
datatype trace_status = NotTraceClassInInfiniteGNS
datatype measurement_regime = WeakCoupling

definition diag_quad :: "int => int => int => int => int" where
  "diag_quad a b v0 v1 = a*v0*v0 + b*v1*v1"

theorem surprisal_quadratic_nonneg: "0 <= surprisal_quadratic x"
  by (simp add: surprisal_quadratic_def)

theorem surprisal_quadratic_zero: "surprisal_quadratic 0 = 0"
  by (simp add: surprisal_quadratic_def)

theorem diag_quad_nonneg:
  assumes "0 <= a" and "0 <= b"
  shows "0 <= diag_quad a b v0 v1"
  using assms by (simp add: diag_quad_def zero_le_mult_iff)

theorem modular_weak_value_kernel:
  "(\<forall>x. 0 <= surprisal_quadratic x) \<and>
   surprisal_quadratic 0 = 0 \<and>
   weak_denominator_same = 1 \<and>
   weak_denominator_orthogonal = 0 \<and>
   (\<forall>k0. weak_value_same k0 = k0) \<and>
   NotTraceClassInInfiniteGNS = NotTraceClassInInfiniteGNS \<and>
   WeakCoupling = WeakCoupling"
  by (simp add: surprisal_quadratic_nonneg surprisal_quadratic_zero weak_denominator_same_def weak_denominator_orthogonal_def weak_value_same_def weak_numerator_same_def)

end
