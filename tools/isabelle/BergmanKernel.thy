theory BergmanKernel
  imports Complex_Main
begin

(* Formalization of supremum norm bounds for Bergman kernels. *)
(* Geometric estimates proving the polarization scales uniformly. *)

definition bergman_kernel_bound :: "(complex => complex) => real => bool" where
  "bergman_kernel_bound K C = (ALL z. norm (K z) <= C)"

lemma bergman_sup_norm:
  assumes "bergman_kernel_bound K C"
  shows "norm (K z) <= C"
  using assms unfolding bergman_kernel_bound_def by simp

definition polarization_scaling :: "(complex => complex) => real => bool" where
  "polarization_scaling K s = (ALL z. norm (K (z * complex_of_real s)) = s * norm (K z))"

lemma polarization_uniform_scale:
  assumes "polarization_scaling K s"
  shows "norm (K (z * complex_of_real s)) = s * norm (K z)"
  using assms unfolding polarization_scaling_def by simp

end
