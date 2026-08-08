theory ZetaRegularizedDeterminant
  imports Main
begin

typedecl operator

axiomatization
  zeta_det :: "operator \<Rightarrow> real" and
  tensor_prod :: "operator \<Rightarrow> operator \<Rightarrow> operator" (infixl "\<otimes>" 70) and
  neg_log_zeta_det :: "operator \<Rightarrow> real" and
  dim :: "operator \<Rightarrow> real" and
  ln_axiomatized :: "real \<Rightarrow> real"
where
  neg_log_zeta_det_def: "neg_log_zeta_det A = - (ln_axiomatized (zeta_det A))" and
  zeta_det_tensor_prod: "ln_axiomatized (zeta_det (A \<otimes> B)) = dim B * ln_axiomatized (zeta_det A) + dim A * ln_axiomatized (zeta_det B)"

lemma neg_log_zeta_det_additivity:
  shows "neg_log_zeta_det (A \<otimes> B) = dim B * neg_log_zeta_det A + dim A * neg_log_zeta_det B"
  unfolding neg_log_zeta_det_def
  by (simp add: zeta_det_tensor_prod algebra_simps)

end
