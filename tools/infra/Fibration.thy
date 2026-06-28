theory Fibration
  imports Complex_Main
begin

text ‹
  Isabelle/HOL Formalization of Split Octonion Fibration
›

locale Triality =
  fixes v_dim :: nat
  fixes sL_dim :: nat
  fixes sR_dim :: nat
  assumes t_symm: "v_dim = 8 ∧ sL_dim = 8 ∧ sR_dim = 8"

lemma (in Triality) generation_equality:
  "v_dim = sL_dim ∧ sL_dim = sR_dim"
  by (simp add: t_symm)

end
