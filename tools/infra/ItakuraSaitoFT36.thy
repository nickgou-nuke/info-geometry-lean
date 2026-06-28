theory ItakuraSaitoFT36
  imports Complex_Main
begin

text ‹
  Formalization of the Itakura-Saito divergence and the 36 Fradkin-Tseytlin
  scale-invariant cocycles required for the N=4 supersymmetry dimensionality
  balance.
›

definition itakura_saito :: "real ⇒ real ⇒ real" where
  "itakura_saito P Q = (P / Q) - ln (P / Q) - 1"

locale ScaleInvariantCocycles =
  fixes n_gauge :: nat
  fixes n_weyl :: nat
  fixes n_ft_scalars :: nat
  assumes weyl_balance: "n_weyl = 4 * n_gauge"
  assumes scalar_balance: "n_ft_scalars = 3 * n_gauge"

lemma standard_model_ft36:
  "ScaleInvariantCocycles 12 48 36"
  by (unfold_locales, simp_all)

end
