theory TKKFramework
  imports CausalFunctor "HOL-Algebra.Ring"
begin

locale info_geo_fermi = einstein_causality +
  fixes TKK_metric :: "'a ⇒ 'a ⇒ real"
    and fermi_op :: "'a ⇒ 'a"
    and gamow_teller_op :: "'a ⇒ 'a"
  assumes fermi_isometry:
    "x ∈ carrier colimit_ring ⟹ y ∈ carrier colimit_ring ⟹
     TKK_metric (fermi_op x) (fermi_op y) = TKK_metric x y"
  assumes gamow_teller_deformation:
    "x ∈ carrier colimit_ring ⟹ y ∈ carrier colimit_ring ⟹
     TKK_metric (gamow_teller_op x) (gamow_teller_op y) ≠ TKK_metric x y"
begin

lemma fermi_metric_preservation:
  assumes "x ∈ carrier colimit_ring"
    and "y ∈ carrier colimit_ring"
  shows "TKK_metric (fermi_op x) (fermi_op y) = TKK_metric x y"
  using assms fermi_isometry by simp

end
end
