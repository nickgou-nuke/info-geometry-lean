theory Isabelle_Fenchel
  imports Main
begin

record legendre_model =
  psi   :: "real ⇒ real"
  phi   :: "real ⇒ real"
  grad  :: "real ⇒ real"

definition is_legendre_model :: "legendre_model ⇒ bool" where
  "is_legendre_model L ≡ 
    (∀θ η. θ * η ≤ psi L θ + phi L η) ∧
    (∀θ. phi L (grad L θ) = θ * grad L θ - psi L θ)"

definition fenchel_gap :: "legendre_model ⇒ real ⇒ real ⇒ real" where
  "fenchel_gap L θ η ≡ psi L θ + phi L η - θ * η"

lemma fenchel_gap_nonneg:
  assumes "is_legendre_model L"
  shows "fenchel_gap L θ η ≥ 0"
proof -
  from assms have "θ * η ≤ psi L θ + phi L η"
    by (simp add: is_legendre_model_def)
  then show ?thesis
    by (simp add: fenchel_gap_def)
qed

lemma fenchel_gap_zero_at_contact:
  assumes "is_legendre_model L"
  shows "fenchel_gap L θ (grad L θ) = 0"
proof -
  from assms have "phi L (grad L θ) = θ * grad L θ - psi L θ"
    by (simp add: is_legendre_model_def)
  then show ?thesis
    by (simp add: fenchel_gap_def)
qed

end
