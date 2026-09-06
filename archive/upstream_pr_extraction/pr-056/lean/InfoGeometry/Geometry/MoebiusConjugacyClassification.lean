import InfoGeometry.Topology.MobiusClassification

namespace InfoGeometry.Geometry.MoebiusConjugacyClassification

open InfoGeometry

def negPartner (M : SL2C) : SL2C :=
  ⟨-M.val, by
    simpa [Matrix.det_neg] using M.property⟩

theorem traceSq_neg (M : SL2C) :
    traceSq (negPartner M) = traceSq M := by
  simp [traceSq, negPartner]

theorem isParabolic_neg_iff (M : SL2C) :
    IsParabolic (negPartner M) ↔ IsParabolic M := by
  unfold IsParabolic
  rw [traceSq_neg]
  constructor
  · rintro ⟨htrace, h₁, h₂⟩
    refine ⟨htrace, ?_, ?_⟩
    · intro h
      apply h₂
      change -M.val = -1
      rw [h]
    · intro h
      apply h₁
      change -M.val = 1
      rw [h]
      norm_num
  · rintro ⟨htrace, h₁, h₂⟩
    refine ⟨htrace, ?_, ?_⟩
    · intro h
      apply h₂
      change -M.val = 1 at h
      simpa using congrArg Neg.neg h
    · intro h
      apply h₁
      change -M.val = -1 at h
      simpa using congrArg Neg.neg h

theorem isElliptic_neg_iff (M : SL2C) :
    IsElliptic (negPartner M) ↔ IsElliptic M := by
  unfold IsElliptic
  rw [traceSq_neg]

theorem isHyperbolic_neg_iff (M : SL2C) :
    IsHyperbolic (negPartner M) ↔ IsHyperbolic M := by
  unfold IsHyperbolic
  rw [traceSq_neg]

theorem isLoxodromic_neg_iff (M : SL2C) :
    IsLoxodromic (negPartner M) ↔ IsLoxodromic M := by
  simp [IsLoxodromic, traceSq_neg, isElliptic_neg_iff,
    isHyperbolic_neg_iff]

theorem classification_exhaustive (M : SL2C) :
    M.val = 1 ∨ M.val = -1 ∨ IsParabolic M ∨
      IsElliptic M ∨ IsHyperbolic M ∨ IsLoxodromic M := by
  by_cases htrace : traceSq M = 4
  · by_cases hone : M.val = 1
    · exact Or.inl hone
    · by_cases hneg : M.val = -1
      · exact Or.inr (Or.inl hneg)
      · exact Or.inr (Or.inr (Or.inl ⟨htrace, hone, hneg⟩))
  · by_cases hell : IsElliptic M
    · exact Or.inr (Or.inr (Or.inr (Or.inl hell)))
    · by_cases hhyp : IsHyperbolic M
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hhyp))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨htrace, hell, hhyp⟩))))

theorem not_parabolic_of_loxodromic {M : SL2C}
    (h : IsLoxodromic M) : ¬ IsParabolic M := by
  intro hp
  exact h.1 hp.1

theorem not_elliptic_of_loxodromic {M : SL2C}
    (h : IsLoxodromic M) : ¬ IsElliptic M := h.2.1

theorem not_hyperbolic_of_loxodromic {M : SL2C}
    (h : IsLoxodromic M) : ¬ IsHyperbolic M := h.2.2

theorem not_loxodromic_of_parabolic {M : SL2C}
    (h : IsParabolic M) : ¬ IsLoxodromic M := by
  intro hl
  exact hl.1 h.1

theorem not_loxodromic_of_elliptic {M : SL2C}
    (h : IsElliptic M) : ¬ IsLoxodromic M := by
  intro hl
  exact hl.2.1 h

theorem not_loxodromic_of_hyperbolic {M : SL2C}
    (h : IsHyperbolic M) : ¬ IsLoxodromic M := by
  intro hl
  exact hl.2.2 h

theorem mobius_noncentral_classification_disjoint {M : SL2C} :
    IsParabolic M → ¬ IsElliptic M ∧ ¬ IsHyperbolic M ∧ ¬ IsLoxodromic M := by
  intro hp
  exact ⟨not_elliptic_of_parabolic hp,
    not_hyperbolic_of_parabolic hp, not_loxodromic_of_parabolic hp⟩

end InfoGeometry.Geometry.MoebiusConjugacyClassification
