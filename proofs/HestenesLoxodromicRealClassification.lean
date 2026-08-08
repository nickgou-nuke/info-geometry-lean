import proofs.HestenesLoxodromicCasimirs

/-!
# Real elliptic/hyperbolic/parabolic classification

The commuting one-axis loxodromic sector has real parameters `η, θ`.  Its
nonzero elliptic and hyperbolic sectors are classified by the scalar Casimir
when the pseudoscalar Casimir vanishes.  A nonzero parabolic element is proved
impossible in this restricted two-parameter sector; genuine parabolic
bivectors require a larger, non-simple bivector carrier.
-/

namespace HestenesLoxodromicRealClassification

 def scalarCasimir (η θ : ℝ) : ℝ := η ^ 2 - θ ^ 2
 def pseudoscalarCasimir (η θ : ℝ) : ℝ := 2 * η * θ

 def IsElliptic (η θ : ℝ) : Prop :=
  pseudoscalarCasimir η θ = 0 ∧ scalarCasimir η θ < 0

 def IsHyperbolic (η θ : ℝ) : Prop :=
  pseudoscalarCasimir η θ = 0 ∧ scalarCasimir η θ > 0

 def IsParabolic (η θ : ℝ) : Prop :=
  pseudoscalarCasimir η θ = 0 ∧ scalarCasimir η θ = 0 ∧ (η ≠ 0 ∨ θ ≠ 0)

 def IsLoxodromic (η θ : ℝ) : Prop :=
  pseudoscalarCasimir η θ ≠ 0

 theorem pure_rotation_isElliptic {θ : ℝ} (hθ : θ ≠ 0) :
    IsElliptic 0 θ := by
  unfold IsElliptic scalarCasimir pseudoscalarCasimir
  constructor
  · ring
  · nlinarith [sq_pos_of_ne_zero hθ]

 theorem pure_boost_isHyperbolic {η : ℝ} (hη : η ≠ 0) :
    IsHyperbolic η 0 := by
  unfold IsHyperbolic scalarCasimir pseudoscalarCasimir
  constructor
  · ring
  · nlinarith [sq_pos_of_ne_zero hη]

 theorem nonzero_pure_sector_classification {η θ : ℝ}
    (hηθ : η * θ = 0) (hne : η ≠ 0 ∨ θ ≠ 0) :
    IsElliptic η θ ∨ IsHyperbolic η θ := by
  unfold IsElliptic IsHyperbolic scalarCasimir pseudoscalarCasimir
  rcases hne with hη | hθ
  · have hθ0 : θ = 0 := by
      exact (mul_eq_zero.mp hηθ).resolve_left hη
    right
    constructor
    · simp [hθ0]
    · rw [hθ0]
      simpa using (sq_pos_of_ne_zero hη)
  · have hη0 : η = 0 := by
      exact (mul_eq_zero.mp hηθ).resolve_right hθ
    left
    constructor
    · simp [hη0]
    · rw [hη0]
      simpa using (neg_lt_zero.mpr (sq_pos_of_ne_zero hθ))

 theorem nonzero_parabolic_impossible {η θ : ℝ} :
    ¬ IsParabolic η θ := by
  intro h
  unfold IsParabolic scalarCasimir pseudoscalarCasimir at h
  rcases h with ⟨hp, hs, hne⟩
  rcases hne with hη | hθ
  · have hprod : η * θ = 0 := by nlinarith [hp]
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact hη hzero
    · subst θ
      norm_num at hs
      exact hη hs
  · have hprod : η * θ = 0 := by nlinarith [hp]
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · subst η
      norm_num at hs
      exact hθ hs
    · exact hθ hzero

 theorem loxodromic_of_pseudoscalar_ne_zero {η θ : ℝ}
    (h : pseudoscalarCasimir η θ ≠ 0) :
    IsLoxodromic η θ := h

end HestenesLoxodromicRealClassification
