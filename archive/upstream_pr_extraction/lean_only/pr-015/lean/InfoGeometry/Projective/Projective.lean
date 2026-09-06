import InfoGeometry.PositiveMeasure

/-!
# Projective geometry of the positive cone

Defines projective rays, the quotient, and ray-invariance of normalization.
-/

namespace InfoGeometry.Projective.Projective
end InfoGeometry.Projective.Projective

namespace InfoGeometry

namespace PositiveMeasure

variable {α : Type u}

section Projective

/-- `μ` and `ν` lie on the same projective ray iff `ν = c • μ` for some `c>0`. -/
def SameRay (μ ν : PositiveMeasure α ℝ) : Prop :=
  ∃ c : ℝ, ∃ hc : 0 < c, ν = scale c hc μ

lemma SameRay.refl (μ : PositiveMeasure α ℝ) : SameRay μ μ := by
  refine ⟨1, one_pos, ?_⟩
  ext a
  simp [scale]

lemma SameRay.symm {μ ν : PositiveMeasure α ℝ} (h : SameRay μ ν) : SameRay ν μ := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_pos.2 hc, ?_⟩
  ext a
  simp [scale, hc.ne']

lemma SameRay.trans {μ ν κ : PositiveMeasure α ℝ} (h₁ : SameRay μ ν) (h₂ : SameRay ν κ) :
    SameRay μ κ := by
  rcases h₁ with ⟨c₁, hc₁, rfl⟩
  rcases h₂ with ⟨c₂, hc₂, rfl⟩
  refine ⟨c₂ * c₁, mul_pos hc₂ hc₁, ?_⟩
  ext a
  simp [scale, mul_assoc]

/-- The setoid for projectivization. -/
instance : Setoid (PositiveMeasure α ℝ) where
  r := SameRay
  iseqv := by
    refine ⟨SameRay.refl, ?_, ?_⟩
    · intro x y hxy
      exact SameRay.symm hxy
    · intro x y z hxy hyz
      exact SameRay.trans hxy hyz

/-- The projectivized cone (rays). -/
def Proj := Quotient (inferInstance : Setoid (PositiveMeasure α ℝ))

end Projective

section Gauge
variable [Fintype α]

/-- `Z` is homogeneous: `Z(c•μ)=c*Z(μ)` for `c>0`. -/
@[simp]
lemma Z_scale (c : ℝ) (hc : 0 < c) (μ : PositiveMeasure α ℝ) :
    Z (α := α) (R := ℝ) (scale c hc μ) = c * Z (α := α) (R := ℝ) μ := by
  classical
  simp [PositiveMeasure.Z, scale, Finset.mul_sum]

end Gauge

section NormalizeGauge
variable [Fintype α] [Nonempty α]

/-- Normalization is ray-invariant: fixing the simplex gauge kills scaling freedom. -/
@[simp]
lemma normalize_scale (c : ℝ) (hc : 0 < c) (μ : PositiveMeasure α ℝ) :
    normalize (α := α) (R := ℝ) (scale c hc μ) = normalize (α := α) (R := ℝ) μ := by
  ext a
  change (scale c hc μ a) / Z (α := α) (R := ℝ) (scale c hc μ) = μ a / Z (α := α) (R := ℝ) μ
  rw [scale_apply, Z_scale]
  field_simp [hc.ne', Z_ne_zero (α := α) (R := ℝ) μ]

end NormalizeGauge
end PositiveMeasure

end InfoGeometry
