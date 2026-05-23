import InfoGeometry.PositiveMeasure
import InfoGeometry.Stratum.Gauge
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Projective geometry of the positive cone

Defines projective rays, the quotient, and ray-invariance of normalization.
-/



namespace InfoGeometry

namespace PositiveMeasure

variable {α : Type u}

section Projective

noncomputable section
-- Reuse `PosGauge` defined in `InfoGeometry.Stratum.Gauge`
open InfoGeometry.Stratum (PosGauge)

-- SMul instance for the gauge action on positive measures
instance : SMul PosGauge (PositiveMeasure α ℝ) :=
  ⟨fun c μ => scale c.val c.property μ⟩

-- MulAction instance for the gauge action on positive measures
instance : MulAction PosGauge (PositiveMeasure α ℝ) where
  one_smul μ := by
    ext a
    change scale 1 zero_lt_one μ a = μ a
    simp [scale]
  mul_smul c d μ := by
    ext a
    change (c.val * d.val) * μ a = c.val * (d.val * μ a)
    rw [mul_assoc]

/-- `μ` and `ν` lie on the same projective ray iff they differ by the `PosGauge` action. -/
def SameRay (μ ν : PositiveMeasure α ℝ) : Prop := ∃ c : PosGauge, c • μ = ν

/-- The setoid for projectivization, rooted formally in Mathlib's orbit relations. -/
instance sameRaySetoid : Setoid (PositiveMeasure α ℝ) :=
  Setoid.mk SameRay ⟨
    fun μ => ⟨1, by
      ext a
      change scale 1 zero_lt_one μ a = μ a
      simp [scale]⟩,
    fun {μ ν} ⟨c, h⟩ => ⟨c⁻¹, by
      rw [← h]
      ext a
      have hc : (c.val : ℝ) ≠ 0 := ne_of_gt c.property
      calc
        c⁻¹.val * (c.val * μ a)
            = (c⁻¹.val * c.val) * μ a := by rw [mul_assoc]
        _ = μ a := by
              rw [show (c⁻¹.val * c.val) = 1 by
                rw [show c⁻¹.val = (c.val)⁻¹ by rfl]
                exact inv_mul_cancel₀ hc, one_mul]
    ⟩,
    fun {μ ν κ} ⟨c, h₁⟩ ⟨d, h₂⟩ => ⟨d * c, by
      rw [← h₂, ← h₁]
      ext a
      calc
        (d * c).val * μ a = (d.val * c.val) * μ a := rfl
        _ = d.val * (c.val * μ a) := by rw [mul_assoc]
    ⟩
  ⟩

/-- The projectivized positive cone (rays). -/
def Proj := Quotient (sameRaySetoid (α := α))

end
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
