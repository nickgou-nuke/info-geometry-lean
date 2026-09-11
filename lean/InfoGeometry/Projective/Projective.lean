import InfoGeometry.PositiveMeasure
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

lemma SameRay.refl (μ : PositiveMeasure α ℝ) : SameRay μ μ := by
  refine ⟨⟨1, zero_lt_one⟩, ?_⟩
  ext a
  change (1 : ℝ) * μ a = μ a
  ring

lemma SameRay.symm {μ ν : PositiveMeasure α ℝ} (h : SameRay μ ν) : SameRay ν μ := by
  rcases h with ⟨c, hc⟩
  refine ⟨⟨c.1⁻¹, inv_pos.mpr c.2⟩, ?_⟩
  ext a
  have hc' : c.1 * μ a = ν a := by
    simpa [SMul.smul, PositiveMeasure.scale] using congrArg (fun m => m a) hc
  calc
    c.1⁻¹ * ν a = c.1⁻¹ * (c.1 * μ a) := by rw [hc']
    _ = μ a := by field_simp [c.2.ne']

lemma SameRay.trans {μ ν κ : PositiveMeasure α ℝ}
    (h₁ : SameRay μ ν) (h₂ : SameRay ν κ) : SameRay μ κ := by
  rcases h₁ with ⟨c, hc⟩
  rcases h₂ with ⟨d, hd⟩
  refine ⟨⟨d.1 * c.1, mul_pos d.2 c.2⟩, ?_⟩
  ext a
  have hc' : c.1 * μ a = ν a := by
    simpa [SMul.smul, PositiveMeasure.scale] using congrArg (fun m => m a) hc
  have hd' : d.1 * ν a = κ a := by
    simpa [SMul.smul, PositiveMeasure.scale] using congrArg (fun m => m a) hd
  calc
    (d.1 * c.1) * μ a = d.1 * (c.1 * μ a) := by ring
    _ = d.1 * ν a := by rw [hc']
    _ = κ a := by rw [hd']

/-- The projectivized positive cone (rays). -/
def Proj := Quotient (sameRaySetoid (α := α))

namespace Projective

lemma same_ray_refl (μ : PositiveMeasure α ℝ) : PositiveMeasure.SameRay μ μ :=
  PositiveMeasure.SameRay.refl μ

lemma same_ray_symm {μ ν : PositiveMeasure α ℝ} (h : PositiveMeasure.SameRay μ ν) :
    PositiveMeasure.SameRay ν μ :=
  PositiveMeasure.SameRay.symm h

lemma same_ray_trans {μ ν κ : PositiveMeasure α ℝ}
    (h₁ : PositiveMeasure.SameRay μ ν) (h₂ : PositiveMeasure.SameRay ν κ) :
    PositiveMeasure.SameRay μ κ :=
  PositiveMeasure.SameRay.trans h₁ h₂

end Projective

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
