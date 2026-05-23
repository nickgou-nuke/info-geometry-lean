import InfoGeometry.PositiveMeasure
import InfoGeometry.Stratum.Gauge

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

noncomputable section
-- Reuse `PosGauge` defined in `InfoGeometry.Stratum.Gauge`
open InfoGeometry.Stratum (PosGauge)

-- SMul instance for the gauge action on positive measures
instance : SMul PosGauge (PositiveMeasure α ℝ) :=
  ⟨fun c μ => scale c.val c.property μ⟩

-- MulAction instance for the gauge action on positive measures
instance : MulAction PosGauge (PositiveMeasure α ℝ) where
  one_smul μ := by ext a; simp
  mul_smul c d μ := by ext a; simp [smul_smul]


/-- `μ` and `ν` lie on the same projective ray iff they differ by the `PosGauge` action. -/
def SameRay (μ ν : PositiveMeasure α ℝ) : Prop :=
  ∃ c : ℝ, ∃ hc : 0 < c, ν = scale c hc μ

/-- The setoid for projectivization, rooted formally in Mathlib's orbit relations. -/
instance sameRaySetoid : Setoid (PositiveMeasure α ℝ) :=
  MulAction.orbitRel PosGauge (PositiveMeasure α ℝ)

lemma same_ray_iff_orbitRel {μ ν : PositiveMeasure α ℝ} :
    SameRay μ ν ↔ sameRaySetoid.r μ ν := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    let c_gauge : PosGauge := ⟨c, hc⟩
    refine ⟨c_gauge⁻¹, ?_⟩
    ext a
    change c⁻¹ * (c * μ a) = μ a
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  · rintro ⟨c, hc⟩
    refine ⟨(c⁻¹).val, (c⁻¹).property, ?_⟩
    ext a
    have hca : c.val * ν a = μ a := congr_arg (fun (x : PositiveMeasure α ℝ) => x a) hc
    change (c⁻¹).val * μ a = ν a
    rw [← hca, ← mul_assoc, inv_mul_cancel₀ c.property.ne', one_mul]

/-- The projectivized positive cone (rays). -/
def Proj := Quotient (sameRaySetoid (α := α))

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
