import InfoGeometry.Thermo.Gibbs

/-!
# Logarithmic deformation coordinates

The Boolean `gradedSign` layer and the thermodynamic deformation scale are
different data.  This owner uses the explicit name `deformationScale` for the
positive real scale and records only the elementary exponential identities
needed by the finite Gibbs layer.
-/

noncomputable section

namespace InfoGeometry.Thermo

/-- Multiplicative activity coordinate associated with a logarithmic generator. -/
def exponentialActivity (generator deformationScale : ℝ) : ℝ :=
  Real.exp (generator / deformationScale)

theorem exponentialActivity_pos (generator deformationScale : ℝ) :
    0 < exponentialActivity generator deformationScale := by
  unfold exponentialActivity
  exact Real.exp_pos _

theorem exponentialActivity_ne_zero (generator deformationScale : ℝ) :
    exponentialActivity generator deformationScale ≠ 0 :=
  (exponentialActivity_pos generator deformationScale).ne'

theorem log_exponentialActivity (generator deformationScale : ℝ) :
    Real.log (exponentialActivity generator deformationScale) =
      generator / deformationScale := by
  unfold exponentialActivity
  exact Real.log_exp _

theorem exponentialActivity_mul
    (x y deformationScale : ℝ) :
    exponentialActivity x deformationScale * exponentialActivity y deformationScale =
      exponentialActivity (x + y) deformationScale := by
  unfold exponentialActivity
  rw [← Real.exp_add]
  congr 1
  ring

theorem exponentialActivity_add_sub
    (generator offset deformationScale : ℝ) :
    exponentialActivity generator deformationScale *
        exponentialActivity (-offset) deformationScale =
      exponentialActivity (generator - offset) deformationScale := by
  rw [exponentialActivity_mul]
  congr 1

/-- A positive multiplicative dilation is an additive logarithmic shift. -/
theorem exponentialActivity_log_shift
    (generator deformationScale scaleFactor : ℝ)
    (hscale : deformationScale ≠ 0) (hscaleFactor : 0 < scaleFactor) :
    exponentialActivity
        (generator + deformationScale * Real.log scaleFactor) deformationScale =
      scaleFactor * exponentialActivity generator deformationScale := by
  unfold exponentialActivity
  have harg :
    (generator + deformationScale * Real.log scaleFactor) / deformationScale =
        generator / deformationScale + Real.log scaleFactor := by
    field_simp [hscale]
  rw [harg, Real.exp_add, Real.exp_log hscaleFactor]
  ring

theorem gibbsWeight_eq_exponentialActivity
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (energy : Ω → ℝ) (deformationScale : ℝ) (ω : Ω) :
    weight energy deformationScale ω =
      exponentialActivity (-energy ω) deformationScale := by
  rfl

end InfoGeometry.Thermo
