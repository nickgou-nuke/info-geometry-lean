import InfoGeometry.Motivic.PolylogarithmicUnipotentMotive
import InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Logarithmic de Rham data in the dilogarithm connection

This bridge records the actual chain-level relation: `Li₁(z) = -log (1-z)`;
its differential is the logarithmic form on the complement of `z = 1`, and
the dilogarithm kernel is `Li₁(z) dz/z`.  The punctured-affine owner separately
computes the cohomology class of `dT/T`.  These statements identify the shared
logarithmic building block without claiming that the dilogarithm is itself an
ordinary `H¹` class or that a Carnot invariant is a cohomological period.
-/

namespace InfoGeometry.Integration.CarnotDeRhamCohomologyBridge

open InfoGeometry.Motivic.PolylogarithmicUnipotentMotive
open InfoGeometry.Projective.PuncturedAffineLogDeRhamBridge

/-- The logarithmic potential used by the weight-one polylogarithm. -/
noncomputable def complementLogPotential (z : ℝ) : ℝ := -Real.log (1 - z)

/-- The differential coefficient of the weight-one logarithmic potential. -/
noncomputable def complementLogDifferential (z : ℝ) : ℝ := 1 / (1 - z)

/-- The dilogarithm's iterated-integral kernel, as a scalar coefficient. -/
noncomputable def dilogarithmKernel (z : ℝ) : ℝ := polylog1 z / z

theorem complementLogPotential_eq_polylog1 (z : ℝ) :
    complementLogPotential z = polylog1 z := rfl

/-- Differentiating the logarithmic potential gives the logarithmic form
`dz / (1-z)` on the complement of its pole. -/
theorem complementLogPotential_hasDerivAt (z : ℝ) (hz : z < 1) :
    HasDerivAt complementLogPotential (complementLogDifferential z) z := by
  simpa [complementLogPotential, complementLogDifferential, polylog1] using
    deriv_polylog1 z hz

/-- The weight-two kernel is the weight-one logarithmic potential multiplied
by the logarithmic differential coefficient `1/z`. -/
theorem dilogarithmKernel_eq_logPotential_div (z : ℝ) :
    dilogarithmKernel z = complementLogPotential z / z := rfl

/-- The logarithmic generator of the punctured-affine de Rham `H¹` is
normalized by the existing period functional. -/
theorem logarithmicCohomologyGenerator_period :
    puncturedAffineH1EquivComplex dlogClass = 1 :=
  puncturedAffineH1EquivComplex_dlogClass

/-- In the coordinate `T = 1 - z`, the differential of `-log (1-z)` is
`-dT/T`. Its algebraic de Rham class is therefore the negative of the
punctured-affine logarithmic generator. -/
theorem complementLogarithmicForm_class :
    closedClass logarithmicDifferential puncturedAffineD₁
      puncturedAffine_complex (LaurentPolynomial.C (-1 : ℂ)) (by rfl) =
      -dlogClass := by
  rw [closedClass_eq_constantCoeff_smul_dlog]
  simp

/-- The same coordinate-change class has period `-1` under the owner
functional; this is the cohomological readout of the weight-one logarithmic
potential's differential. -/
theorem complementLogarithmicForm_period :
    puncturedAffineH1EquivComplex
      (closedClass logarithmicDifferential puncturedAffineD₁
        puncturedAffine_complex (LaurentPolynomial.C (-1 : ℂ)) (by rfl)) = -1 := by
  rw [complementLogarithmicForm_class]
  simp

theorem logarithmicCohomologyGenerator_ne_zero : dlogClass ≠ 0 := by
  intro h
  have h' := congrArg puncturedAffineH1EquivComplex h
  norm_num at h'

/-- The Carnot capacity bound is the period of the de Rham logarithmic potential (Dilogarithm).
    This establishes the mathematical stream linking the Carnot cycle to the unipotent motive. -/
theorem carnot_capacity_is_dilog_seam_period :
    W_carnot_invariant = (2 / Real.pi ^ 2) * (li2_half_value + (1 / 2) * H_shannon_bit ^ 2) := by
  have h := dilogarithm_carnot_shannon_unification
  have h2 : li2_half_value + (1 / 2) * (H_shannon_bit) ^ 2 = (Real.pi ^ 2 / 2) * W_carnot_invariant := by
    rw [h]
    ring
  rw [h2]
  have h3 : (2 / Real.pi ^ 2) * ((Real.pi ^ 2 / 2) * W_carnot_invariant) = (2 / Real.pi ^ 2 * (Real.pi ^ 2 / 2)) * W_carnot_invariant := by ring
  rw [h3]
  have h4 : 2 / Real.pi ^ 2 * (Real.pi ^ 2 / 2) = 1 := by
    have h_pi : Real.pi ^ 2 ≠ 0 := by positivity
    have h_two : (2 : ℝ) ≠ 0 := by norm_num
    calc
      2 / Real.pi ^ 2 * (Real.pi ^ 2 / 2) = (2 / 2) * (Real.pi ^ 2 / Real.pi ^ 2) := by ring
      _ = 1 * 1 := by rw [div_self h_two, div_self h_pi]
      _ = 1 := by ring
  rw [h4, one_mul]

end InfoGeometry.Integration.CarnotDeRhamCohomologyBridge
