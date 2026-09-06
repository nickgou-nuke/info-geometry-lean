import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFiniteDifference
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fréchet--Duhamel identification for the Banach-algebra exponential

The finite-difference owner proves the exact identity along the
interaction-picture path.  This owner performs the remaining analytic step:
the insertion kernel is jointly continuous in the real perturbation parameter
and the interval variable, hence its Bochner interval integral is continuous.
The exact divided differences therefore converge to the unperturbed Duhamel
integral.

Uniqueness of the real Fréchet derivative then identifies Mathlib's
changed-origin exponential derivative with the Duhamel operator.  No
commutativity, trace, spectral decomposition, or finite-dimensionality
assumption is used.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra

open MeasureTheory
open scoped Interval

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/--
The unscaled insertion integral in the exact finite-difference formula.
At perturbation parameter zero it is the Duhamel derivative applied to h.
-/
noncomputable def duhamelDifferenceQuotient
    (a h : A) (r : ℝ) : A :=
  ∫ s in (0 : ℝ)..1, duhamelFiniteDifferenceIntegrand a h r s

/--
The parameter-dependent insertion integral is continuous in the real
perturbation parameter.
-/
theorem continuous_duhamelDifferenceQuotient (a h : A) :
    Continuous (duhamelDifferenceQuotient a h) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
  unfold duhamelFiniteDifferenceIntegrand
  fun_prop

/-- At zero perturbation, the difference quotient integral is D exp_a[h]. -/
theorem duhamelDifferenceQuotient_zero (a h : A) :
    duhamelDifferenceQuotient a h 0 =
      duhamelDerivative a h := by
  rw [duhamelDerivative_apply_integral]
  rfl

/--
Exact finite-difference formula with the scalar perturbation pulled outside
the Bochner interval integral.
-/
theorem exp_add_smul_sub_exp_eq_smul_duhamelDifferenceQuotient
    (a h : A) (r : ℝ) :
    NormedSpace.exp (a + r • h) - NormedSpace.exp a =
      r • duhamelDifferenceQuotient a h r := by
  calc
    NormedSpace.exp (a + r • h) - NormedSpace.exp a =
        ∫ s in (0 : ℝ)..1,
          r • duhamelFiniteDifferenceIntegrand a h r s :=
      (integral_duhamelFiniteDifference_eq_exp_sub_exp a h r).symm
    _ = r • duhamelDifferenceQuotient a h r := by
      rw [intervalIntegral.integral_smul]
      rfl

/--
The exponential along the real affine line a + r h has the Duhamel
directional derivative at zero.
-/
theorem hasDerivAt_exp_affine_duhamel (a h : A) :
    HasDerivAt
      (fun r : ℝ => NormedSpace.exp (a + r • h))
      (duhamelDerivative a h) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  rw [← duhamelDifferenceQuotient_zero a h]
  refine
    ((continuous_duhamelDifferenceQuotient a h).continuousAt.mono_left
      inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hr
  simp only [zero_add, zero_smul, add_zero]
  rw [exp_add_smul_sub_exp_eq_smul_duhamelDifferenceQuotient]
  simp [smul_smul, hr0]

/--
Pointwise form of the full noncommutative Fréchet--Duhamel identity.
-/
theorem exponentialDerivative_apply_eq_duhamelDerivative
    (a h : A) :
    exponentialDerivative (𝕜 := ℝ) a h =
      duhamelDerivative a h := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hLine :
      HasDerivAt (fun r : ℝ => a + r • h) h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) a).add
        ((hasDerivAt_id (x := (0 : ℝ))).smul_const h) using 1 <;>
      simp
  have hFromFrechet :
      HasDerivAt
        (fun r : ℝ => NormedSpace.exp (a + r • h))
        (exponentialDerivative (𝕜 := ℝ) a h) 0 := by
    convert
      (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) (A := A) a).comp_hasDerivAt_of_eq
        (x := (0 : ℝ)) (y := a) hLine (by simp) using 1 <;>
      simp [Function.comp_def]
  exact hFromFrechet.unique (hasDerivAt_exp_affine_duhamel a h)

/--
Bundled operator identity between the changed-origin real Fréchet derivative
and the Bochner--Duhamel operator.
-/
theorem exponentialDerivative_eq_duhamelDerivative (a : A) :
    exponentialDerivative (𝕜 := ℝ) a =
      duhamelDerivative a := by
  ext h
  exact exponentialDerivative_apply_eq_duhamelDerivative a h

end InfoGeometry.OperatorAlgebra
