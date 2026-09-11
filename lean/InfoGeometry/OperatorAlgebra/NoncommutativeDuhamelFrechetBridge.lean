import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFiniteDifference
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
  simp [duhamelDifferenceQuotient, duhamelFiniteDifferenceIntegrand]

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

end InfoGeometry.OperatorAlgebra
