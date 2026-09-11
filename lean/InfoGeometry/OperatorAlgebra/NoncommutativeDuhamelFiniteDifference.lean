import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Exact noncommutative Duhamel finite-difference formula

This owner proves the finite-difference identity that sits immediately before
operator-level Fréchet--Duhamel identification.

For a real Banach algebra and `a h : A`, consider

`F_{r}(s) = exp ((1-s)a) * exp (s (a + r h))`.

Differentiating in `s` uses only the native one-parameter exponential
calculus: the right-generator derivative on the first exponential and the
left-generator derivative on the second.  The two `a` terms cancel without
any commutativity assumption and leave

`F_r'(s) = r * exp((1-s)a) * h * exp(s(a+r h))`.

The fundamental theorem of calculus then gives the exact finite-difference
Duhamel formula.  No spectral decomposition, trace, or supplied derivative law
is used here.

This theorem is stronger than the one-insertion trace collapse but still stops
short of identifying `exponentialDerivative a` with `duhamelDerivative a`:
that final step requires passing from this finite-difference formula to the
Fréchet limit uniformly in the perturbation parameter.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra

open MeasureTheory
open scoped Interval

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Interaction-picture path joining `exp a` to `exp (a + r h)`. -/
noncomputable def duhamelBridgePath
    (a h : A) (r s : ℝ) : A :=
  NormedSpace.exp ((1 - s) • a) *
    NormedSpace.exp (s • (a + r • h))

/-- The insertion kernel occurring in the exact finite-difference formula. -/
noncomputable def duhamelFiniteDifferenceIntegrand
    (a h : A) (r s : ℝ) : A :=
  NormedSpace.exp ((1 - s) • a) * h *
    NormedSpace.exp (s • (a + r • h))

/-- Derivative of the interaction-picture bridge path.

The proof deliberately chooses the right-generator derivative for the first
exponential and the left-generator derivative for the second, so the two base
`a` terms cancel in their native noncommutative order. -/
theorem hasDerivAt_duhamelBridgePath
    (a h : A) (r s : ℝ) :
    HasDerivAt (duhamelBridgePath a h r)
      (r • duhamelFiniteDifferenceIntegrand a h r s) s := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hu : HasDerivAt (fun x : ℝ => 1 - x) (-1) s := by
    convert
      (hasDerivAt_const (x := s) (1 : ℝ)).sub
        (hasDerivAt_id (x := s)) using 1 <;> norm_num
  have hleft0 :
      HasDerivAt
        (fun u : ℝ => NormedSpace.exp (u • a))
        (NormedSpace.exp ((1 - s) • a) * a) (1 - s) :=
    (hasStrictDerivAt_exp_smul_const a (1 - s)).hasDerivAt
  have hleft :
      HasDerivAt
        (fun x : ℝ => NormedSpace.exp ((1 - x) • a))
        (-(NormedSpace.exp ((1 - s) • a) * a)) s := by
    simpa [Function.comp_def] using hleft0.scomp s hu
  have hright :
      HasDerivAt
        (fun x : ℝ => NormedSpace.exp (x • (a + r • h)))
        ((a + r • h) * NormedSpace.exp (s • (a + r • h))) s :=
    (hasStrictDerivAt_exp_smul_const' (a + r • h) s).hasDerivAt
  have hprod :=
    (ContinuousLinearMap.mul ℝ A).hasDerivAt_of_bilinear hleft hright
  change HasDerivAt
    (fun x : ℝ =>
      NormedSpace.exp ((1 - x) • a) *
        NormedSpace.exp (x • (a + r • h))) _ s
  convert hprod using 1
  · change r • duhamelFiniteDifferenceIntegrand a h r s =
      NormedSpace.exp ((1 - s) • a) *
          ((a + r • h) * NormedSpace.exp (s • (a + r • h))) +
        (-(NormedSpace.exp ((1 - s) • a) * a)) *
          NormedSpace.exp (s • (a + r • h))
    unfold duhamelFiniteDifferenceIntegrand
    symm
    calc
      NormedSpace.exp ((1 - s) • a) *
            ((a + r • h) * NormedSpace.exp (s • (a + r • h))) +
          (-(NormedSpace.exp ((1 - s) • a) * a)) *
            NormedSpace.exp (s • (a + r • h)) =
        -(NormedSpace.exp ((1 - s) • a) * a *
            NormedSpace.exp (s • (a + r • h))) +
          NormedSpace.exp ((1 - s) • a) *
            (a * NormedSpace.exp (s • (a + r • h)) +
              (r • h) * NormedSpace.exp (s • (a + r • h))) := by
          rw [add_mul, add_comm]
          simp only [neg_mul, mul_assoc]
      _ =
        -(NormedSpace.exp ((1 - s) • a) * a *
            NormedSpace.exp (s • (a + r • h))) +
          (NormedSpace.exp ((1 - s) • a) * a *
              NormedSpace.exp (s • (a + r • h)) +
            NormedSpace.exp ((1 - s) • a) *
              ((r • h) * NormedSpace.exp (s • (a + r • h)))) := by
          rw [mul_add]
          simp only [mul_assoc]
      _ = NormedSpace.exp ((1 - s) • a) *
            ((r • h) * NormedSpace.exp (s • (a + r • h))) := by
          abel
      _ = r •
          (NormedSpace.exp ((1 - s) • a) * h *
            NormedSpace.exp (s • (a + r • h))) := by
          simp only [mul_assoc, mul_smul_comm, smul_mul_assoc]

/-- The scaled insertion kernel is continuous in the path parameter. -/
theorem continuous_duhamelFiniteDifferenceIntegrand_s
    (a h : A) (r : ℝ) :
    Continuous (fun s : ℝ =>
      r • duhamelFiniteDifferenceIntegrand a h r s) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold duhamelFiniteDifferenceIntegrand
  fun_prop

/-- Exact scaled finite-difference Duhamel formula. -/
theorem integral_duhamelFiniteDifference_eq_exp_sub_exp
    (a h : A) (r : ℝ) :
    (∫ s in (0 : ℝ)..1,
      r • duhamelFiniteDifferenceIntegrand a h r s) =
      NormedSpace.exp (a + r • h) - NormedSpace.exp a := by
  have hderiv :
      ∀ s ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (duhamelBridgePath a h r)
          (r • duhamelFiniteDifferenceIntegrand a h r s) s := by
    intro s hs
    exact hasDerivAt_duhamelBridgePath a h r s
  have hint :
      IntervalIntegrable
        (fun s : ℝ => r • duhamelFiniteDifferenceIntegrand a h r s)
        volume 0 1 :=
    (continuous_duhamelFiniteDifferenceIntegrand_s a h r).intervalIntegrable 0 1
  simpa [duhamelBridgePath] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (1 : ℝ)) hderiv hint)

/-- Standard exact noncommutative finite-difference Duhamel identity:

`exp(a+h) - exp(a) = ∫₀¹ exp((1-s)a) h exp(s(a+h)) ds`.
-/
theorem exp_add_sub_exp_eq_integral_duhamelFiniteDifference
    (a h : A) :
    NormedSpace.exp (a + h) - NormedSpace.exp a =
      ∫ s in (0 : ℝ)..1,
        NormedSpace.exp ((1 - s) • a) * h *
          NormedSpace.exp (s • (a + h)) := by
  have hfd := integral_duhamelFiniteDifference_eq_exp_sub_exp a h 1
  simpa [duhamelFiniteDifferenceIntegrand] using hfd.symm

end InfoGeometry.OperatorAlgebra
