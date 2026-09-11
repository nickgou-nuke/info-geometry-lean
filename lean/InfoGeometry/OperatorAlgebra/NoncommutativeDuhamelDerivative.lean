import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The noncommutative Duhamel derivative operator

For a real Banach algebra and `a : A`, the Duhamel operator is

`h ↦ ∫ t in 0..1, exp ((1 - t) • a) * h * exp (t • a)`.

It is constructed as an interval integral in the Banach space of continuous
linear maps.  Consequently linearity and continuity are native consequences
of Mathlib's Bochner integral, not fields in an evidence structure.
-/

namespace InfoGeometry.OperatorAlgebra

open MeasureTheory
open scoped Interval

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/--
The continuous linear insertion map appearing in the Duhamel integrand.
-/
noncomputable def duhamelIntegrand (a : A) (t : ℝ) : A →L[ℝ] A :=
  ContinuousLinearMap.mulLeftRight ℝ A
    (NormedSpace.exp ((1 - t) • a))
    (NormedSpace.exp (t • a))

/--
The noncommutative Duhamel operator, formed directly as a Bochner interval
integral of continuous linear maps.
-/
noncomputable def duhamelDerivative (a : A) : A →L[ℝ] A :=
  ∫ t in (0 : ℝ)..1, duhamelIntegrand a t

/-- The continuous-linear-map-valued Duhamel integrand is continuous. -/
theorem continuous_duhamelIntegrand (a : A) :
    Continuous (duhamelIntegrand a) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  unfold duhamelIntegrand
  fun_prop

/-- The Duhamel integrand is interval integrable on every compact interval. -/
theorem intervalIntegrable_duhamelIntegrand
    (a : A) (s t : ℝ) :
    IntervalIntegrable (duhamelIntegrand a) volume s t :=
  (continuous_duhamelIntegrand a).intervalIntegrable s t

/--
Evaluation of the Duhamel continuous linear map is the operator-valued
Duhamel integral.  Integrability is an explicit analytic premise rather than
an opaque structure field.
-/
theorem duhamelDerivative_apply
    (a h : A)
    (hIntegrable :
      IntervalIntegrable (duhamelIntegrand a) volume (0 : ℝ) 1) :
    duhamelDerivative a h =
      ∫ t in (0 : ℝ)..1,
        NormedSpace.exp ((1 - t) • a) *
          h *
            NormedSpace.exp (t • a) := by
  simpa [duhamelDerivative, duhamelIntegrand] using
    ContinuousLinearMap.intervalIntegral_apply hIntegrable h

/--
Unconditional evaluation formula, with interval integrability discharged by
continuity of the operator-valued integrand.
-/
theorem duhamelDerivative_apply_integral (a h : A) :
    duhamelDerivative a h =
      ∫ t in (0 : ℝ)..1,
        NormedSpace.exp ((1 - t) • a) *
          h *
            NormedSpace.exp (t • a) := by
  exact duhamelDerivative_apply a h
    (intervalIntegrable_duhamelIntegrand a 0 1)

/-- At the zero generator, the Duhamel operator is the identity map. -/
@[simp]
theorem duhamelDerivative_zero :
    duhamelDerivative (0 : A) = ContinuousLinearMap.id ℝ A := by
  ext h
  simp [duhamelDerivative, duhamelIntegrand,
    ContinuousLinearMap.mulLeftRight_apply]

/--
The changed-origin exponential derivative is the identity at the zero
generator, by uniqueness of the Fréchet derivative.
-/
@[simp]
theorem exponentialDerivative_zero :
    exponentialDerivative (𝕜 := ℝ) (0 : A) =
      ContinuousLinearMap.id ℝ A := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  exact
    (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) (A := A) (0 : A)).unique
      hasFDerivAt_exp_zero

/--
The Duhamel and changed-origin exponential derivatives agree at the origin.
This fixes the normalization and left/right multiplication orientation for the
general coefficient proof.
-/
theorem exponentialDerivative_eq_duhamelDerivative_zero :
    exponentialDerivative (𝕜 := ℝ) (0 : A) =
      duhamelDerivative (0 : A) := by
  simp

/--
On a tangent direction in the centralizer of `a`, the Duhamel derivative
reduces to ordinary multiplication by `exp a`.  The ambient Banach algebra
remains noncommutative; only the selected direction is required to commute
with the base operator.
-/
theorem duhamelDerivative_apply_of_commute
    (a h : A) (hComm : Commute h a) :
    duhamelDerivative a h = NormedSpace.exp a * h := by
  rw [duhamelDerivative_apply_integral]
  have hPointwise :
      ∀ t : ℝ,
        NormedSpace.exp ((1 - t) • a) * h *
              NormedSpace.exp (t • a) =
          NormedSpace.exp a * h := by
    intro t
    have hCommExp :
        Commute h (NormedSpace.exp (t • a)) :=
      (hComm.smul_right t).exp_right
    have hScaledComm :
      Commute ((1 - t) • a) (t • a) :=
      ((Commute.refl a).smul_left (1 - t)).smul_right t
    have hScaleSum : (1 - t) • a + t • a = a := by
      rw [sub_smul, one_smul]
      abel
    calc
      NormedSpace.exp ((1 - t) • a) * h *
            NormedSpace.exp (t • a) =
          NormedSpace.exp ((1 - t) • a) *
            (h * NormedSpace.exp (t • a)) := by
              rw [mul_assoc]
      _ = NormedSpace.exp ((1 - t) • a) *
            (NormedSpace.exp (t • a) * h) := by
              rw [hCommExp.eq]
      _ = (NormedSpace.exp ((1 - t) • a) *
            NormedSpace.exp (t • a)) * h := by
              rw [mul_assoc]
      _ = NormedSpace.exp ((1 - t) • a + t • a) * h := by
              letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
              rw [NormedSpace.exp_add_of_commute hScaledComm]
      _ = NormedSpace.exp a * h := by
              rw [hScaleSum]
  simp_rw [hPointwise]
  simp

/--
On a direction commuting with the base operator, the changed-origin Fréchet
derivative of the exponential is left multiplication by `exp a`.
-/
theorem exponentialDerivative_apply_of_commute
    (a h : A) (hComm : Commute h a) :
    exponentialDerivative (𝕜 := ℝ) a h =
      NormedSpace.exp a * h := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hLine :
      HasDerivAt (fun t : ℝ => a + t • h) h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) a).add
        ((hasDerivAt_id (x := (0 : ℝ))).smul_const h) using 1 <;> simp
  have hFromFrechet :
      HasDerivAt
        (fun t : ℝ => NormedSpace.exp (a + t • h))
        (exponentialDerivative (𝕜 := ℝ) a h) 0 :=
    by
      convert
        (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) (A := A) a).comp_hasDerivAt_of_eq
          (x := (0 : ℝ)) (y := a) hLine (by simp) using 1 <;> simp [Function.comp_def]
  have hFactored :
      (fun t : ℝ => NormedSpace.exp (a + t • h)) =
        fun t : ℝ => NormedSpace.exp a * NormedSpace.exp (t • h) := by
    funext t
    exact NormedSpace.exp_add_of_commute
      (hComm.symm.smul_right t)
  have hFromFactorization :
      HasDerivAt
        (fun t : ℝ => NormedSpace.exp (a + t • h))
        (NormedSpace.exp a * h) 0 := by
    rw [hFactored]
    simpa using
      (hasDerivAt_exp_smul_const h (0 : ℝ)).const_mul
        (NormedSpace.exp a)
  exact hFromFrechet.unique hFromFactorization

/--
The changed-origin exponential derivative and the Bochner-Duhamel derivative
agree on every tangent direction in the centralizer of the base operator.
-/
theorem exponentialDerivative_apply_eq_duhamelDerivative_of_commute
    (a h : A) (hComm : Commute h a) :
    exponentialDerivative (𝕜 := ℝ) a h =
      duhamelDerivative a h := by
  rw [exponentialDerivative_apply_of_commute a h hComm]
  rw [duhamelDerivative_apply_of_commute a h hComm]

end InfoGeometry.OperatorAlgebra
