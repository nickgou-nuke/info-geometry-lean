import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

/--
The finite-difference Duhamel integral.  At z = 0 it is the derivative
integral; away from zero it is the exact divided difference furnished by the
path t ↦ exp ((1 - t) • a) * exp (t • (a + z • h)).
-/
noncomputable def perturbedDuhamelIntegral
    (a h : A) (z : ℝ) : A :=
  ∫ t in (0 : ℝ)..1,
    NormedSpace.exp ((1 - t) • a) *
      h *
        NormedSpace.exp (t • (a + z • h))

/-- The finite-difference Duhamel integral depends continuously on z. -/
theorem continuous_perturbedDuhamelIntegral (a h : A) :
    Continuous (perturbedDuhamelIntegral a h) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
  fun_prop

/--
Exact finite-difference Duhamel formula.  No commutativity assumption is made:
the second exponential is evaluated at the perturbed endpoint a + z • h.
-/
theorem exp_add_smul_sub_exp_eq_smul_perturbedDuhamelIntegral
    (a h : A) (z : ℝ) :
    NormedSpace.exp (a + z • h) - NormedSpace.exp a =
      z • perturbedDuhamelIntegral a h z := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let F : ℝ → A := fun t =>
    NormedSpace.exp ((1 - t) • a) *
      NormedSpace.exp (t • (a + z • h))
  let F' : ℝ → A := fun t =>
    NormedSpace.exp ((1 - t) • a) *
      (z • h) *
        NormedSpace.exp (t • (a + z • h))
  have hF' (t : ℝ) : HasDerivAt F (F' t) t := by
    have hOneSub :
        HasDerivAt (fun u : ℝ => 1 - u) (-1) t := by
      convert
        (hasDerivAt_const (x := t) (1 : ℝ)).sub
          (hasDerivAt_id (x := t)) using 1 <;> simp
    have hLeft :
        HasDerivAt
          (fun u : ℝ => NormedSpace.exp ((1 - u) • a))
          (-(NormedSpace.exp ((1 - t) • a) * a)) t := by
      convert
        (hasDerivAt_exp_smul_const a (1 - t)).comp t hOneSub
          using 1 <;> simp
    have hRight :
        HasDerivAt
          (fun u : ℝ => NormedSpace.exp (u • (a + z • h)))
          ((a + z • h) *
            NormedSpace.exp (t • (a + z • h))) t :=
      hasDerivAt_exp_smul_const' (a + z • h) t
    dsimp [F, F']
    convert hLeft.mul hRight using 1
    noncomm_ring
  have hF'cont : Continuous F' := by
    dsimp [F']
    fun_prop
  have hFTC :
      (∫ t in (0 : ℝ)..1, F' t) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hF' t) (hF'cont.intervalIntegrable 0 1)
  calc
    NormedSpace.exp (a + z • h) - NormedSpace.exp a =
        ∫ t in (0 : ℝ)..1,
          NormedSpace.exp ((1 - t) • a) *
            (z • h) *
              NormedSpace.exp (t • (a + z • h)) := by
      simpa [F, F'] using hFTC.symm
    _ = ∫ t in (0 : ℝ)..1,
          z •
            (NormedSpace.exp ((1 - t) • a) *
              h *
                NormedSpace.exp (t • (a + z • h))) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [mul_smul_comm, smul_mul_assoc]
    _ = z • perturbedDuhamelIntegral a h z := by
      rw [intervalIntegral.integral_smul]
      rfl

/--
The exponential along the real affine line a + z • h has the Duhamel
directional derivative at zero.  The proof uses the exact finite-difference
formula and continuity of its parameter-dependent Bochner integral.
-/
theorem hasDerivAt_exp_affine_duhamel (a h : A) :
    HasDerivAt
      (fun z : ℝ => NormedSpace.exp (a + z • h))
      (duhamelDerivative a h) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hAtZero :
      perturbedDuhamelIntegral a h 0 =
        duhamelDerivative a h := by
    rw [duhamelDerivative_apply_integral]
    simp [perturbedDuhamelIntegral]
  rw [← hAtZero]
  refine
    (continuous_perturbedDuhamelIntegral a h).continuousAt.mono_left
      inf_le_left |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
  simp only [zero_add, zero_smul, add_zero]
  rw [exp_add_smul_sub_exp_eq_smul_perturbedDuhamelIntegral]
  simp [smul_smul, hz0]

/--
The changed-origin real Fréchet derivative of the Banach-algebra exponential
is the Duhamel operator in every direction.  This is the full
noncommutative operator identity; no centralizer hypothesis remains.
-/
theorem exponentialDerivative_apply_eq_duhamelDerivative
    (a h : A) :
    exponentialDerivative (𝕜 := ℝ) a h =
      duhamelDerivative a h := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hLine :
      HasDerivAt (fun t : ℝ => a + t • h) h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) a).add
        ((hasDerivAt_id (x := (0 : ℝ))).smul_const h) using 1 <;>
      simp
  have hFromFrechet :
      HasDerivAt
        (fun t : ℝ => NormedSpace.exp (a + t • h))
        (exponentialDerivative (𝕜 := ℝ) a h) 0 := by
    convert
      (hasFDerivAt_exp_noncommutative (𝕜 := ℝ) (A := A) a).comp_hasDerivAt_of_eq
        (x := (0 : ℝ)) (y := a) hLine (by simp) using 1 <;>
      simp [Function.comp_def]
  exact hFromFrechet.unique (hasDerivAt_exp_affine_duhamel a h)

/-- Bundled operator form of the noncommutative Duhamel identity. -/
theorem exponentialDerivative_eq_duhamelDerivative (a : A) :
    exponentialDerivative (𝕜 := ℝ) a =
      duhamelDerivative a := by
  ext h
  exact exponentialDerivative_apply_eq_duhamelDerivative a h

end InfoGeometry.OperatorAlgebra
