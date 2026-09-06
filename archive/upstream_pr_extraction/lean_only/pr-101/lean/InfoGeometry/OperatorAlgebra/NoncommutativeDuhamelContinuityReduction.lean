import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFiniteDifference
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

/-!
# Fréchet--Duhamel reduction to one parametric continuity statement

The exact finite-difference owner proves

`exp(a + r h) - exp(a) = r • G(r)`

with

`G(r) = ∫₀¹ exp((1-s)a) h exp(s(a+r h)) ds`.

This file identifies `G(0)` with the repository's native Bochner--Duhamel
operator and proves that continuity of the parameterized integral at `r = 0`
is the only remaining topological input needed for full operator-level
Fréchet--Duhamel equality.

The continuity condition is kept explicit in the final theorem name.  It is
not stored in a structure and is not renamed as the desired Duhamel theorem.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra

open Filter MeasureTheory
open scoped Interval Topology

variable {A : Type*}
variable [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The unscaled perturbative Duhamel integral. -/
noncomputable def duhamelPerturbationIntegral
    (a h : A) (r : ℝ) : A :=
  ∫ s in (0 : ℝ)..1,
    duhamelFiniteDifferenceIntegrand a h r s

/-- At zero perturbation the finite-difference kernel is exactly the native
Duhamel derivative applied to the selected direction. -/
theorem duhamelPerturbationIntegral_zero
    (a h : A) :
    duhamelPerturbationIntegral a h 0 =
      duhamelDerivative a h := by
  rw [duhamelPerturbationIntegral,
    duhamelDerivative_apply_integral]
  apply intervalIntegral.integral_congr
  intro s hs
  simp [duhamelFiniteDifferenceIntegrand]

/-- Exact finite-difference identity in the useful factorized form
`r • G(r) = exp(a+r h)-exp(a)`. -/
theorem smul_duhamelPerturbationIntegral_eq_exp_sub_exp
    (a h : A) (r : ℝ) :
    r • duhamelPerturbationIntegral a h r =
      NormedSpace.exp (a + r • h) - NormedSpace.exp a := by
  unfold duhamelPerturbationIntegral
  rw [← intervalIntegral.integral_smul]
  exact integral_duhamelFiniteDifference_eq_exp_sub_exp a h r

/-- Away from the base point, the ordinary slope of the exponential affine
line is exactly the perturbative Duhamel integral. -/
theorem slope_exp_affine_eq_duhamelPerturbationIntegral
    (a h : A) {r : ℝ} (hr : r ≠ 0) :
    slope (fun t : ℝ => NormedSpace.exp (a + t • h)) 0 r =
      duhamelPerturbationIntegral a h r := by
  have hfd :=
    smul_duhamelPerturbationIntegral_eq_exp_sub_exp a h r
  rw [slope]
  simp only [sub_zero, zero_smul, add_zero]
  rw [← hfd]
  simp [hr]

/-- Continuity of the single parameterized Bochner integral at the origin is
sufficient to identify the changed-origin Fréchet derivative with the native
Duhamel derivative in the selected direction. -/
theorem exponentialDerivative_apply_eq_duhamelDerivative_of_continuousAt
    (a h : A)
    (hcont : ContinuousAt (duhamelPerturbationIntegral a h) 0) :
    exponentialDerivative (𝕜 := ℝ) a h =
      duhamelDerivative a h := by
  letI : NormedAlgebra ℚ A :=
    NormedAlgebra.restrictScalars ℚ ℝ A
  have hLine :
      HasDerivAt (fun r : ℝ => a + r • h) h 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) a).add
        ((hasDerivAt_id (x := (0 : ℝ))).smul_const h) using 1 <;>
      simp
  have hExp :
      HasDerivAt
        (fun r : ℝ => NormedSpace.exp (a + r • h))
        (exponentialDerivative (𝕜 := ℝ) a h) 0 := by
    simpa using
      (hasFDerivAt_exp_noncommutative
        (𝕜 := ℝ) (A := A) a).comp_hasDerivAt_of_eq
          (0 : ℝ) hLine (by simp)
  have hSlope :
      Tendsto
        (slope (fun r : ℝ => NormedSpace.exp (a + r • h)) 0)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (exponentialDerivative (𝕜 := ℝ) a h)) :=
    hasDerivAt_iff_tendsto_slope.mp hExp
  have hSlopeEq :
      slope (fun r : ℝ => NormedSpace.exp (a + r • h)) 0 =ᶠ[𝓝[≠] (0 : ℝ)]
        duhamelPerturbationIntegral a h := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := by simpa using hr
    exact slope_exp_affine_eq_duhamelPerturbationIntegral a h hr0
  have hDuhamelLimit :
      Tendsto (duhamelPerturbationIntegral a h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (duhamelPerturbationIntegral a h 0)) :=
    hcont.tendsto.mono_left inf_le_left
  have hSlopeAsDuhamel :
      Tendsto (duhamelPerturbationIntegral a h)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (exponentialDerivative (𝕜 := ℝ) a h)) :=
    hSlope.congr' hSlopeEq
  have hEq :
      exponentialDerivative (𝕜 := ℝ) a h =
        duhamelPerturbationIntegral a h 0 :=
    tendsto_nhds_unique hSlopeAsDuhamel hDuhamelLimit
  rw [hEq, duhamelPerturbationIntegral_zero]

end InfoGeometry.OperatorAlgebra
