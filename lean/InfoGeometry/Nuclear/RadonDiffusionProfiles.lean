/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stationary diffusion with first-order loss

Real constant-coefficient profiles, their actual derivatives, boundary values,
and exact uniform cell averages. `D * k^2 = lambda` is the model's parameter
relation. No experiment, equilibrium assumption, fitted parameter, or uniqueness
of arbitrary ODE solutions is certified here.

For cells covering `[0, N*d]`, BOTH finite-column models are sampled at the
same centers `(i - 1/2)*d`. A whole-cell uniform average is proved to have
the center-sampled shape, rather than assumed to be a point measurement.
-/

noncomputable section

namespace InfoGeometry.Nuclear.RadonDiffusionProfiles

open MeasureTheory

/-- A twice differentiable stationary profile, including regularity explicitly. -/
def SolvesDiffusionDecay (D lambda : ℝ) (C : ℝ → ℝ) : Prop :=
  Differentiable ℝ C ∧ Differentiable ℝ (deriv C) ∧
    ∀ x, D * deriv (deriv C) x - lambda * C x = 0

def sinhProfile (A k L x : ℝ) : ℝ := A * Real.sinh (k * (L - x))

def coshProfile (A k L x : ℝ) : ℝ := A * Real.cosh (k * (L - x))

def expProfile (A k x : ℝ) : ℝ := A * Real.exp (-k * x)

private theorem hasDerivAt_argument (k L x : ℝ) :
    HasDerivAt (fun y : ℝ => k * (L - y)) (-k) x := by
  simpa using ((hasDerivAt_id' x).const_sub L).const_mul k

theorem hasDerivAt_sinhProfile (A k L x : ℝ) :
    HasDerivAt (sinhProfile A k L) (-k * coshProfile A k L x) x := by
  unfold sinhProfile coshProfile
  convert ((hasDerivAt_argument k L x).sinh).const_mul A using 1 <;> ring

theorem hasDerivAt_coshProfile (A k L x : ℝ) :
    HasDerivAt (coshProfile A k L) (-k * sinhProfile A k L x) x := by
  unfold coshProfile sinhProfile
  convert ((hasDerivAt_argument k L x).cosh).const_mul A using 1 <;> ring

theorem hasDerivAt_expProfile (A k x : ℝ) :
    HasDerivAt (expProfile A k) (-k * expProfile A k x) x := by
  have h := (((hasDerivAt_id' x).const_mul (-k)).exp).const_mul A
  unfold expProfile
  convert h using 1 <;> ring

theorem deriv_sinhProfile (A k L : ℝ) :
    deriv (sinhProfile A k L) = fun x => -k * coshProfile A k L x := by
  funext x
  exact (hasDerivAt_sinhProfile A k L x).deriv

theorem deriv_coshProfile (A k L : ℝ) :
    deriv (coshProfile A k L) = fun x => -k * sinhProfile A k L x := by
  funext x
  exact (hasDerivAt_coshProfile A k L x).deriv

theorem deriv_expProfile (A k : ℝ) :
    deriv (expProfile A k) = fun x => -k * expProfile A k x := by
  funext x
  exact (hasDerivAt_expProfile A k x).deriv

theorem deriv2_sinhProfile (A k L x : ℝ) :
    deriv (deriv (sinhProfile A k L)) x = k ^ 2 * sinhProfile A k L x := by
  rw [deriv_sinhProfile]
  convert ((hasDerivAt_coshProfile A k L x).const_mul (-k)).deriv using 1
  ring

theorem deriv2_coshProfile (A k L x : ℝ) :
    deriv (deriv (coshProfile A k L)) x = k ^ 2 * coshProfile A k L x := by
  rw [deriv_coshProfile]
  convert ((hasDerivAt_sinhProfile A k L x).const_mul (-k)).deriv using 1
  ring

theorem deriv2_expProfile (A k x : ℝ) :
    deriv (deriv (expProfile A k)) x = k ^ 2 * expProfile A k x := by
  rw [deriv_expProfile]
  convert ((hasDerivAt_expProfile A k x).const_mul (-k)).deriv using 1
  ring

theorem sinhProfile_solves (A k L D lambda : ℝ) (h : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (sinhProfile A k L) := by
  refine ⟨fun x => (hasDerivAt_sinhProfile A k L x).differentiableAt, ?_, ?_⟩
  · rw [deriv_sinhProfile]
    exact fun x => ((hasDerivAt_coshProfile A k L x).const_mul (-k)).differentiableAt
  · intro x
    rw [deriv2_sinhProfile, ← mul_assoc, h, sub_self]

theorem coshProfile_solves (A k L D lambda : ℝ) (h : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (coshProfile A k L) := by
  refine ⟨fun x => (hasDerivAt_coshProfile A k L x).differentiableAt, ?_, ?_⟩
  · rw [deriv_coshProfile]
    exact fun x => ((hasDerivAt_sinhProfile A k L x).const_mul (-k)).differentiableAt
  · intro x
    rw [deriv2_coshProfile, ← mul_assoc, h, sub_self]

theorem expProfile_solves (A k D lambda : ℝ) (h : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (expProfile A k) := by
  refine ⟨fun x => (hasDerivAt_expProfile A k x).differentiableAt, ?_, ?_⟩
  · rw [deriv_expProfile]
    exact fun x => ((hasDerivAt_expProfile A k x).const_mul (-k)).differentiableAt
  · intro x
    rw [deriv2_expProfile, ← mul_assoc, h, sub_self]

/-- Fixed inlet and a perfect sink when `k > 0` and `L > 0`.
The zero-loss linear profile is not obtained by substituting `k = 0` here. -/
def dirichletProfile (C0 k L : ℝ) : ℝ → ℝ :=
  sinhProfile (C0 / Real.sinh (k * L)) k L

/-- Fixed inlet and zero derivative at the physical endpoint. -/
def neumannProfile (C0 k L : ℝ) : ℝ → ℝ :=
  coshProfile (C0 / Real.cosh (k * L)) k L

theorem dirichlet_inlet (C0 : ℝ) {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    dirichletProfile C0 k L 0 = C0 := by
  have hs : Real.sinh (k * L) ≠ 0 :=
    Real.sinh_ne_zero.mpr (ne_of_gt (mul_pos hk hL))
  simp [dirichletProfile, sinhProfile, hs]

@[simp] theorem dirichlet_outlet (C0 k L : ℝ) :
    dirichletProfile C0 k L L = 0 := by
  simp [dirichletProfile, sinhProfile]

@[simp] theorem neumann_inlet (C0 k L : ℝ) :
    neumannProfile C0 k L 0 = C0 := by
  simp [neumannProfile, coshProfile, ne_of_gt (Real.cosh_pos (k * L))]

theorem neumann_outlet_derivative (C0 k L : ℝ) :
    deriv (neumannProfile C0 k L) L = 0 := by
  unfold neumannProfile
  rw [deriv_coshProfile]
  simp [sinhProfile]

theorem dirichlet_solves (C0 k L D lambda : ℝ) (h : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (dirichletProfile C0 k L) :=
  sinhProfile_solves _ k L D lambda h

theorem neumann_solves (C0 k L D lambda : ℝ) (h : D * k ^ 2 = lambda) :
    SolvesDiffusionDecay D lambda (neumannProfile C0 k L) :=
  coshProfile_solves _ k L D lambda h

/-- Average over a cell with center `c` and width `d`; physical widths are positive. -/
def cellAverage (f : ℝ → ℝ) (c d : ℝ) : ℝ :=
  (∫ x in (c - d / 2)..(c + d / 2), f x) / d

theorem cellAverage_sinhProfile (A k L c d : ℝ) (hk : k ≠ 0) (hd : d ≠ 0) :
    cellAverage (sinhProfile A k L) c d =
      (2 * Real.sinh (k * d / 2) / (k * d)) * sinhProfile A k L c := by
  have hp (x : ℝ) : HasDerivAt (coshProfile (-A / k) k L)
      (sinhProfile A k L x) x := by
    convert hasDerivAt_coshProfile (-A / k) k L x using 1
    dsimp [sinhProfile]
    field_simp
  have hc : Continuous (sinhProfile A k L) := by
    unfold sinhProfile
    fun_prop
  unfold cellAverage
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hp x) (hc.intervalIntegrable _ _)]
  dsimp [coshProfile, sinhProfile]
  rw [show k * (L - (c + d / 2)) = k * (L - c) - k * d / 2 by ring,
    show k * (L - (c - d / 2)) = k * (L - c) + k * d / 2 by ring,
    Real.cosh_sub, Real.cosh_add]
  field_simp
  ring

theorem cellAverage_coshProfile (A k L c d : ℝ) (hk : k ≠ 0) (hd : d ≠ 0) :
    cellAverage (coshProfile A k L) c d =
      (2 * Real.sinh (k * d / 2) / (k * d)) * coshProfile A k L c := by
  have hp (x : ℝ) : HasDerivAt (sinhProfile (-A / k) k L)
      (coshProfile A k L x) x := by
    convert hasDerivAt_sinhProfile (-A / k) k L x using 1
    dsimp [coshProfile]
    field_simp
  have hc : Continuous (coshProfile A k L) := by
    unfold coshProfile
    fun_prop
  unfold cellAverage
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hp x) (hc.intervalIntegrable _ _)]
  dsimp [coshProfile, sinhProfile]
  rw [show k * (L - (c + d / 2)) = k * (L - c) - k * d / 2 by ring,
    show k * (L - (c - d / 2)) = k * (L - c) + k * d / 2 by ring,
    Real.sinh_sub, Real.sinh_add]
  field_simp
  ring

/-- One-based cell numbering: valid cartridge indices satisfy `1 ≤ i ≤ N`. -/
def cartridgeCenter (d i : ℝ) : ℝ := (i - 1 / 2) * d

theorem cartridge_left_face (d i : ℝ) :
    cartridgeCenter d i - d / 2 = (i - 1) * d := by
  unfold cartridgeCenter
  ring

theorem cartridge_right_face (d i : ℝ) :
    cartridgeCenter d i + d / 2 = i * d := by
  unfold cartridgeCenter
  ring

/-- A common geometry fixes the argument for both finite-column models. -/
theorem cartridge_argument (k d N i : ℝ) :
    k * (N * d - cartridgeCenter d i) = (k * d) * (N + 1 / 2 - i) := by
  unfold cartridgeCenter
  ring

theorem sinh_at_cartridge (A k d N i : ℝ) :
    sinhProfile A k (N * d) (cartridgeCenter d i) =
      A * Real.sinh ((k * d) * (N + 1 / 2 - i)) := by
  rw [sinhProfile, cartridge_argument]

theorem cosh_at_cartridge (A k d N i : ℝ) :
    coshProfile A k (N * d) (cartridgeCenter d i) =
      A * Real.cosh ((k * d) * (N + 1 / 2 - i)) := by
  rw [coshProfile, cartridge_argument]

/-- Equal-step exponential attenuation, stated without division or nonzero amplitude. -/
theorem expProfile_step (A k x d : ℝ) :
    expProfile A k x = Real.exp (k * d) * expProfile A k (x + d) := by
  unfold expProfile
  calc
    A * Real.exp (-k * x) = A * Real.exp (k * d + -k * (x + d)) := by
      congr 2
      ring
    _ = _ := by rw [Real.exp_add]; ring

theorem expProfile_halving (A k x d : ℝ) (h : k * d = Real.log 2) :
    expProfile A k x = 2 * expProfile A k (x + d) := by
  rw [expProfile_step A k x d, h, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Terminal Neumann ratio at the last two equal-cell centers. -/
theorem terminal_cosh_ratio (mu : ℝ) :
    Real.cosh (3 * mu / 2) / Real.cosh (mu / 2) = 2 * Real.cosh mu - 1 := by
  have hc : Real.cosh (mu / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have htwo : Real.cosh mu = Real.cosh (mu / 2) ^ 2 + Real.sinh (mu / 2) ^ 2 := by
    calc
      Real.cosh mu = Real.cosh (2 * (mu / 2)) := by congr 1; ring
      _ = _ := Real.cosh_two_mul (mu / 2)
  rw [show 3 * mu / 2 = 3 * (mu / 2) by ring, Real.cosh_three_mul]
  rw [htwo]
  have h := Real.cosh_sq_sub_sinh_sq (mu / 2)
  field_simp
  nlinarith

end InfoGeometry.Nuclear.RadonDiffusionProfiles
