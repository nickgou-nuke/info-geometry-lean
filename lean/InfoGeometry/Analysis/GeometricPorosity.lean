/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometric depletion of a real porosity parameter

The scalar sequence here is the geometric-sum specialization of the porosity
constants in equation (3.9) of Knutsen, arXiv:2204.03068v1. The parameter is real,
and the bounds include the algebraic endpoint `ν = 0`.

These declarations concern a real sequence, its limit, and a conditional scalar
iteration. They do not construct porous subsets, thickenings, an STFT, a Fock
space, or the analytic one-step estimate needed for an uncertainty principle.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace InfoGeometry.Analysis.GeometricPorosity

/-- Successive subtraction of the geometric losses `(ν / 3)^(n + 1)`. -/
noncomputable def porositySequence (ν : ℝ) : ℕ → ℝ
  | 0 => ν
  | n + 1 => porositySequence ν n - (ν / 3) ^ (n + 1)

@[simp] theorem porositySequence_zero (ν : ℝ) :
    porositySequence ν 0 = ν := rfl

@[simp] theorem porositySequence_succ (ν : ℝ) (n : ℕ) :
    porositySequence ν (n + 1) =
      porositySequence ν n - (ν / 3) ^ (n + 1) := rfl

/-- The recursive constants equal the original parameter minus the finite
geometric sum. This is a scalar identity for every real parameter. -/
theorem porositySequence_eq_sub_sum (ν : ℝ) (n : ℕ) :
    porositySequence ν n =
      ν - ∑ k ∈ Finset.range n, (ν / 3) ^ (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [porositySequence_succ, ih, Finset.sum_range_succ]
      ring

/-- A closed form with the denominator cleared; it remains valid at `ν = 3`. -/
theorem porositySequence_mul (ν : ℝ) (n : ℕ) :
    (3 - ν) * porositySequence ν n =
      ν * (2 - ν) + ν * (ν / 3) ^ n := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
      rw [porositySequence_succ, mul_sub, ih]
      simp only [pow_succ]
      ring

/-- The usual quotient form requires precisely a nonzero denominator. -/
theorem porositySequence_eq_closedForm (ν : ℝ) (n : ℕ) (hν : 3 - ν ≠ 0) :
    porositySequence ν n =
      (ν * (2 - ν) + ν * (ν / 3) ^ n) / (3 - ν) := by
  apply (eq_div_iff hν).2
  rw [mul_comm]
  exact porositySequence_mul ν n

/-- Nonnegative geometric losses make the sequence antitone. -/
theorem porositySequence_antitone {ν : ℝ} (hν : 0 ≤ ν) :
    Antitone (porositySequence ν) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [porositySequence_succ]
  exact sub_le_self _ (pow_nonneg (div_nonneg hν (by norm_num)) _)

/-- Every term is at most the initial parameter. -/
theorem porositySequence_le {ν : ℝ} (hν : 0 ≤ ν) (n : ℕ) :
    porositySequence ν n ≤ ν := by
  simpa using porositySequence_antitone hν (Nat.zero_le n)

/-- On the unit interval, geometric depletion retains at least half of the
original parameter at every finite stage. -/
theorem half_le_porositySequence {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n : ℕ) :
    ν / 2 ≤ porositySequence ν n := by
  have hpow : 0 ≤ ν * (ν / 3) ^ n :=
    mul_nonneg hν0 (pow_nonneg (div_nonneg hν0 (by norm_num)) n)
  have hquad : 0 ≤ ν * (1 - ν) := mul_nonneg hν0 (sub_nonneg.mpr hν1)
  have hden : 0 < 3 - ν := by linarith
  have hscaled : 0 ≤ (3 - ν) * (porositySequence ν n - ν / 2) := by
    nlinarith [porositySequence_mul ν n]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hscaled hden)

/-- In particular, the constants remain nonnegative on the unit interval. -/
theorem porositySequence_nonneg {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n : ℕ) :
    0 ≤ porositySequence ν n :=
  (div_nonneg hν0 (by norm_num)).trans (half_le_porositySequence hν0 hν1 n)

/-- The lower bound controls every natural power, including the geometric
exponent `2 * d` used for phase-space dimension. -/
theorem one_sub_porositySequence_pow_le {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (n m : ℕ) :
    1 - porositySequence ν n ^ m ≤ 1 - (ν / 2) ^ m := by
  exact sub_le_sub_left
    (pow_le_pow_left₀ (div_nonneg hν0 (by norm_num))
      (half_le_porositySequence hν0 hν1 n) m) 1

/-- The scalar sequence has an actual real limit, obtained from decay of its
geometric remainder. This does not assert a limit of porous sets or operators. -/
theorem tendsto_porositySequence {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    Tendsto (porositySequence ν) atTop (𝓝 (ν * (2 - ν) / (3 - ν))) := by
  have hden : 3 - ν ≠ 0 := by linarith [hν1]
  have hpow : Tendsto (fun n : ℕ => (ν / 3) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hν0 (by norm_num)) (by linarith)
  have hnum : Tendsto (fun n : ℕ => ν * (2 - ν) + ν * (ν / 3) ^ n)
      atTop (𝓝 (ν * (2 - ν))) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => ν * (2 - ν)) atTop (𝓝 (ν * (2 - ν)))).add
        (hpow.const_mul ν)
  have hseq : porositySequence ν =
      fun n => (ν * (2 - ν) + ν * (ν / 3) ^ n) / (3 - ν) :=
    funext (fun n => porositySequence_eq_closedForm ν n hden)
  rw [hseq]
  exact hnum.div_const (3 - ν)

/-- The uniform scalar factor furnished by the lower bound in dimension `d`. -/
def contractionFactor (ν : ℝ) (d : ℕ) : ℝ := 1 - (ν / 2) ^ (2 * d)

theorem contractionFactor_nonneg {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (d : ℕ) :
    0 ≤ contractionFactor ν d := by
  exact sub_nonneg.mpr (pow_le_one₀
    (div_nonneg hν0 (by norm_num)) (by linarith [hν1] : ν / 2 ≤ 1))

theorem contractionFactor_lt_one {ν : ℝ} (hν : 0 < ν) (d : ℕ) :
    contractionFactor ν d < 1 := by
  exact sub_lt_self 1 (pow_pos (div_pos hν (by norm_num)) (2 * d))

/-- An explicitly supplied scalar one-step estimate iterates to a geometric
upper bound. Establishing this premise for localization operators is separate
analytic work. -/
theorem iteration_le_geometric {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (d : ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ (1 - porositySequence ν n ^ (2 * d)) * a n)
    (n : ℕ) :
    a n ≤ contractionFactor ν d ^ n * a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a (n + 1) ≤ (1 - porositySequence ν n ^ (2 * d)) * a n := hstep n
        _ ≤ contractionFactor ν d * a n :=
          mul_le_mul_of_nonneg_right
            (one_sub_porositySequence_pow_le hν0 hν1 n (2 * d)) (ha n)
        _ ≤ contractionFactor ν d * (contractionFactor ν d ^ n * a 0) :=
          mul_le_mul_of_nonneg_left ih (contractionFactor_nonneg hν0 hν1 d)
        _ = contractionFactor ν d ^ (n + 1) * a 0 := by
          rw [pow_succ]
          ring

/-- A nonnegative scalar iteration satisfying the stated one-step bound tends
to zero whenever the original parameter is positive. -/
theorem tendsto_iteration_zero {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1)
    (d : ℕ) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ (1 - porositySequence ν n ^ (2 * d)) * a n) :
    Tendsto a atTop (𝓝 0) := by
  have hgeom : Tendsto (fun n : ℕ => contractionFactor ν d ^ n * a 0)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (contractionFactor_nonneg hν0.le hν1 d)
        (contractionFactor_lt_one hν0 d)).mul_const (a 0)
  exact squeeze_zero ha (iteration_le_geometric hν0.le hν1 d a ha hstep) hgeom

end InfoGeometry.Analysis.GeometricPorosity
