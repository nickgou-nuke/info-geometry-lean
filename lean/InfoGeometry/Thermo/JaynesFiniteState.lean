/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Jaynes exponential states

This is the finite algebraic/statistical owner for a reference surprisal `K`
and one supplied constraint observable `F`.  It proves positivity,
normalization, and the logarithmic state identity.  It does not claim a KMS
existence theorem, a BKM Hessian theorem, or a spectral-projector curvature
result.
-/

open scoped BigOperators

namespace InfoGeometry.Thermo

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Unnormalized Jaynes weight `exp (-K + θ F)`. -/
noncomputable def jaynesWeight
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-K ω + theta * F ω)

/-- Finite Jaynes partition function. -/
noncomputable def jaynesPartition
    (K F : Ω → ℝ) (theta : ℝ) : ℝ :=
  ∑ ω, jaynesWeight K F theta ω

/-- Normalized finite Jaynes state. -/
noncomputable def jaynesState
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) : ℝ :=
  jaynesWeight K F theta ω / jaynesPartition K F theta

theorem jaynesWeight_pos (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    0 < jaynesWeight K F theta ω := by
  unfold jaynesWeight
  exact Real.exp_pos _

theorem jaynesPartition_pos (K F : Ω → ℝ) (theta : ℝ) :
    0 < jaynesPartition K F theta := by
  classical
  unfold jaynesPartition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun ω => jaynesWeight K F theta ω)
      (by intro ω hω; exact jaynesWeight_pos K F theta ω)
      Finset.univ_nonempty)

theorem jaynesState_pos (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    0 < jaynesState K F theta ω := by
  unfold jaynesState
  exact div_pos (jaynesWeight_pos K F theta ω) (jaynesPartition_pos K F theta)

theorem jaynesState_sum_one (K F : Ω → ℝ) (theta : ℝ) :
    ∑ ω, jaynesState K F theta ω = 1 := by
  classical
  unfold jaynesState
  have hZ : jaynesPartition K F theta ≠ 0 :=
    (jaynesPartition_pos K F theta).ne'
  calc
    ∑ ω, jaynesWeight K F theta ω / jaynesPartition K F theta =
        (∑ ω, jaynesWeight K F theta ω) / jaynesPartition K F theta := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset Ω))
              (f := fun ω => jaynesWeight K F theta ω)
              (a := jaynesPartition K F theta))
    _ = jaynesPartition K F theta / jaynesPartition K F theta := by
          rfl
    _ = 1 := by exact div_self hZ

theorem jaynes_logState
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    Real.log (jaynesState K F theta ω) =
      -K ω + theta * F ω - Real.log (jaynesPartition K F theta) := by
  unfold jaynesState jaynesWeight
  rw [Real.log_div (by positivity) (jaynesPartition_pos K F theta).ne']
  rw [Real.log_exp]

theorem jaynes_logState_eq_reference_surprisal
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    -Real.log (jaynesState K F theta ω) =
      K ω - theta * F ω + Real.log (jaynesPartition K F theta) := by
  rw [jaynes_logState]
  ring

/-! ## Jaynesian cumulant & Fisher–Jaynes Hessian analyticity -/

/-- Expectation of an observable `G` in the finite Jaynes state at coupling `theta`. -/
noncomputable def jaynesExpectation
    (K F : Ω → ℝ) (theta : ℝ) (G : Ω → ℝ) : ℝ :=
  ∑ ω, jaynesState K F theta ω * G ω

/-- Variance of an observable `G` in the finite Jaynes state at coupling `theta`. -/
noncomputable def jaynesVariance
    (K F : Ω → ℝ) (theta : ℝ) (G : Ω → ℝ) : ℝ :=
  ∑ ω, jaynesState K F theta ω * (G ω - jaynesExpectation K F theta G) ^ 2

theorem jaynesVariance_nonneg
    (K F : Ω → ℝ) (theta : ℝ) (G : Ω → ℝ) :
    0 ≤ jaynesVariance K F theta G := by
  unfold jaynesVariance
  refine Finset.sum_nonneg ?_
  intro ω _
  exact mul_nonneg (jaynesState_pos K F theta ω).le (sq_nonneg _)

theorem jaynesVariance_eq_second_moment_sub_sq
    (K F : Ω → ℝ) (theta : ℝ) (G : Ω → ℝ) :
    jaynesVariance K F theta G =
      jaynesExpectation K F theta (fun ω => G ω ^ 2) -
        (jaynesExpectation K F theta G) ^ 2 := by
  unfold jaynesVariance jaynesExpectation
  set μ : ℝ := ∑ ω', jaynesState K F theta ω' * G ω'
  have hsum :
      (∑ ω, jaynesState K F theta ω * (G ω - μ) ^ 2) =
        (∑ ω, jaynesState K F theta ω * G ω ^ 2) -
        2 * μ * (∑ ω, jaynesState K F theta ω * G ω) +
        μ ^ 2 * (∑ ω, jaynesState K F theta ω) := by
    have hpt : ∀ ω : Ω,
        jaynesState K F theta ω * (G ω - μ) ^ 2 =
          jaynesState K F theta ω * G ω ^ 2 -
            2 * μ * (jaynesState K F theta ω * G ω) +
            μ ^ 2 * jaynesState K F theta ω := by
      intro ω
      ring
    simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, jaynesState_sum_one]
  ring

theorem hasDerivAt_jaynesWeight
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    HasDerivAt (fun t => jaynesWeight K F t ω)
      (F ω * jaynesWeight K F theta ω) theta := by
  have hlin : HasDerivAt (fun t => -K ω + t * F ω) (0 + 1 * F ω) theta :=
    (hasDerivAt_const theta (-K ω)).add ((hasDerivAt_id theta).mul_const (F ω))
  have hlin' : HasDerivAt (fun t => -K ω + t * F ω) (F ω) theta := by
    simpa using hlin
  have hexp := (Real.hasDerivAt_exp (-K ω + theta * F ω)).comp theta hlin'
  refine hexp.congr_deriv ?_
  unfold jaynesWeight
  ring

theorem hasDerivAt_jaynesPartition
    (K F : Ω → ℝ) (theta : ℝ) :
    HasDerivAt (jaynesPartition K F)
      (∑ ω, F ω * jaynesWeight K F theta ω) theta := by
  change HasDerivAt (fun t => ∑ ω, jaynesWeight K F t ω)
    (∑ ω, F ω * jaynesWeight K F theta ω) theta
  exact HasDerivAt.fun_sum (fun ω _ => hasDerivAt_jaynesWeight K F theta ω)

/-- Jaynesian cumulant generating theorem: `d/dθ log Z(θ) = 𝔼_θ[F]`. -/
theorem hasDerivAt_log_jaynesPartition
    (K F : Ω → ℝ) (theta : ℝ) :
    HasDerivAt (fun t => Real.log (jaynesPartition K F t))
      (jaynesExpectation K F theta F) theta := by
  have hlog := (hasDerivAt_jaynesPartition K F theta).log (jaynesPartition_pos K F theta).ne'
  refine hlog.congr_deriv ?_
  unfold jaynesExpectation jaynesState
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro ω _
  ring

/-- Derivative of the Jaynes Gibbs weight `p_θ(ω)` with respect to `θ`. -/
theorem hasDerivAt_jaynesState
    (K F : Ω → ℝ) (theta : ℝ) (ω : Ω) :
    HasDerivAt (fun t => jaynesState K F t ω)
      (jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F)) theta := by
  have hnum := hasDerivAt_jaynesWeight K F theta ω
  have hden := hasDerivAt_jaynesPartition K F theta
  have hZ : jaynesPartition K F theta ≠ 0 := (jaynesPartition_pos K F theta).ne'
  have hdiv : HasDerivAt (fun t => jaynesState K F t ω)
      ((F ω * jaynesWeight K F theta ω * jaynesPartition K F theta -
          jaynesWeight K F theta ω * ∑ x, F x * jaynesWeight K F theta x) /
        jaynesPartition K F theta ^ 2) theta :=
    hnum.div hden hZ
  refine hdiv.congr_deriv ?_
  have hExp : (∑ x, F x * jaynesWeight K F theta x) / jaynesPartition K F theta =
      jaynesExpectation K F theta F := by
    unfold jaynesExpectation jaynesState
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  unfold jaynesState
  rw [← hExp]
  field_simp [hZ]

/-- Fisher–Jaynes susceptibility / convexity theorem:
`d/dθ 𝔼_θ[F] = d²/dθ² log Z(θ) = Var_θ(F) ≥ 0`. -/
theorem hasDerivAt_jaynesExpectation
    (K F : Ω → ℝ) (theta : ℝ) :
    HasDerivAt (fun t => jaynesExpectation K F t F)
      (jaynesVariance K F theta F) theta := by
  have hterm : ∀ ω ∈ (Finset.univ : Finset Ω),
      HasDerivAt (fun t => jaynesState K F t ω * F ω)
        (jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) * F ω) theta := by
    intro ω _
    exact (hasDerivAt_jaynesState K F theta ω).mul_const (F ω)
  have hsum : HasDerivAt (fun t => jaynesExpectation K F t F)
      (∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) * F ω) theta :=
    HasDerivAt.fun_sum hterm
  refine hsum.congr_deriv ?_
  have hzero :
      (∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, jaynesState_sum_one, one_mul]
    unfold jaynesExpectation
    ring
  calc
    (∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) * F ω)
        = (∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) * F ω) -
            jaynesExpectation K F theta F *
              (∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F)) := by
            rw [hzero, mul_zero, sub_zero]
    _ = ∑ ω, (jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) * F ω -
          jaynesExpectation K F theta F *
            (jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F))) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ∑ ω, jaynesState K F theta ω * (F ω - jaynesExpectation K F theta F) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          ring
    _ = jaynesVariance K F theta F := rfl

end InfoGeometry.Thermo
