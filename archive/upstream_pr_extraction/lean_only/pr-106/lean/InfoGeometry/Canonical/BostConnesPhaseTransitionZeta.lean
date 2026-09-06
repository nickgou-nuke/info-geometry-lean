import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.BostConnesPhaseTransitionZeta

/-!
# Finite weighted sequence readouts

This module defines a finite weighted sum on positive natural indices and
proves its linearity, positivity, and the value of the constant readout at a
two-term cutoff. It does not construct a C*-dynamical system, a KMS state,
a phase transition, or a zeta factorization.
-/

/-- A real-valued sequence indexed by positive natural numbers. -/
def BCSequence := ℕ+ → ℝ

/-- A finite weighted sum, with the zero index omitted. -/
def bcKMSStateTrunc (beta : ℝ) (N : ℕ) (f : BCSequence) : ℝ :=
  ∑ n ∈ Finset.range N, if h : 0 < n then f ⟨n, h⟩ * (n : ℝ) ^ (-beta) else 0

/-- Linearity of the finite weighted sum. -/
theorem bc_kms_state_trunc_linear (beta : ℝ) (N : ℕ) (a b : ℝ) (f g : BCSequence) :
    bcKMSStateTrunc beta N (fun n => a * f n + b * g n) =
      a * bcKMSStateTrunc beta N f + b * bcKMSStateTrunc beta N g := by
  dsimp [bcKMSStateTrunc]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext n
  split_ifs <;> ring

/-- Positivity of the finite weighted sum for pointwise nonnegative inputs. -/
theorem bc_kms_state_trunc_pos (beta : ℝ) (N : ℕ) (f : BCSequence) (h_pos : ∀ n, 0 ≤ f n) :
    0 ≤ bcKMSStateTrunc beta N f := by
  dsimp [bcKMSStateTrunc]
  apply Finset.sum_nonneg
  intro n _
  split_ifs with h
  · apply mul_nonneg
    · exact h_pos ⟨n, h⟩
    · positivity
  · rfl

/-- The constant readout has value one at the two-term cutoff. -/
theorem bc_kms_state_trunc_one_eq_one (beta : ℝ) :
    bcKMSStateTrunc beta 2 (fun _ => 1) = 1 := by
  dsimp [bcKMSStateTrunc]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp

end InfoGeometry.Canonical.BostConnesPhaseTransitionZeta
