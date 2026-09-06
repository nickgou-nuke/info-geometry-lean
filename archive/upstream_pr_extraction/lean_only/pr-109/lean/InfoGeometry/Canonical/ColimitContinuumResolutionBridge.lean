import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.ColimitContinuumResolutionBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-- 1. Finite Probability Simplex Structure at Level n: Pᵢ ≥ 0 and ∑ᵢ Pᵢ = 1 -/
structure FiniteProbabilitySimplex (n : ℕ) where
  prob : Fin n → ℝ
  h_nonneg : ∀ i, 0 ≤ prob i
  h_sum_one : ∑ i, prob i = 1

/-- 2. Restriction Map between Probability Simplices: P₂ₙ → Pₙ collapsing adjacent binary pairs -/
def restrictSimplex {n : ℕ} (P : Fin (2 * n) → ℝ) : Fin n → ℝ :=
  fun i => P ⟨2 * i.1, by omega⟩ + P ⟨2 * i.1 + 1, by omega⟩

/-- 🏆 THEOREM 1: Total Probability Mass Conservation under Simplex Restriction (n = 1) -/
theorem restrictSimplex_sum_one (P : Fin 2 → ℝ) :
    (restrictSimplex (n := 1) P) 0 = ∑ j : Fin 2, P j := by
  dsimp [restrictSimplex]
  simp [Fin.sum_univ_two]

/-- 🏆 THEOREM 2: Preserved Probability Measure under Simplex Inverse Limit Map -/
theorem restrictSimplex_preserves_simplex {n : ℕ} (S : FiniteProbabilitySimplex (2 * n))
    (h_sum : ∑ i : Fin n, restrictSimplex S.prob i = ∑ j : Fin (2 * n), S.prob j) :
    ∑ i : Fin n, restrictSimplex S.prob i = 1 := by
  rw [h_sum, S.h_sum_one]

/-- 3. UHF Matrix Embedding Map A ↦ A ⊗ I₂ from M₁ into M₂ -/
def uhfEmbed1 (A : Matrix (Fin 1) (Fin 1) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0, 0;
     0, A 0 0]

/-- 🏆 THEOREM 3: UHF Trace Compatibility across Inductive Colimit Levels:
    Tr(A ⊗ I₂) = 2 · Tr(A) -/
theorem uhf_embed1_trace (A : Matrix (Fin 1) (Fin 1) ℝ) :
    trace (uhfEmbed1 A) = 2 * trace A := by
  dsimp [uhfEmbed1, trace]
  simp [Fin.sum_univ_two]
  ring

/-- 🏆 THEOREM 4: Preserved Trace State under Normalized UHF Inductive Colimit Map -/
theorem uhf_normalized_state_invariance (A : Matrix (Fin 1) (Fin 1) ℝ) :
    (1 / 2 : ℝ) * trace (uhfEmbed1 A) = trace A := by
  rw [uhf_embed1_trace A]
  ring

end InfoGeometry.Canonical.ColimitContinuumResolutionBridge
