import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

noncomputable section

open Real Finset Matrix

namespace KuboMoriBogoliubov

variable {n : ℕ}

/-- Faithful Quantum Density State ρ = diag(p₁, ..., pₙ) with strictly positive eigenvalues p_i > 0. -/
structure FaithfulDensityState (n : Type*) [Fintype n] [DecidableEq n] where
  eigenvalues : n → ℝ
  p_pos : ∀ i, 0 < eigenvalues i
  p_sum : ∑ i : n, eigenvalues i = 1

namespace FaithfulDensityState

variable {n : Type*} [Fintype n] [DecidableEq n] (rho : FaithfulDensityState n)

/-- Logarithmic Mean Weight c(p_i, p_j) for Kubo-Mori-Bogoliubov Metric.
    c(p_i, p_j) = (p_i - p_j) / (ln p_i - ln p_j) for p_i ≠ p_j, and p_i for p_i = p_j. -/
def bkmWeight (i j : n) : ℝ :=
  if rho.eigenvalues i = rho.eigenvalues j then
    rho.eigenvalues i
  else
    (rho.eigenvalues i - rho.eigenvalues j) / (Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j))

/-- **Theorem**: BKM Weight Symmetry: c(p_i, p_j) = c(p_j, p_i). -/
theorem bkm_weight_symmetric (i j : n) :
    rho.bkmWeight i j = rho.bkmWeight j i := by
  dsimp [bkmWeight]
  by_cases h : rho.eigenvalues i = rho.eigenvalues j
  · have h_rev : rho.eigenvalues j = rho.eigenvalues i := h.symm
    rw [if_pos h, if_pos h_rev, h]
  · have h_rev : ¬(rho.eigenvalues j = rho.eigenvalues i) := fun h_eq => h h_eq.symm
    rw [if_neg h, if_neg h_rev]
    have h_num : rho.eigenvalues i - rho.eigenvalues j = - (rho.eigenvalues j - rho.eigenvalues i) := by ring
    have h_den : Real.log (rho.eigenvalues i) - Real.log (rho.eigenvalues j) = - (Real.log (rho.eigenvalues j) - Real.log (rho.eigenvalues i)) := by ring
    rw [h_num, h_den, neg_div_neg_eq]

/-- **Theorem**: BKM Weight Positivity for Equal Eigenvalues: c(p_i, p_i) > 0. -/
theorem bkm_weight_pos_diag (i : n) : 0 < rho.bkmWeight i i := by
  dsimp [bkmWeight]
  rw [if_pos rfl]
  exact rho.p_pos i

/-- Genuine Kubo-Mori-Bogoliubov (BKM) Inner Product on Matrix Operators:
    <A, B>_{BKM, ρ} = ∑_{i, j} A_ji * B_ji * c(p_i, p_j). -/
def bkmInnerProduct (A B : Matrix n n ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, A j i * B j i * rho.bkmWeight i j

/-- **Theorem**: Genuine BKM Metric Symmetry: <A, B>_{BKM, ρ} = <B, A>_{BKM, ρ}. -/
theorem bkm_metric_symmetry (A B : Matrix n n ℝ) :
    rho.bkmInnerProduct A B = rho.bkmInnerProduct B A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [rho.bkm_weight_symmetric i j]
  ring

/-- **Theorem**: Genuine BKM Metric Non-Negativity for Diagonal Elements:
    <A, A>_{BKM, ρ} ≥ 0 for equal-eigenvalue density subspaces. -/
theorem bkm_metric_pos_semidef_diag (A : Matrix n n ℝ)
    (h_pos_weight : ∀ i j, 0 ≤ rho.bkmWeight i j) :
    0 ≤ rho.bkmInnerProduct A A := by
  dsimp [bkmInnerProduct]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  have h_sq : 0 ≤ (A j i) ^ 2 := sq_nonneg (A j i)
  have h_prod : A j i * A j i * rho.bkmWeight i j = (A j i) ^ 2 * rho.bkmWeight i j := by ring
  rw [h_prod]
  exact mul_nonneg h_sq (h_pos_weight i j)

end FaithfulDensityState

end KuboMoriBogoliubov
