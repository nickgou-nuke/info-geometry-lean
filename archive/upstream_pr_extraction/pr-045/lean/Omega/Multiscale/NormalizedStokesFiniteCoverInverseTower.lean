import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Multiscale

noncomputable section

/-- Concrete finite-cover inverse-tower data for normalized bulk, boundary, and differential
integrals. -/
structure NormalizedStokesFiniteCoverInverseTowerSystem where
  coverDegree : ℕ → ℕ
  bulkIntegral : ℕ → ℝ
  boundaryIntegral : ℕ → ℝ
  differentialIntegral : ℕ → ℝ

namespace NormalizedStokesFiniteCoverInverseTowerSystem

def cumulativeCoverDegree (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) fun j => (S.coverDegree j : ℝ)

def normalizedBulk (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.bulkIntegral n / cumulativeCoverDegree S n

def normalizedBoundary (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.boundaryIntegral n / cumulativeCoverDegree S n

def normalizedDifferential (S : NormalizedStokesFiniteCoverInverseTowerSystem) (n : ℕ) : ℝ :=
  S.differentialIntegral n / cumulativeCoverDegree S n

lemma cumulativeCoverDegree_pos (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n) (n : ℕ) :
    0 < cumulativeCoverDegree S n := by
  unfold cumulativeCoverDegree
  refine Finset.prod_pos ?_
  intro i hi
  have hdeg_pos_nat : 0 < S.coverDegree i := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (coverDegree_two_le i)
  exact_mod_cast hdeg_pos_nat

lemma normalizedBulk_step (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n)
    (bulkPullback : ∀ n, S.bulkIntegral (n + 1) = (S.coverDegree n : ℝ) * S.bulkIntegral n)
    (n : ℕ) : normalizedBulk S (n + 1) = normalizedBulk S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 :=
    (cumulativeCoverDegree_pos S coverDegree_two_le n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedBulk
  rw [bulkPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedBoundary_step (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n)
    (boundaryPullback :
      ∀ n, S.boundaryIntegral (n + 1) = (S.coverDegree n : ℝ) * S.boundaryIntegral n)
    (n : ℕ) : normalizedBoundary S (n + 1) = normalizedBoundary S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 :=
    (cumulativeCoverDegree_pos S coverDegree_two_le n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedBoundary
  rw [boundaryPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedDifferential_step (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n)
    (differentialPullback :
      ∀ n, S.differentialIntegral (n + 1) =
        (S.coverDegree n : ℝ) * S.differentialIntegral n)
    (n : ℕ) : normalizedDifferential S (n + 1) = normalizedDifferential S n := by
  have hCum :
      cumulativeCoverDegree S (n + 1) =
        cumulativeCoverDegree S n * (S.coverDegree n : ℝ) := by
    unfold cumulativeCoverDegree
    rw [Finset.prod_range_succ]
  have hCumNz : cumulativeCoverDegree S n ≠ 0 :=
    (cumulativeCoverDegree_pos S coverDegree_two_le n).ne'
  have hDegPosNat : 0 < S.coverDegree n := by
    exact lt_of_lt_of_le (by decide : 0 < 2) (coverDegree_two_le n)
  have hDegNz : (S.coverDegree n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hDegPosNat
  unfold normalizedDifferential
  rw [differentialPullback n, hCum]
  field_simp [hCumNz, hDegNz]

lemma normalizedStokes_levelwise (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (levelwiseStokes : ∀ n, S.differentialIntegral n = S.boundaryIntegral n) (n : ℕ) :
    normalizedDifferential S n = normalizedBoundary S n := by
  unfold normalizedDifferential normalizedBoundary
  rw [levelwiseStokes n]

end NormalizedStokesFiniteCoverInverseTowerSystem

open NormalizedStokesFiniteCoverInverseTowerSystem

/-- Pullback scaling by covering degree makes the normalized finite-level integrals invariant. -/
theorem paper_app_normalized_stokes_finite_cover_inverse_tower
    (S : NormalizedStokesFiniteCoverInverseTowerSystem)
    (coverDegree_two_le : ∀ n, 2 ≤ S.coverDegree n)
    (bulkPullback : ∀ n, S.bulkIntegral (n + 1) =
      (S.coverDegree n : ℝ) * S.bulkIntegral n)
    (boundaryPullback : ∀ n, S.boundaryIntegral (n + 1) =
      (S.coverDegree n : ℝ) * S.boundaryIntegral n)
    (differentialPullback : ∀ n, S.differentialIntegral (n + 1) =
      (S.coverDegree n : ℝ) * S.differentialIntegral n)
    (levelwiseStokes : ∀ n, S.differentialIntegral n = S.boundaryIntegral n) :
    (∀ n, normalizedBulk S (n + 1) = normalizedBulk S n) ∧
      (∀ n, normalizedBoundary S (n + 1) = normalizedBoundary S n) ∧
      (∀ n, normalizedDifferential S (n + 1) = normalizedDifferential S n) ∧
      (∀ n, normalizedDifferential S n = normalizedBoundary S n) := by
  exact ⟨normalizedBulk_step S coverDegree_two_le bulkPullback,
    normalizedBoundary_step S coverDegree_two_le boundaryPullback,
    normalizedDifferential_step S coverDegree_two_le differentialPullback,
    normalizedStokes_levelwise S levelwiseStokes⟩

end

end Omega.Multiscale
