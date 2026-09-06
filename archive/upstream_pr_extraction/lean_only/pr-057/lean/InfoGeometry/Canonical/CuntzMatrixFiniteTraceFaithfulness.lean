import InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

/-!
# Finite faithfulness of the normalized matrix trace

This owner stays at the finite matrix level. It proves the exact
nondegeneracy statement needed by the algebraic GNS quotient, without
introducing an order or C*-structure on the infinite direct limit.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open Matrix

theorem matrixTrace_star_mul_self_re_eq_sum_normSq
    (n : ℕ) (A : MatrixStage n) :
    (Matrix.trace (star A * A)).re =
      ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
  dsimp [Matrix.trace, Matrix.mul_apply, star, conjTranspose_apply]
  have h_elem (k i : Fin (2 ^ n)) :
      (starRingEnd ℂ (A k i) * A k i).re = Complex.normSq (A k i) := by
    rw [mul_comm, Complex.mul_conj]
    rfl
  have h_sum2 (i : Fin (2 ^ n)) :
      (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i).re =
        ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
    have h_map := map_sum Complex.reAddGroupHom
      (fun k => starRingEnd ℂ (A k i) * A k i) Finset.univ
    change Complex.reAddGroupHom
        (∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) =
      ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
    rw [h_map]
    congr 1
    ext k
    exact h_elem k i
  have h_map := map_sum Complex.reAddGroupHom
    (fun i => ∑ k : Fin (2 ^ n), starRingEnd ℂ (A k i) * A k i) Finset.univ
  change Complex.reAddGroupHom
      (∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n),
        starRingEnd ℂ (A k i) * A k i) =
    ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i)
  rw [h_map]
  congr 1
  ext i
  exact h_sum2 i

theorem matrixTraceState_star_mul_self_im_zero
    (n : ℕ) (A : MatrixStage n) :
    (matrixTraceState n (star A * A)).im = 0 := by
  have hcast : (1 / (2 ^ n : ℂ)) =
      ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  have ht := matrixTrace_star_mul_self_im_zero n A
  rw [matrixTraceState_apply, hcast]
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
  rw [ht]
  simp

/-- 🏆 THEOREM: Explicit normalized real-part quadratic identity on MatrixStage n. -/
theorem matrixTraceState_star_mul_self_re_eq
    (n : ℕ) (A : MatrixStage n) :
    (matrixTraceState n (star A * A)).re =
      (1 / (2 ^ n : ℝ)) *
        ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) := by
  rw [matrixTraceState_apply, Complex.mul_re]
  have hcast : (1 / (2 ^ n : ℂ)) = (((1 / (2 ^ n : ℝ) : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [matrixTrace_star_mul_self_re_eq_sum_normSq]

/-- 🏆 THEOREM: Nonnegativity of the normalized matrix trace on star A * A. -/
theorem matrixTraceState_star_mul_self_re_nonneg
    (n : ℕ) (A : MatrixStage n) :
    0 ≤ (matrixTraceState n (star A * A)).re := by
  rw [matrixTraceState_star_mul_self_re_eq]
  have hcoeff : 0 ≤ (1 / (2 ^ n : ℝ)) := by positivity
  have hsum : 0 ≤ ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  exact mul_nonneg hcoeff hsum

/-- 🏆 THEOREM: Faithfulness / Nondegeneracy of matrixTraceState on MatrixStage n. -/
theorem matrixTraceState_star_mul_self_eq_zero_iff
    (n : ℕ) (A : MatrixStage n) :
    matrixTraceState n (star A * A) = 0 ↔ A = 0 := by
  constructor
  · intro hzero
    have h_re_zero :
        (matrixTraceState n (star A * A)).re = 0 := by
      rw [hzero]
      rfl
    have h_sum :
        ∑ i : Fin (2 ^ n), ∑ k : Fin (2 ^ n), Complex.normSq (A k i) = 0 := by
      rw [matrixTraceState_star_mul_self_re_eq] at h_re_zero
      have h_coeff : (1 / (2 ^ n : ℝ)) > 0 := by positivity
      nlinarith
    have h_outer : ∀ i : Fin (2 ^ n),
        ∑ k : Fin (2 ^ n), Complex.normSq (A k i) = 0 := by
      intro i
      have hnonneg : ∀ j : Fin (2 ^ n), j ∈ (Finset.univ : Finset (Fin (2 ^ n))) →
          0 ≤ ∑ k : Fin (2 ^ n), Complex.normSq (A k j) := by
        intro j _
        exact Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h_sum i
        (Finset.mem_univ i)
    ext i j
    have h_inner : Complex.normSq (A i j) = 0 := by
      have hnonneg : ∀ k : Fin (2 ^ n), k ∈ (Finset.univ : Finset (Fin (2 ^ n))) →
          0 ≤ Complex.normSq (A k j) := by
        intro k _
        exact Complex.normSq_nonneg _
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (h_outer j) i
        (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp h_inner
  · intro hA
    subst A
    simp

/-- 🏆 THEOREM: Strict positivity of the trace on non-zero matrices. -/
theorem matrixTraceState_star_mul_self_re_pos_of_ne_zero
    (n : ℕ) {A : MatrixStage n} (hA : A ≠ 0) :
    0 < (matrixTraceState n (star A * A)).re := by
  have hnonneg := matrixTraceState_star_mul_self_re_nonneg n A
  have hne : (matrixTraceState n (star A * A)).re ≠ 0 := by
    intro h_zero
    have h_state_zero : matrixTraceState n (star A * A) = 0 := by
      apply Complex.ext
      · exact h_zero
      · exact matrixTraceState_star_mul_self_im_zero n A
    have h_A_zero := (matrixTraceState_star_mul_self_eq_zero_iff n A).mp h_state_zero
    exact hA h_A_zero
  exact lt_of_le_of_ne hnonneg hne.symm

end InfoGeometry.Canonical.CuntzMatrixFiniteTraceFaithfulness
