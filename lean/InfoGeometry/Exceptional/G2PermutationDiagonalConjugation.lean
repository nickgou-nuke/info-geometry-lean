/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Exceptional.G2ArtinRootPermutationLift

namespace InfoGeometry.Exceptional.G2PermutationDiagonalConjugation

open InfoGeometry.Exceptional.G2ArtinRootLift

abbrev Root := InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction.G2CoordinateRoot

/-- 🏆 THEOREM: Permutation conjugation of a diagonal phase operator permutes the diagonal entries by $\pi^{-1}$:
    $$P_\pi D(\phi) P_\pi^{-1} = D(\phi \circ \pi^{-1})$$ -/
theorem permMatrix_conj_diagonal
    (π : Equiv.Perm Root) (phase : Root → ℂ) :
    permMatrix π * Matrix.diagonal phase * permMatrix π⁻¹ =
      Matrix.diagonal (phase ∘ (π⁻¹ : Equiv.Perm Root)) := by
  ext i j
  simp only [Matrix.mul_apply, permMatrix_apply, Matrix.diagonal_apply]
  have h_inner : ∀ x : Root, (∑ x_1 : Root, (if π x_1 = i then (1 : ℂ) else 0) * if x_1 = x then phase x_1 else 0) =
      if π x = i then phase x else 0 := by
    intro x
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
      by_cases h : π x = i
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    · intro l _ hl
      rw [if_neg hl, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  simp_rw [h_inner]
  rw [Finset.sum_eq_single (π⁻¹ j)]
  · rw [if_pos rfl, mul_one]
    have heq : π (π⁻¹ j) = j := Equiv.apply_symm_apply π j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hpi : π (π⁻¹ i) = i := Equiv.apply_symm_apply π i
      rw [if_pos hpi]
      rfl
    · rw [if_neg hij]
      have hneq : π (π⁻¹ j) ≠ i := by
        rw [heq]
        exact fun h => hij h.symm
      rw [if_neg hneq]
  · intro x _ hx
    have hzero : (if π⁻¹ j = x then (1 : ℂ) else 0) = 0 := if_neg (Ne.symm hx)
    rw [hzero, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end InfoGeometry.Exceptional.G2PermutationDiagonalConjugation
