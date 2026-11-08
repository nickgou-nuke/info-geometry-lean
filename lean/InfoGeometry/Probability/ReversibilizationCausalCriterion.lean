/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.FiniteMarkovReversibilization

/-!
# Exact triangular-support criterion for reversible averaging

On the existing real matrix carrier, positive weights and nonnegative entries
make each averaged edge vanish exactly when both directed edges vanish.
Consequently triangular support of the average forces the original matrix to
be diagonal. With unit row sums this is equivalent to the original matrix
being the identity. Neither stationarity nor triangularity of the input is
assumed. These statements concern the finite matrix averaging operation, not
an identification of attention operators with stochastic kernels.

Dependencies: weightedSelfPart_eq_zero_iff → triangular-support criterion →
unit-row-sum criterion.
-/

namespace InfoGeometry.Physics

variable {n : Type*} [LinearOrder n]

/-- Reversible averaging has triangular support exactly for diagonal input. -/
theorem weightedSelfPart_causal_iff (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, 0 < π i) (hP : ∀ i j, 0 ≤ P i j) :
    Probability.IsCausalLowerTriangular (weightedSelfPart π P) ↔
      ∀ i j, i ≠ j → P i j = 0 := by
  constructor
  · intro hc i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ((weightedSelfPart_eq_zero_iff π P hπ hP i j).mp (hc i j h)).1
    · exact ((weightedSelfPart_eq_zero_iff π P hπ hP j i).mp (hc j i h)).2
  · intro hd i j hij
    exact (weightedSelfPart_eq_zero_iff π P hπ hP i j).mpr
      ⟨hd i j (ne_of_lt hij), hd j i (ne_of_gt hij)⟩

/-- For unit-row-sum input, causal support survives averaging only at identity. -/
theorem weightedSelfPart_causal_rowSumOne_iff [Fintype n]
    (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, 0 < π i) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) :
    Probability.IsCausalLowerTriangular (weightedSelfPart π P) ↔ P = 1 := by
  rw [weightedSelfPart_causal_iff π P hπ hP]
  constructor
  · intro hd
    have hs : Probability.IsSymmetricMatrix P := by
      intro i j
      by_cases h : i = j
      · subst j; rfl
      · rw [hd i j h, hd j i (Ne.symm h)]
    have hc : Probability.IsCausalLowerTriangular P :=
      fun i j hij => hd i j (ne_of_lt hij)
    ext i j
    simpa only [Matrix.one_apply] using
      Probability.causalSymmetric_rowSumOne_eq_one P hs hc hrow i j
  · rintro rfl i j hij
    simp [hij]

end InfoGeometry.Physics
