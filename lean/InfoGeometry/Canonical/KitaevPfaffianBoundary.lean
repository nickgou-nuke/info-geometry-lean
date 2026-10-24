/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Volume.OrientedPfaffian
import InfoGeometry.Canonical.KitaevChainKernel

/-! An unpaired endpoint kills every signed matching term of the actual
full chain coefficient matrix. This concerns coefficient matrices, not the
state-space kernel of the many-body operator. -/
noncomputable section
namespace InfoGeometry.Canonical.KitaevPfaffianBoundary
open InfoGeometry.Volume.OrientedPfaffian
open KitaevChainCoefficients KitaevChainKernel
open scoped BigOperators

theorem matchingWeight_zero_of_zero_row {n : ℕ}
    (K : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hK : IsSkew K)
    (i : Fin (2*n)) (hi : ∀ j, K i j = 0) (M : PerfectMatching n) :
    M.matchingWeight K = 0 := by
  unfold PerfectMatching.matchingWeight
  apply Finset.prod_eq_zero_iff.mpr
  rcases lt_or_gt_of_ne (Ne.symm (M.partner_ne_self i)) with h | h
  · exact ⟨i, (M.mem_leftEndpoints i).mpr h, hi _⟩
  · refine ⟨M.partner i, (M.mem_leftEndpoints _).mpr ?_, ?_⟩
    · simpa using h
    · rw [M.partner_partner, hK, hi, neg_zero]

theorem orientedPfaffian_zero_of_zero_row {n : ℕ}
    (K : Matrix (Fin (2*n)) (Fin (2*n)) ℝ) (hK : IsSkew K)
    (i : Fin (2*n)) (hi : ∀ j, K i j = 0) :
    orientedPfaffian n K = 0 := by
  apply Finset.sum_eq_zero
  intro M _
  rw [matchingWeight_zero_of_zero_row K hK i hi M, mul_zero]

theorem chain_endpoint_row_zero {N : ℕ} (t : ℝ) (i : Fin (2*N))
    (hi : i.val = 0 ∨ i.val + 1 = 2*N) (j : Fin (2*N)) :
    chainCoefficientMatrix N t i j = 0 := by
  have h := chain_action_endpoint t (Pi.single j 1) i hi
  simpa using h

theorem chain_orientedPfaffian_zero {N : ℕ} (hN : 0 < N) (t : ℝ) :
    orientedPfaffian N (chainCoefficientMatrix N t) = 0 :=
  orientedPfaffian_zero_of_zero_row _ (chainCoefficientMatrix_skew N t)
    ⟨0, Nat.mul_pos (by decide) hN⟩ (chain_endpoint_row_zero t _ (Or.inl rfl))

end InfoGeometry.Canonical.KitaevPfaffianBoundary
