import InfoGeometry.GroupTheory.DoubleCoset
import Mathlib.Data.Set.Basic

namespace InfoGeometry.GroupTheory.G2BruhatLocalization

variable {G IndexType CellType WordType : Type*}

/-!
# Generic Bruhat-cell localization

This lemma isolates the set-theoretic step used by quotient alignment.  It
does not assert the concrete residual alignment itself: that remains a
separate certificate about the chosen `residualWord`.
-/

theorem cell_localization_of_equal_representatives
    (quotientRepresentative : IndexType → Set G)
    (orbitCells : CellType → Set IndexType)
    (residualWord : CellType → IndexType → WordType)
    (cell_disjoint : ∀ (k₁ k₂ : CellType) (i j : IndexType),
      i ∈ orbitCells k₁ → j ∈ orbitCells k₂ → k₁ ≠ k₂ →
        Disjoint (quotientRepresentative i) (quotientRepresentative j))
    (repr_nonempty : ∀ i : IndexType,
      (quotientRepresentative i).Nonempty)
    (i j : IndexType)
    (h_eq : quotientRepresentative i = quotientRepresentative j)
    (h_cover : ∀ i : IndexType, ∃ k : CellType, i ∈ orbitCells k)
    (h_residual_align : ∀ (k : CellType) (i j : IndexType),
      i ∈ orbitCells k → j ∈ orbitCells k →
        quotientRepresentative i = quotientRepresentative j →
        residualWord k i = residualWord k j) :
    ∃ k : CellType,
      i ∈ orbitCells k ∧
      j ∈ orbitCells k ∧
      residualWord k i = residualWord k j := by
  rcases h_cover i with ⟨kᵢ, hi⟩
  rcases h_cover j with ⟨kⱼ, hj⟩
  have hkj : kᵢ = kⱼ := by
    by_contra hne
    have hd := cell_disjoint kᵢ kⱼ i j hi hj hne
    rw [h_eq] at hd
    rcases repr_nonempty j with ⟨x, hx⟩
    have hempty : quotientRepresentative j ∩ quotientRepresentative j = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hd
    have hmem : x ∈ quotientRepresentative j ∩ quotientRepresentative j :=
      Set.mem_inter hx hx
    rw [hempty] at hmem
    exact hmem.elim
  refine ⟨kᵢ, hi, ?_, ?_⟩
  · simpa [hkj] using hj
  · exact h_residual_align kᵢ i j hi (by simpa [hkj] using hj) h_eq

end InfoGeometry.GroupTheory.G2BruhatLocalization
