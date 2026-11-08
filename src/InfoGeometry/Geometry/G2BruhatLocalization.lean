import InfoGeometry.GroupTheory.DoubleCoset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic

namespace InfoGeometry.Geometry.G2Bruhat

variable {G IndexType CellType WordType : Type*}

/-!
# Generic Bruhat-cell localization

This theorem isolates the logical step used by the concrete quotient table:
disjoint cells force equal representatives to have a common cell.  The
remaining residual-word alignment is deliberately an explicit hypothesis.
-/

theorem weyl_cell_localization_of_quotient_equality
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
      i ∈ orbitCells k ∧ j ∈ orbitCells k ∧
        residualWord k i = residualWord k j := by
  obtain ⟨kᵢ, hki⟩ := h_cover i
  obtain ⟨kⱼ, hkj⟩ := h_cover j
  have hcell : kᵢ = kⱼ := by
    by_contra hne
    have hd := cell_disjoint kᵢ kⱼ i j hki hkj hne
    rw [h_eq] at hd
    obtain ⟨g, hg⟩ := repr_nonempty j
    exact Set.disjoint_left.1 hd hg hg
  subst kⱼ
  exact ⟨kᵢ, hki, hkj, h_residual_align kᵢ i j hki hkj h_eq⟩

end InfoGeometry.Geometry.G2Bruhat
