import InfoGeometry.Algebra.Zorn.G2NativeCellDecomposition

/-!
# The unique Bruhat cell is preserved by PC peeling

Contract: on the native split-octonion automorphism group over F₂, the input
and its full peel belong to exactly the same one of the twelve concrete
Bruhat cells. This classifies the cell, not the two Borel factors inside it.
Dependencies: native disjoint-cell decomposition and same-cell preservation.
No Weyl-only residual hypothesis or external cardinality assumption is used.
-/

namespace InfoGeometry.Algebra.Zorn.G2FullPeelCellClassification

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open G2TwoPCRecovery G2TwoBruhatClassification G2QuotientOrbitSeparation

theorem exists_unique_common_cell (g : SplitOctF2Aut) :
    ∃! k : Fin 12,
      g ∈ concreteBruhatCell (orbitWeylRepresentative k) ∧
      fullPeel g ∈ concreteBruhatCell (orbitWeylRepresentative k) := by
  obtain ⟨k, hk, huniq⟩ := G2NativeCellDecomposition.exists_unique_cell g
  exact ⟨k, ⟨hk, fullPeel_mem_same_concreteBruhatCell hk⟩,
    fun j hj => huniq j hj.1⟩

theorem fullPeel_mem_cell_iff (g : SplitOctF2Aut) (k : Fin 12) :
    fullPeel g ∈ concreteBruhatCell (orbitWeylRepresentative k) ↔
      g ∈ concreteBruhatCell (orbitWeylRepresentative k) := by
  constructor
  · intro hk
    obtain ⟨j, hj, _⟩ := exists_unique_common_cell g
    obtain ⟨i, _, huniq⟩ := G2NativeCellDecomposition.exists_unique_cell (fullPeel g)
    have hkj : k = j := (huniq k hk).trans (huniq j hj.2).symm
    simpa only [hkj] using hj.1
  · exact fullPeel_mem_same_concreteBruhatCell

end InfoGeometry.Algebra.Zorn.G2FullPeelCellClassification
