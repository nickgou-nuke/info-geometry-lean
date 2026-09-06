import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

/-!
# Concrete Bruhat-cell invariance under left/right PC factors

This module adds the minimal membership-level bridge needed by downstream
Bruhat-index assembly theorems. It deliberately proves only that multiplying
an element already known to lie in a concrete Bruhat cell by left/right
unipotent (PC) factors keeps it in that same cell.

No total `bruhatIndex` function, global Bruhat coverage, or cell-disjointness
claim is introduced here.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatPCInvariance

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-- Left and right PC/Borel multiplication preserves membership in a concrete
Bruhat cell. This is the membership-level invariant needed before a total
Bruhat-index function is available. -/
theorem bruhatIndex_left_right_pc_invariant
    (w g uL uR : SplitOctF2Aut)
    (huL : uL ∈ sylowTwoSubgroup)
    (huR : uR ∈ sylowTwoSubgroup)
    (hg : g ∈ concreteBruhatCell w) :
    uL * g * uR ∈ concreteBruhatCell w := by
  apply concreteBruhatCell_right_mul w uR (uL * g) huR
  exact concreteBruhatCell_left_mul w uL g huL hg

/-- Specialized PC-word form of the same invariance. -/
theorem pcWord_left_right_preserves_concreteBruhatCell
    (w g : SplitOctF2Aut)
    (a d : Fin 6 → Bool)
    (hg : g ∈ concreteBruhatCell w) :
    pcWord a * g * pcWord d ∈ concreteBruhatCell w := by
  apply bruhatIndex_left_right_pc_invariant w g (pcWord a) (pcWord d)
  · exact pcWord_mem_sylow a
  · exact pcWord_mem_sylow d
  · exact hg

end InfoGeometry.Algebra.Zorn.G2BruhatPCInvariance
