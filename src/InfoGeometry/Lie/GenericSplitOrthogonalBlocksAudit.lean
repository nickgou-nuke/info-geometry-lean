import InfoGeometry.Lie.GenericSplitOrthogonalBlocks
import InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

/-! Kernel audit surface for the finite neutral-Witt block criterion. -/

namespace InfoGeometry.Lie.GenericSplitOrthogonalBlocks.Audit

open InfoGeometry.Lie.GenericSplitOrthogonalBlocks
open InfoGeometry.Lie.SplitOctonionWittEndomorphismBlockBridge

/-- The generic theorem specializes to the existing fixed `n = 4` owner. -/
theorem fixedFourCriterion_via_generic (M : WittBlockMatrix) :
    SplitOctonionWittEndomorphismBlockBridge.IsWittSkew M ↔
      SplitOctonionWittEndomorphismBlockBridge.IsWittOrthogonalLie M := by
  let X : BlockData 4 := ⟨M.A, M.B, M.C, M.D⟩
  change InfoGeometry.Lie.GenericSplitOrthogonalBlocks.IsWittSkew 4 X ↔
    InfoGeometry.Lie.GenericSplitOrthogonalBlocks.HasWittLieBlocks 4 X
  exact isWittSkew_iff_hasWittLieBlocks 4 X

#check isWittSkew_iff_hasWittLieBlocks
#print axioms isWittSkew_iff_hasWittLieBlocks
#check splitOrthogonalLieSubalgebra
#check mem_splitOrthogonalLieSubalgebra_iff
#print axioms mem_splitOrthogonalLieSubalgebra_iff
#check toMatrix_mem_splitOrthogonalLieSubalgebra_iff
#print axioms toMatrix_mem_splitOrthogonalLieSubalgebra_iff
#print axioms toMatrix_cartanThetaBlocks
#print axioms cartanThetaBlocks_preserves
#print axioms cartanThetaBlocks_involutive
#print axioms cartanThetaBlocks_maps_lieCarrier
#check fixedFourCriterion_via_generic
#print axioms fixedFourCriterion_via_generic

end InfoGeometry.Lie.GenericSplitOrthogonalBlocks.Audit
