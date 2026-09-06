import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import InfoGeometry.Canonical.ZornVectorMatrixRationalEquiv
import InfoGeometry.Physics.BdGChiralBlockMatrix

namespace InfoGeometry.Canonical

open scoped TensorProduct

/-- The rational tensor-product carrier combining the native eight-slot
split-octonion coordinates with a finite BdG matrix coefficient space. -/
abbrev SplitOctonionBdGCarrier :=
  StandardRationalSplitOctonion ⊗[ℚ] InfoGeometry.Physics.BdGBlock ℚ

@[simp] theorem finrank_splitOctonionBdGCarrier :
    Module.finrank ℚ SplitOctonionBdGCarrier = 32 := by
  have hcard : Fintype.card IntegralSplitBasis = 8 := by native_decide
  rw [Module.finrank_tensorProduct]
  simp [StandardRationalSplitOctonion,
    Module.finrank_pi, InfoGeometry.Physics.BdGBlock,
    Module.finrank_matrix, hcard]

end InfoGeometry.Canonical
