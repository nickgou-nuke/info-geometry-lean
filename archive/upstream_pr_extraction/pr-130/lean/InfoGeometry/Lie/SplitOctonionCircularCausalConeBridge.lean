import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Algebra.RealPauliCausalCone

namespace InfoGeometry.Lie.SplitOctonionCircularCausalConeBridge

open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Algebra.RealPauliCausalCone

/-- The circular null cone in the 8D coordinate space. -/
def circularNullCone : Set Coord :=
  { x | circularWittQuadratic x = 0 }

/-- The Minkowski null cone in the 4D coordinate space. -/
def minkowskiNullCone : Set (Fin 4 → ℝ) :=
  { u | u 0 * u 0 - (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) = 0 }

/-- The restriction of the quadratic form to the diagonal Minkowski embedding. -/
theorem minkowskiDiagonal_quadratic (u : Fin 4 → ℝ) :
    circularWittQuadratic (minkowskiDiagonalEmbedding u) =
      u 0 * u 0 - (u 1 * u 1 + u 2 * u 2 + u 3 * u 3) :=
  circularWittQuadratic_minkowskiDiagonal u

/-- A vector is in the Minkowski null cone iff its diagonal embedding is in the circular null cone. -/
theorem minkowskiNull_iff_circularNull (u : Fin 4 → ℝ) :
    u ∈ minkowskiNullCone ↔ minkowskiDiagonalEmbedding u ∈ circularNullCone := by
  dsimp [minkowskiNullCone, circularNullCone]
  rw [minkowskiDiagonal_quadratic u]

/-- Map a Real Pauli operator to the 8D coordinate space via the diagonal embedding. -/
noncomputable def pauliToDiagonal (X : RealPauliOp) : Coord :=
  minkowskiDiagonalEmbedding (fun i =>
    if i = 0 then X.t
    else if i = 1 then X.x
    else if i = 2 then X.y
    else X.z)

/-- The Minkowski determinant of a Real Pauli operator equals the circular Witt quadratic form of its diagonal embedding. -/
theorem pauliDet_eq_circularQuadratic_onDiagonal (X : RealPauliOp) :
    detMinkowski X = circularWittQuadratic (pauliToDiagonal X) := by
  dsimp [detMinkowski, pauliToDiagonal]
  rw [minkowskiDiagonal_quadratic]
  simp
  ring

end InfoGeometry.Lie.SplitOctonionCircularCausalConeBridge
