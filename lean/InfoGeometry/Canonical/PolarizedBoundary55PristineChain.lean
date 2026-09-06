import InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
import InfoGeometry.Geometry.PolarizedBoundaryBivectors

/-!
# Quadratic extension, native Clifford action, and bivector readout

This aggregate supplies one focused target. The four-vector slots are neither
Weyl spinors nor operator coefficients unless an additional representation is
explicitly applied. No field equation, modular theorem, contact grading, or
Klein-bottle quotient is inferred from the coordinate identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.PolarizedBoundary55PristineChain

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.PolarizedMinkowski55
open InfoGeometry.Clifford.PolarizedBoundaryInvolutions
open InfoGeometry.Algebra.Zorn.PolarizedQuadraticExtension55
open InfoGeometry.Geometry.PolarizedBoundaryBivectors
open InfoGeometry.Canonical.HodgeStar4DFinite

/-- The old norm, the ten-dimensional quadratic form, and the native split form agree. -/
theorem zorn_quadratic_clifford_chain (X : NativeZorn) :
    Q55 (diagonalEquiv (zornEmbedding X)) =
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X ∧
      boundaryMatrixAction (zornEmbedding X) * boundaryMatrixAction (zornEmbedding X) =
        algebraMap ℝ _ (InfoGeometry.Algebra.Zorn.ZornMatrix.detZ X) := by
  constructor
  · rw [diagonalEquiv_quadratic, zornEmbedding_norm]
  · rw [boundaryMatrixAction_sq, zornEmbedding_norm]

/-- The source involution has a Clifford lift, but not a freely acting deck action. -/
theorem source_involution_packet (z : Boundary55) :
    boundaryQuadratic (mixedSwap z) = boundaryQuadratic z ∧
      mixedSwap (mixedSwap z) = z ∧
      mixedSwapClifford (mixedSwapClifford (CliffordAlgebra.ι boundaryQuadratic z)) =
        CliffordAlgebra.ι boundaryQuadratic z :=
  ⟨mixedSwap_preserves z, mixedSwap_sq z, mixedSwapClifford_sq _⟩

/-- The actual degree-two exterior readout has the existing complex chiral decomposition. -/
theorem boundary_chiral_packet (z : Boundary55) :
    selfDualPart (bivectorReadout (boundaryBivector z)) +
        antiSelfDualPart (bivectorReadout (boundaryBivector z)) =
          bivectorReadout (boundaryBivector z) ∧
      bivectorReadout (boundaryBivector (mixedSwap z)) =
        -bivectorReadout (boundaryBivector z) :=
  ⟨bivector_chiral_reconstruction _, mixedSwap_bivector z⟩

end InfoGeometry.Canonical.PolarizedBoundary55PristineChain
