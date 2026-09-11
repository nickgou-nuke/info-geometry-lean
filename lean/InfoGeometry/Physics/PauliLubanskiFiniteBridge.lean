import InfoGeometry.Physics.FourVectorPauliCasimirBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Pauli--Lubanski bridge

This owner records the algebraic Pauli--Lubanski readout in a finite
`3+1` decomposition.  It deliberately does not assert a Poincare
representation, self-adjoint generators, or an irreducible spin spectrum.
-/

noncomputable section

namespace InfoGeometry.Physics.PauliLubanskiFiniteBridge

open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Physics.ZornMatrixSU3

abbrev SpatialVector := InfoGeometry.Algebra.FiniteSpin.Vec3R

def spatialMomentum (P : FourVector) : SpatialVector :=
  ![P.x, P.y, P.z]

def spatialTriple (w : ℝ) (v : SpatialVector) : FourVector :=
  ⟨w, v 0, v 1, v 2⟩

structure LorentzBivectorDatum where
  momentum : FourVector
  rotation : SpatialVector
  boost : SpatialVector

/-! In the mostly-minus convention this is the standard finite split of
`W^μ = (p · J, E J + p × K)`, with the sign convention fixed by this owner. -/
def pauliLubanski (D : LorentzBivectorDatum) : FourVector :=
  spatialTriple (ZornMatrixSU3.dotProduct (spatialMomentum D.momentum) D.rotation)
    (D.momentum.t • D.rotation +
      ZornMatrixSU3.crossProduct (spatialMomentum D.momentum) D.boost)

theorem pauliLubanski_orthogonal (D : LorentzBivectorDatum) :
    minkowskiPair D.momentum (pauliLubanski D) = 0 := by
  rcases D with ⟨⟨E, px, py, pz⟩, J, K⟩
  simp [pauliLubanski, spatialMomentum, spatialTriple, minkowskiPair,
    ZornMatrixSU3.dotProduct, ZornMatrixSU3.crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  ring_nf

theorem pauliLubanski_square_is_second_casimir (D : LorentzBivectorDatum) :
    minkowskiSq (pauliLubanski D) =
      minkowskiPair (pauliLubanski D) (pauliLubanski D) :=
  rfl

/-! In the rest frame, the finite Pauli--Lubanski readout reduces to the
spatial rotation bivector.  This is the concrete algebraic source of the
massive second-Casimir expression; no spin-spectrum classification is assumed. -/
theorem pauliLubanski_rest_frame_square (m : ℝ) (J K : SpatialVector) :
    minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * ZornMatrixSU3.dotProduct J J := by
  simp [pauliLubanski, spatialMomentum, spatialTriple, minkowskiPair,
    ZornMatrixSU3.dotProduct, ZornMatrixSU3.crossProduct,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.dot3,
    InfoGeometry.Canonical.ZornVectorMatrixExplicit.cross3]
  ring

theorem pauliLubanski_rest_frame_massive_casimir
    (m s : ℝ) (J K : SpatialVector)
    (hJ : ZornMatrixSU3.dotProduct J J = s * (s + 1)) :
    minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * s * (s + 1) := by
  rw [pauliLubanski_rest_frame_square]
  rw [hJ]
  ring

end InfoGeometry.Physics.PauliLubanskiFiniteBridge
