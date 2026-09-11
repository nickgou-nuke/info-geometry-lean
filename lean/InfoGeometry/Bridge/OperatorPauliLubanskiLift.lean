import InfoGeometry.Physics.PauliLubanskiFiniteBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Canonical readback of the finite Pauli--Lubanski owner.  The bridge keeps
the existing `FourVector`/bivector carrier authoritative and adds no second
representation or analytic operator theory. -/

namespace InfoGeometry.Bridge.OperatorPauliLubanskiLift

open InfoGeometry.Physics.PauliLubanskiFiniteBridge
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Physics.ZornMatrixSU3

abbrev SpatialVector := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev Datum := LorentzBivectorDatum

theorem orthogonal (D : Datum) :
    minkowskiPair D.momentum (pauliLubanski D) = 0 :=
  pauliLubanski_orthogonal D

theorem rest_frame_square (m : ℝ) (J K : SpatialVector) :
    minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * InfoGeometry.Physics.ZornMatrixSU3.dotProduct J J :=
  pauliLubanski_rest_frame_square m J K

theorem rest_frame_massive_casimir
    (m s : ℝ) (J K : SpatialVector)
    (hJ : InfoGeometry.Physics.ZornMatrixSU3.dotProduct J J = s * (s + 1)) :
    minkowskiPair
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩)
        (pauliLubanski ⟨⟨m, 0, 0, 0⟩, J, K⟩) =
      -m ^ 2 * s * (s + 1) :=
  pauliLubanski_rest_frame_massive_casimir m s J K hJ

end InfoGeometry.Bridge.OperatorPauliLubanskiLift
