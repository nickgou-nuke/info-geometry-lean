/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.PauliLubanskiFiniteBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Bridge.QuaternionicPauliDiracSoldering

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


abbrev PauliBlock := InfoGeometry.Bridge.QuaternionicPauliDiracSoldering.PauliBlock
abbrev WeylSpinor := InfoGeometry.Bridge.QuaternionicPauliDiracSoldering.WeylSpinor

noncomputable def spinHalfCasimir : PauliBlock := (3 / 4 : ℂ) • (1 : PauliBlock)

theorem spinHalfCasimir_eq_three_quarters :
    spinHalfCasimir = (3 / 4 : ℂ) • (1 : PauliBlock) := rfl

end InfoGeometry.Bridge.OperatorPauliLubanskiLift
