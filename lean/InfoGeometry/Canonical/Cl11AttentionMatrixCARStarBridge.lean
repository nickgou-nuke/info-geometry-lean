/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11AttentionMatrixCARBridge

/-!
# Star preservation for the algebraic Clifford-to-matrix-carrier map

This file proves that the existing ring map from the real algebraic direct
limit to the complex algebraic matrix direct limit preserves the stagewise
star operation. It makes no completion, equivalence, or modular-flow claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11AttentionMatrixCARStarBridge

open InfoGeometry.Canonical.Cl11AttentionMatrixCARBridge
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit

/-- The existing real-to-complex algebraic direct-limit ring map preserves
the involutions induced stagewise by matrix star. -/
theorem clLimitToComplexCarrier_star
    (x : InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.ClLimit) :
    clLimitToComplexCarrier (star x) = star (clLimitToComplexCarrier x) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change clLimitToComplexCarrier (ofStage n (star A)) =
        star (clLimitToComplexCarrier (ofStage n A))
      rw [clLimitToComplexCarrier_stage, clLimitToComplexCarrier_stage]
      rw [coherentComplexifyClStage_star, stageInjection_star]

/-- The same existing carrier map, packaged as a non-unital star-ring
homomorphism. -/
noncomputable def clLimitToComplexCarrierStarHom :
    InfoGeometry.Canonical.Cl11FermionicFockOperatorTowerEquivalence.ClLimit →⋆ₙ+* Carrier where
  toNonUnitalRingHom := clLimitToComplexCarrier.toNonUnitalRingHom
  map_star' := clLimitToComplexCarrier_star

end InfoGeometry.Canonical.Cl11AttentionMatrixCARStarBridge
