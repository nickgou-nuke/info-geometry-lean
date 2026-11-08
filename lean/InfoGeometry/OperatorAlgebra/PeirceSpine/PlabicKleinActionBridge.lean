/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.PositroidClusterTwistPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.TetraktysKleinActionBridge

/-!
# Peirce parity transports the plabic boundary/null-space splitting

The same parity automorphism used in the tetraktys Klein action transports the
plabic boundary idempotent and its complementary twistor operator to the
sign-reversed bridge chart. This is a same-carrier operator theorem; it does
not identify the finite Penrose incidence carrier or doubled Hilbert space
with this ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]
variable {P : B} (hP : P * P = P) (A C : B)

/-- The parity automorphism fixes the two Peirce diagonal corners and negates
each directed off-diagonal bridge. -/
theorem parity_transports_plabic_boundary_and_nullspace
    (Z : B) :
    parityConjRingEquiv hP (plabicBoundaryOp P A C) =
        plabicBoundaryOp P (-A) (-C) ∧
    parityConjRingEquiv hP (plabicTwistorSol P A C Z) =
        plabicTwistorSol P (-A) (-C) (parityConjRingEquiv hP Z) := by
  have hPfix : parityConjRingEquiv hP P = P := by
    change parityConj P P = P
    unfold parityConj invS
    noncomm_ring [hP]
  have hQfix : parityConjRingEquiv hP (1 - P) = 1 - P := by
    rw [map_sub, map_one, hPfix]
  have hPlus : parityConjRingEquiv hP (conePlus P A) = conePlus P (-A) := by
    change parityConj P (conePlus P A) = conePlus P (-A)
    unfold parityConj
    peirce_nf hP
  have hMinus : parityConjRingEquiv hP (coneMinus P C) = coneMinus P (-C) := by
    change parityConj P (coneMinus P C) = coneMinus P (-C)
    unfold parityConj
    peirce_nf hP
  constructor
  · unfold plabicBoundaryOp
    simp only [map_mul, map_add, map_sub, map_one, hPlus, hMinus, hPfix]
  · unfold plabicTwistorSol
    simp only [map_mul, map_add, map_sub, map_one, hPlus, hMinus, hQfix]

end InfoGeometry.OperatorAlgebra.PeirceSpine
