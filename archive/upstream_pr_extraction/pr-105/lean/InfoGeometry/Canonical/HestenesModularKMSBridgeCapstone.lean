/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Krein.HestenesModularKMSBridge

namespace InfoGeometry.Canonical

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

/-- Canonical projection capstone for the Hestenes/Krein modular KMS bridge. -/
theorem hestenes_modular_kms_bridge_canonical_capstone
    (K : EndH)
    (hK : K * K = -(1 : EndH)) :
    let P := HestenesKreinKMSPacket.ofStaticFlow K hK
    -- 1. Phase axis square law: K² = -1
    (P.phaseAxis * P.phaseAxis = -(1 : EndH)) ∧
    -- 2. Hestenes analyticity: σ_t(KA) = K σ_t(A)
    (∀ (t : ℝ) (A : EndH), P.modularFlow.flow t (P.phaseAxis * A) = P.phaseAxis * P.modularFlow.flow t A) ∧
    -- 3. Rotor conjugation equality
    (∀ (t : ℝ) (A : EndH), P.modularFlow.flow t A = P.rotor t * A * P.rotorInv t) ∧
    -- 4. Krein inner product preservation
    (∀ (t : ℝ) (ξ η : E), KreinSpace.kreinInner (H := E) (P.rotor t ξ) (P.rotor t η) = KreinSpace.kreinInner (H := E) ξ η) ∧
    -- 5. Null cone preservation
    (∀ (t : ℝ) {ξ : E}, KreinSpace.kreinInner (H := E) ξ ξ = 0 → KreinSpace.kreinInner (H := E) (P.rotor t ξ) (P.rotor t ξ) = 0) := by
  intro P
  exact ⟨
    P.phaseAxis_sq,
    P.hestenes_flow_to_abstract_flow,
    P.modularFlow_eq_rotor_conjugation_theorem,
    P.rotor_preserves_kreinInner,
    fun t ξ h => P.modular_rotor_preserves_null_cone t h
  ⟩

end InfoGeometry.Canonical
