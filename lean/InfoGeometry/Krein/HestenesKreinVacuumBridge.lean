import InfoGeometry.Krein.HestenesModularKMSBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Krein.HestenesKreinVacuumBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.HestenesModularKMSBridge

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Vacuum vector socket for the Hestenes/Krein real KMS packet.

This file does not prove a global Haagerup--Araki standard-form uniqueness
statement.  The cyclic/separating/uniqueness content remains an explicit
certificate supplied by the Hestenes--Krein owner.  Locally, this bridge proves
the Krein readbacks that follow from the supplied witnesses.
-/
@[rep_depth krein]
abbrev HestenesKreinVacuum (P : HestenesKreinKMSPacket (E := E)) :=
  {omega : E //
    omega ∈ P.HestenesNaturalCone ∧
    KreinSpace.kreinInner (H := E) omega omega = 1 ∧
    KreinSpace.jCLM (H := E) omega = omega ∧
    (∀ t : ℝ, P.rotor t omega = omega) ∧
    (∀ (t : ℝ) (A : EndH),
      P.hestenesExpectation omega (P.modularFlow.flow t A) =
        P.hestenesExpectation omega A)}

namespace HestenesKreinVacuum

abbrev omega {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) : E := V.1
abbrev omega_in_cone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) : V.1 ∈ P.HestenesNaturalCone := V.2.1
abbrev omega_normalized {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) :
    KreinSpace.kreinInner (H := E) V.1 V.1 = 1 := V.2.2.1
abbrev J_fixes_omega {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) :
    KreinSpace.jCLM (H := E) V.1 = V.1 := V.2.2.2.1
abbrev rotor_fixes_omega {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) : ∀ t : ℝ, P.rotor t V.1 = V.1 := V.2.2.2.2.1
abbrev omega_expectation_flow_invariant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]
    {P : HestenesKreinKMSPacket (E := E)}
    (V : HestenesKreinVacuum P) :
    ∀ (t : ℝ) (A : E →L[ℝ] E),
      P.hestenesExpectation V.1 (P.modularFlow.flow t A) =
        P.hestenesExpectation V.1 A := V.2.2.2.2.2

end HestenesKreinVacuum


namespace HestenesKreinVacuum

variable {P : HestenesKreinKMSPacket (E := E)}
variable (V : HestenesKreinVacuum P)

/-- Vacuum real state: `φ_Ω(A) = [AΩ, Ω]_J`. -/
@[rep_depth krein]
def vacuumRealState (A : EndH) : ℝ :=
  P.hestenesExpectation V.omega A

/-- The vacuum state is normalized on the identity observable. -/
@[rep_depth krein]
theorem vacuumRealState_id :
    V.vacuumRealState (1 : EndH) = 1 := by
  unfold vacuumRealState HestenesKreinKMSPacket.hestenesExpectation
  simpa using V.omega_normalized

/-- The rotor fixes the vacuum vector. -/
@[rep_depth krein]
theorem vacuum_rotor_fixed (t : ℝ) :
    P.rotor t V.omega = V.omega :=
  V.rotor_fixes_omega t

/-- The rotor preserves the normalized Krein norm of the vacuum. -/
@[rep_depth krein]
theorem vacuum_rotor_norm_invariant (t : ℝ) :
    KreinSpace.kreinInner (H := E) (P.rotor t V.omega) (P.rotor t V.omega) = 1 := by
  calc
    KreinSpace.kreinInner (H := E) (P.rotor t V.omega) (P.rotor t V.omega)
        = KreinSpace.kreinInner (H := E) V.omega V.omega :=
            P.rotor_preserves_kreinInner t V.omega V.omega
    _ = 1 := V.omega_normalized

/-- The Krein fundamental symmetry fixes the vacuum. -/
@[rep_depth krein]
theorem vacuum_J_fixed :
    KreinSpace.jCLM (H := E) V.omega = V.omega :=
  V.J_fixes_omega

/-- The vacuum expectation is invariant under the Hestenes/Krein modular flow. -/
@[rep_depth krein]
theorem vacuumRealState_flow_invariant (t : ℝ) (A : EndH) :
    V.vacuumRealState (P.modularFlow.flow t A) = V.vacuumRealState A :=
  V.omega_expectation_flow_invariant t A

/-- The vacuum lies in the Hestenes/Krein natural cone. -/
@[rep_depth krein]
theorem vacuum_mem_naturalCone :
    V.omega ∈ P.HestenesNaturalCone :=
  V.omega_in_cone

/-- The normalized vacuum is not Krein-null. -/
@[rep_depth krein]
theorem vacuum_not_null :
    KreinSpace.kreinInner (H := E) V.omega V.omega ≠ 0 := by
  rw [V.omega_normalized]
  exact one_ne_zero

/-- If the vacuum state is supplied as KMS, then its Hestenes boundary law holds. -/
@[rep_depth krein]
theorem vacuum_kms_boundary
    {β : ℝ}
    (hKMS : P.IsHestenesKMSCondition β V.vacuumRealState)
    (A B : EndH) :
    V.vacuumRealState (A * (P.modularFlow.flow β B)) = V.vacuumRealState (B * A) :=
  hKMS A B

end HestenesKreinVacuum

end Core

end InfoGeometry.Krein.HestenesKreinVacuumBridge
