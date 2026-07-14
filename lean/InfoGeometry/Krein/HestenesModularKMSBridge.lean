import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

namespace HestenesModularKMSBridge

open InfoGeometry.Krein
open InfoGeometry.OperatorAlgebra.OperatorThermodynamics

section Core

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [KreinSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance instNormedRingEndH : NormedRing EndH := inferInstance
noncomputable local instance instNormedAlgebraRealEndH : NormedAlgebra ℝ EndH := inferInstance
local instance instTopologicalRingEndH : IsTopologicalRing EndH := inferInstance
local instance instCompleteSpaceEndH : CompleteSpace EndH := inferInstance

/--
Hestenes/Krein real-form KMS packet.

This is the theorem-safe real translation of the modular/KMS socket:

* the abstract complex unit is represented by a real phase axis `K` with `K² = -1`;
* the modular dynamics is a repository-native `OperatorFlow` on bounded real
  endomorphisms;
* Hestenes analyticity is stored as `σₜ(KA) = K σₜ(A)`;
* null-cone preservation is a vector-rotor/Krein-isometry witness, not an
  unsupported consequence of the observable flow.
-/
@[rep_depth krein]
structure HestenesKreinKMSPacket where
  /-- Hestenes phase axis on the real observable algebra. -/
  phaseAxis : EndH

  /-- The phase axis squares to the real replacement of `-1`. -/
  phase_sq : phaseAxis * phaseAxis = -(1 : EndH)

  /-- Bounded modular flow on real observables. -/
  modularFlow : OperatorFlow EndH

  /-- Real rotor implementing vector-side modular motion. -/
  rotor : ℝ → EndH

  /-- Inverse rotor for the vector-side modular motion. -/
  rotorInv : ℝ → EndH

  /-- The observable flow is supplied by rotor conjugation. -/
  modularFlow_eq_rotor_conjugation :
    ∀ (t : ℝ) (A : EndH), modularFlow.flow t A = rotor t * A * rotorInv t

  /-- The rotor preserves the Krein metric. -/
  rotor_preserves_kreinInner :
    ∀ (t : ℝ) (ξ η : E),
      KreinSpace.kreinInner (H := E) (rotor t ξ) (rotor t η) =
        KreinSpace.kreinInner (H := E) ξ η

  /-- Hestenes analyticity: real modular flow commutes with left multiplication by `K`. -/
  flow_is_hestenes_analytic :
    ∀ (t : ℝ) (A : EndH), modularFlow.flow t (phaseAxis * A) =
      phaseAxis * modularFlow.flow t A

namespace HestenesKreinKMSPacket

variable (P : HestenesKreinKMSPacket (E := E))

/-- The real Hestenes/Krein natural cone candidate: nonnegative Krein norm. -/
@[rep_depth krein]
def HestenesNaturalCone (_P : HestenesKreinKMSPacket (E := E)) : Set E :=
  { ξ : E | 0 ≤ KreinSpace.kreinInner (H := E) ξ ξ }

/-- Hestenes expectation value represented by a cone/vacuum vector. -/
@[rep_depth krein]
def hestenesExpectation (_P : HestenesKreinKMSPacket (E := E)) (Ω : E) (A : EndH) : ℝ :=
  KreinSpace.kreinInner (H := E) (A Ω) Ω

/--
KMS boundary condition in the real Hestenes language.

The imaginary-time shift is represented by the supplied modular boundary at
`β`; Hestenes real analyticity remains the separate phase-axis witness.
-/
@[rep_depth krein]
def IsHestenesKMSCondition (β : ℝ) (φ : EndH → ℝ) : Prop :=
  ∀ A B : EndH, φ (A * (P.modularFlow.flow β B)) = φ (B * A)

/-- Readback of the real phase-axis square law. -/
@[rep_depth krein]
theorem phaseAxis_sq :
    P.phaseAxis * P.phaseAxis = -(1 : EndH) :=
  P.phase_sq

/-- Readback of the Hestenes analyticity/real-complex-linearity law. -/
@[rep_depth krein]
theorem hestenes_flow_to_abstract_flow (t : ℝ) (A : EndH) :
    P.modularFlow.flow t (P.phaseAxis * A) = P.phaseAxis * P.modularFlow.flow t A :=
  P.flow_is_hestenes_analytic t A

/-- Readback: the modular flow is the real rotor-conjugation action. -/
@[rep_depth krein]
theorem modularFlow_eq_rotor_conjugation_theorem (t : ℝ) (A : EndH) :
    P.modularFlow.flow t A = P.rotor t * A * P.rotorInv t :=
  P.modularFlow_eq_rotor_conjugation t A

/-- The rotor preserves the Hestenes natural cone. -/
@[rep_depth krein]
theorem rotor_preserves_HestenesNaturalCone
    (t : ℝ) {ξ : E} (hξ : ξ ∈ P.HestenesNaturalCone) :
    P.rotor t ξ ∈ P.HestenesNaturalCone := by
  change 0 ≤ KreinSpace.kreinInner (H := E) ξ ξ at hξ
  change 0 ≤ KreinSpace.kreinInner (H := E) (P.rotor t ξ) (P.rotor t ξ)
  rw [P.rotor_preserves_kreinInner t ξ ξ]
  exact hξ

/-- The modular rotor preserves the Krein null cone. -/
@[rep_depth krein]
theorem modular_rotor_preserves_null_cone
    (t : ℝ) {ξ : E}
    (h_null : KreinSpace.kreinInner (H := E) ξ ξ = 0) :
    KreinSpace.kreinInner (H := E) (P.rotor t ξ) (P.rotor t ξ) = 0 := by
  rw [P.rotor_preserves_kreinInner t ξ ξ]
  exact h_null

/-- The stored KMS boundary certificate can be read as a theorem. -/
@[rep_depth krein]
theorem hestenes_kms_boundary
    {β : ℝ} {φ : EndH → ℝ}
    (hKMS : P.IsHestenesKMSCondition β φ) (A B : EndH) :
    φ (A * (P.modularFlow.flow β B)) = φ (B * A) :=
  hKMS A B

/-- Vacuum/vector-state specialization of the Hestenes KMS boundary. -/
@[rep_depth krein]
theorem hestenesExpectation_kms_boundary
    {β : ℝ} {Ω : E}
    (hKMS : P.IsHestenesKMSCondition β (P.hestenesExpectation Ω))
    (A B : EndH) :
    P.hestenesExpectation Ω (A * (P.modularFlow.flow β B)) =
      P.hestenesExpectation Ω (B * A) :=
  hKMS A B

end HestenesKreinKMSPacket

end Core

end HestenesModularKMSBridge
