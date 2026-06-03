import InfoGeometry.Canonical.BoundedModularFlowCalibration
import InfoGeometry.OperatorAlgebra.HorizonKMS

open scoped InnerProductSpace

noncomputable section

/-!
# KMS Condition Bridge

This file connects the bounded Souriau/Drazin modular-flow calibration to the
repository's KMS readout socket.

It does not prove analytic strip continuation from bounded algebra alone.  The
KMS boundary law, state invariance, and support-stability preservation are
explicit witness fields.
-/

namespace InfoGeometry.Canonical.KMSConditionBridge

open InfoGeometry.Canonical.BoundedModularFlowCalibration
open InfoGeometry.OperatorAlgebra.HorizonKMS

section Core

variable {E LieAlgebra : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
KMS socket for a bounded Souriau/Drazin modular flow.

`bounded.flow : ℝ → EndH` is the already-calibrated bounded generator flow.
`kmsFlow : ℝ → EndH → EndH` is the observable action used for KMS readouts,
typically supplied as an adjoint action `A ↦ U_t A U_{-t}`.
-/
@[rep_depth thermo]
structure BoundedKMSConditionBridge where
  /-- Bounded modular-flow calibration over the Souriau/Drazin surrogate. -/
  bounded :
    BoundedModularFlowCalibration (E := E) (LieAlgebra := LieAlgebra)

  /-- Observable-level KMS/modular action. -/
  kmsFlow : ℝ → EndH → EndH

  /-- State or weight readout. -/
  state : EndH → ℝ

  /-- KMS inverse temperature. -/
  beta : ℝ

  /-- Positive inverse temperature. -/
  beta_pos : 0 < beta

  /-- Zero-time observable-flow law. -/
  kmsFlow_zero :
    ∀ A : EndH, kmsFlow 0 A = A

  /-- Additive observable-flow law. -/
  kmsFlow_add :
    ∀ s t : ℝ, ∀ A : EndH, kmsFlow (s + t) A = kmsFlow s (kmsFlow t A)

  /--
  Calibration of the observable action against the bounded generator flow.
  In concrete bounded models this is the adjoint action `U_t A U_{-t}`.
  -/
  kmsFlow_eq_bounded_adjoint :
    ∀ t : ℝ, ∀ A : EndH, kmsFlow t A = bounded.flow t * A * bounded.flow (-t)

  /-- State is invariant under real modular time. -/
  state_invariant :
    ∀ t : ℝ, ∀ A : EndH, state (kmsFlow t A) = state A

  /--
  Preservation of the Drazin regular-support commutation lane.

  This is witness data: it does not follow from `flow_eq_exp_Ksur` unless the
  observable action is also known to preserve the commutant of the support
  projector.
  -/
  regularSupportStable :
    ∀ t : ℝ, ∀ A : EndH,
      bounded.souriau.superBridge.CIK.spectralProjector * A =
          A * bounded.souriau.superBridge.CIK.spectralProjector →
        bounded.souriau.superBridge.CIK.spectralProjector * kmsFlow t A =
          kmsFlow t A * bounded.souriau.superBridge.CIK.spectralProjector

  /--
  The Massieu/free-energy scalar shift is central for the supplied observable
  KMS flow.
  -/
  partitionPotential_flow_central :
    ∀ t : ℝ, ∀ A : EndH,
      bounded.souriau.family.opScale bounded.souriau.family.partitionPotential (kmsFlow t A) =
        kmsFlow t
          (bounded.souriau.family.opScale bounded.souriau.family.partitionPotential A)

  /--
  Infinitesimal generator law for the observable flow.

  This remains a proposition field because derivative/commutator conventions
  depend on the chosen concrete flow model.
  -/
  infinitesimalGeneratorLaw : Prop

namespace BoundedKMSConditionBridge

variable (K : BoundedKMSConditionBridge (E := E) (LieAlgebra := LieAlgebra))

/-- Convert the bounded KMS condition bridge to the repository KMS readout datum. -/
@[rep_depth thermo]
def toKMSReadoutDatum : KMSReadoutDatum EndH where
  flow := K.kmsFlow
  state := K.state
  beta := K.beta
  beta_pos := K.beta_pos
  flow_zero := K.kmsFlow_zero
  flow_add := K.kmsFlow_add
  flow_invariant := K.state_invariant

/-- The KMS inverse temperature is nonzero. -/
@[rep_depth thermo]
theorem beta_ne_zero :
    K.beta ≠ 0 :=
  ne_of_gt K.beta_pos

/-- The bounded generator is still the calibrated Souriau bare source. -/
@[rep_depth thermo]
theorem bounded_flow_eq_exp_Khat_beta (t : ℝ) :
    K.bounded.flow t =
      NormedSpace.exp (t • K.bounded.souriau.family.Khat_beta) :=
  K.bounded.flow_eq_exp_Khat_beta t

/-- Regular-support commutation stability for the supplied observable KMS flow. -/
@[rep_depth thermo]
theorem flow_stability_under_regular_support
    (t : ℝ) (A : EndH)
    (hA :
      K.bounded.souriau.superBridge.CIK.spectralProjector * A =
        A * K.bounded.souriau.superBridge.CIK.spectralProjector) :
    K.bounded.souriau.superBridge.CIK.spectralProjector * K.kmsFlow t A =
      K.kmsFlow t A * K.bounded.souriau.superBridge.CIK.spectralProjector :=
  K.regularSupportStable t A hA

/-- The Massieu/free-energy scalar shift commutes through the supplied KMS flow. -/
@[rep_depth thermo]
theorem partition_potential_flow_central (t : ℝ) (A : EndH) :
    K.bounded.souriau.family.opScale K.bounded.souriau.family.partitionPotential
        (K.kmsFlow t A) =
      K.kmsFlow t
        (K.bounded.souriau.family.opScale
          K.bounded.souriau.family.partitionPotential A) :=
  K.partitionPotential_flow_central t A

end BoundedKMSConditionBridge

end Core

end InfoGeometry.Canonical.KMSConditionBridge
