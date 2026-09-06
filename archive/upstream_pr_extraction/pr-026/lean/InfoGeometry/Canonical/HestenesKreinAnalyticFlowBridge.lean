import InfoGeometry.Canonical.HestenesAnalyticity
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

noncomputable section

/-!
# InfoGeometry.Canonical.HestenesKreinAnalyticFlowBridge

Flow and rotor-generator sockets for real Hestenes--Krein analyticity.

This file does not construct a KMS flow, Tomita flow, analytic strip, or
holomorphic functional calculus. It records theorem-safe readbacks:

* a supplied flow preserves the Hestenes analytic sector;
* a supplied Hestenes-analytic generator acts by analytic commutator.

The owner is `HestenesAnalyticity`, where preservation of the internal phase
axis `clockAxis` replaces scalar-complex holomorphy.
-/

namespace InfoGeometry.Canonical.HestenesKreinAnalyticFlowBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesAnalyticity

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
A Hestenes--Krein analytic flow on real doubled endomorphisms.

This is a socket: it does not construct the flow from a modular Hamiltonian.
It records that a supplied flow preserves the internal Hestenes phase-axis
analytic sector.
-/
@[rep_depth krein]
structure HestenesKreinAnalyticFlow where
  /-- Supplied real-time flow on doubled endomorphisms. -/
  flow : ℝ → EndH → EndH

  /-- Flow identity at time zero. -/
  flow_zero :
    ∀ A : EndH, flow 0 A = A

  /-- Additive time composition law. -/
  flow_add :
    ∀ (t s : ℝ) (A : EndH), flow (t + s) A = flow t (flow s A)

  /--
  The key analytic compatibility: analytic operators remain analytic after
  transport by the supplied flow.
  -/
  preserves_hestenesAnalytic :
    ∀ (t : ℝ) (A : EndH),
      IsHestenesAnalyticSymmetry (E := E) A →
        IsHestenesAnalyticSymmetry (E := E) (flow t A)

namespace HestenesKreinAnalyticFlow

variable (F : HestenesKreinAnalyticFlow (E := E))

/-- Readback: Hestenes analyticity is preserved under the supplied flow. -/
@[rep_depth krein]
theorem flow_preserves_hestenesAnalytic
    (t : ℝ) (A : EndH)
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E) (F.flow t A) :=
  F.preserves_hestenesAnalytic t A hA

end HestenesKreinAnalyticFlow

/--
A Hestenes analytic rotor/generator.

`generator` is an infinitesimal symmetry candidate. The only law stored here is
that it preserves the internal Hestenes phase axis.
-/
@[rep_depth krein]
structure HestenesAnalyticRotorGenerator where
  generator : EndH

  /-- The generator commutes with the internal Hestenes phase axis. -/
  generator_hestenesAnalytic :
    IsHestenesAnalyticSymmetry (E := E) generator

namespace HestenesAnalyticRotorGenerator

variable (G : HestenesAnalyticRotorGenerator (E := E))

/--
If `A` is Hestenes analytic, then the commutator `[G,A]` is also Hestenes
analytic. This is the real-operator analogue of closure of analytic vector
fields under Lie bracket.
-/
@[rep_depth krein]
theorem commutator_with_generator_is_hestenesAnalytic
    {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E)
      (hestenesSymmetryCommutator (E := E) G.generator A) := by
  exact hestenesAnalyticSymmetry_commutator
    (E := E)
    G.generator_hestenesAnalytic
    hA

/--
The generator commutator itself is the Hestenes--Krein infinitesimal action
socket.
-/
@[rep_depth operator]
noncomputable def infinitesimalAction
    (A : EndH) : EndH :=
  hestenesSymmetryCommutator (E := E) G.generator A

/--
Readback: the infinitesimal action preserves Hestenes analyticity on analytic
inputs.
-/
@[rep_depth krein]
theorem infinitesimalAction_preserves_hestenesAnalytic
    {A : EndH}
    (hA : IsHestenesAnalyticSymmetry (E := E) A) :
    IsHestenesAnalyticSymmetry (E := E) (G.infinitesimalAction A) := by
  unfold infinitesimalAction
  exact G.commutator_with_generator_is_hestenesAnalytic hA

end HestenesAnalyticRotorGenerator

end Core

end InfoGeometry.Canonical.HestenesKreinAnalyticFlowBridge
