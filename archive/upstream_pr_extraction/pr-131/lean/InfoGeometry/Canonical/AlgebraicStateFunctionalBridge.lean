import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.AlgebraicStateFunctionalBridge

Minimal owner/translator surface for the doctrine:

- state is owned first as a normalized linear probe on the observable carrier;
- a doubled/Krein vector state is one representation surface for that probe;
- basis/frame data is representational scaffolding, not the ontology of statehood.

This file is intentionally modest. It does **not** formalize a full C*- or
von-Neumann-state theory, and it does **not** implement a full GNS theorem.
It records the smallest truthful bridge currently supported by the repo:
`VectorState.expectation` on the doubled carrier gives a normalized linear probe
once a normalization property is supplied.
-/

namespace InfoGeometry.Canonical.AlgebraicStateFunctionalBridge

open InfoGeometry.Volume.ConnesCocycle
open StandardFormCore
open InfoGeometry.Krein

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => DoubledSpace H
local notation "EndH" => AlgebraEnd H

/--
Abstract normalized algebraic probe on the observable carrier.

This is the smallest current owner surface for "state-as-functional" in the
operatorial lane. Positivity in the full operator-algebraic sense remains future
work; the current file only owns normalized linear probing.
-/
@[rep_depth operator]
structure PositiveNormalizedFunctional
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  probe : AlgebraEnd H →ₗ[ℝ] ℝ
  normalized : probe 1 = 1

namespace PositiveNormalizedFunctional

variable (ω : PositiveNormalizedFunctional H)

/-- The probe of the identity observable is normalized to one. -/
@[rep_depth operator]
theorem probe_id :
    ω.probe 1 = 1 :=
  ω.normalized

/--
Construct a normalized algebraic probe from a doubled-space vector state once a
normalization property is supplied.
-/
@[rep_depth krein]
noncomputable def ofNormalizedVectorState
    (ξ : VectorState H)
    (hnorm : ξ.expectation (ContinuousLinearMap.id ℝ H2) = 1) :
    PositiveNormalizedFunctional H where
  probe :=
    { toFun := fun A => ξ.expectation A
      map_add' := by
        intro A B
        simp [VectorState.expectation, inner_add_left, add_assoc, add_left_comm]
      map_smul' := by
        intro c A
        simp [VectorState.expectation, inner_smul_left] }
  normalized := by
    simpa using hnorm

@[rep_depth krein]
theorem ofNormalizedVectorState_probe_apply
    (ξ : VectorState H)
    (hnorm : ξ.expectation (ContinuousLinearMap.id ℝ H2) = 1)
    (A : EndH) :
    (ofNormalizedVectorState (H := H) ξ hnorm).probe A = ξ.expectation A :=
  rfl

end PositiveNormalizedFunctional

/--
Representation frame on the doubled/Krein carrier.

The frame gives coordinates/basis data for a representation surface. It is not
part of the ontology of statehood itself.
-/
@[rep_depth krein]
structure RepresentationFrame
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  Index : Type*
  coordinate : Index → DoubledSpace H

/--
Bridge from an abstract normalized probe to a standard-form carrier and an
optional representation frame.

The key field is `probe_eq_referenceExpectation`: the probe is the same object
as the expectation of the carrier's reference state. The frame is attached only
as additional representational scaffolding.
-/
@[rep_depth operator]
structure StateRepresentationBridge
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  state : PositiveNormalizedFunctional H
  carrier : StandardFormCarrier H
  frame : RepresentationFrame H
  probe_eq_referenceExpectation :
    (fun A : AlgebraEnd H => state.probe A) = carrier.referenceState.expectation

namespace StateRepresentationBridge

variable (B : StateRepresentationBridge H)

/-- The abstract probe agrees with the doubled-carrier reference expectation. -/
@[rep_depth krein]
theorem probe_eq_referenceExpectation' :
    (fun A : EndH => B.state.probe A) = B.carrier.referenceState.expectation :=
  B.probe_eq_referenceExpectation

/-- Pointwise evaluation form of the representation bridge. -/
@[rep_depth krein]
theorem probe_apply_eq_referenceExpectation
    (A : EndH) :
    B.state.probe A = B.carrier.referenceState.expectation A := by
  exact congrArg (fun f : EndH → ℝ => f A) B.probe_eq_referenceExpectation

/--
Attach a new representation frame without changing the underlying probe/state
identification.
-/
@[rep_depth operator]
def withFrame
    (F : RepresentationFrame H) :
    StateRepresentationBridge H where
  state := B.state
  carrier := B.carrier
  frame := F
  probe_eq_referenceExpectation := B.probe_eq_referenceExpectation

/-- Changing the frame does not change the probe identity. -/
@[rep_depth operator]
theorem withFrame_probe_eq
    (F : RepresentationFrame H) :
    (B.withFrame F).state.probe = B.state.probe := rfl

/-- Changing the frame does not change the bridge to reference expectation. -/
@[rep_depth krein]
theorem withFrame_probe_apply_eq_referenceExpectation
    (F : RepresentationFrame H) (A : EndH) :
    (B.withFrame F).state.probe A = B.carrier.referenceState.expectation A := by
  exact congrArg (fun f : EndH → ℝ => f A) (B.withFrame F).probe_eq_referenceExpectation

end StateRepresentationBridge

end Core

end InfoGeometry.Canonical.AlgebraicStateFunctionalBridge
