import Mathlib
import InfoGeometry.Canonical.GeometricCalculusSurgery

/-!
# InfoGeometry/Canonical/OperatorFreudenthalBoundary.lean

Bridge between geometric Stokes boundary flux and Freudenthal charge horizons.

This file does not assert that every Stokes flux computes a black-hole entropy.
Instead, it defines the proof-carrying interface that downstream modules must
instantiate once the concrete Clifford/Stokes/Freudenthal analytic layer exists.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open MeasureTheory
open Topology

noncomputable section

/-! ## 1. Scalar probes of operator-valued flux -/

/--
A real observable used to read a scalar from an operator-valued boundary flux.

In a concrete model this may be a trace, supertrace, renormalized trace, state
expectation, or horizon pairing.
-/
structure OperatorFluxProbe
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  evalFlux : RealEnd E →L[ℝ] ℝ

/--
Scalar flux obtained by applying a real probe to the geometric flux projector.
-/
def scalarBoundaryFlux
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (probe : OperatorFluxProbe E)
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ) : ℝ :=
  probe.evalFlux (geometricFluxProjector bdry R.R normalization)

/-! ## 2. Freudenthal horizon interface -/

/--
Abstract Freudenthal charge horizon datum.

`Charge` should later be instantiated by the repository's concrete Freudenthal
charge type. The entropy law is stored as a proof field rather than asserted
globally.
-/
structure FreudenthalHorizonDatum (Charge : Type*) where
  /-- The quartic Freudenthal invariant, usually denoted `I₄`. -/
  quarticInvariant : Charge → ℝ

  /-- The horizon entropy functional. -/
  entropy : Charge → ℝ

  /-- Predicate saying that a charge lies on the relevant horizon stratum. -/
  IsHorizon : Charge → Prop

  /-- Predicate saying that a charge lies on the rank-collapse/divisor locus. -/
  IsRankCollapse : Charge → Prop

  /-- The horizon stratum is identified with the relevant rank-collapse locus. -/
  horizon_iff_rankCollapse :
    ∀ q : Charge, IsHorizon q ↔ IsRankCollapse q

  /--
  D=4 Freudenthal black-hole entropy formula on the horizon stratum.

  This is intentionally a field. Concrete modules can instantiate it with the
  STU/Freudenthal theorem once available.
  -/
  entropy_eq_quartic_on_horizon :
    ∀ q : Charge,
      IsHorizon q →
        entropy q = Real.pi * Real.sqrt |quarticInvariant q|

/-! ## 3. Operator-Freudenthal boundary data -/

/--
A directed Stokes boundary whose points are labeled by Freudenthal charges.

This is the geometric bridge: the analytic boundary is interpreted as a
Freudenthal horizon boundary.
-/
structure OperatorFreudenthalBoundary
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : RealEnd E)
    (bdry : DirectedBoundary P E)
    (F : FreudenthalHorizonDatum Charge) where
  /-- Charge label attached to each boundary parameter. -/
  chargeAt : bdry.Param → Charge

  /-- Distinguished total/effective charge represented by the boundary. -/
  distinguishedCharge : Charge

  /-- Every boundary charge lies on the Freudenthal horizon. -/
  boundary_lies_on_horizon :
    ∀ x : bdry.Param, F.IsHorizon (chargeAt x)

  /-- The distinguished charge lies on the Freudenthal horizon. -/
  distinguished_on_horizon :
    F.IsHorizon distinguishedCharge

  /--
  Placeholder for the future statement that the boundary charge distribution
  represents the distinguished total charge.
  -/
  boundary_represents_distinguished_charge : Prop

  /--
  Placeholder for the future statement that the Stokes boundary is the geometric
  boundary of the zero/rank-collapse divisor.
  -/
  horizon_is_zero_spectral_boundary : Prop

namespace OperatorFreudenthalBoundary

variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : RealEnd E}
    {bdry : DirectedBoundary P E}
    {F : FreudenthalHorizonDatum Charge}

/--
Boundary charges lie on the rank-collapse locus.
-/
theorem boundary_rankCollapse
    (B : OperatorFreudenthalBoundary A bdry F)
    (x : bdry.Param) :
    F.IsRankCollapse (B.chargeAt x) :=
  (F.horizon_iff_rankCollapse (B.chargeAt x)).mp
    (B.boundary_lies_on_horizon x)

/--
The distinguished charge lies on the rank-collapse locus.
-/
theorem distinguished_rankCollapse
    (B : OperatorFreudenthalBoundary A bdry F) :
    F.IsRankCollapse B.distinguishedCharge :=
  (F.horizon_iff_rankCollapse B.distinguishedCharge).mp
    B.distinguished_on_horizon

end OperatorFreudenthalBoundary

/-! ## 4. Stokes flux to Freudenthal entropy bridge -/

/--
The proof-carrying bridge between geometric Stokes flux and Freudenthal entropy.

This is the object downstream applications should require when they want to
use the slogan:

`topological Stokes flux = D=4 Freudenthal black-hole entropy`.

The equality is not global; it is a field of the bridge.
-/
structure StokesFreudenthalFluxBridge
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ)
    (probe : OperatorFluxProbe E)
    (F : FreudenthalHorizonDatum Charge) where

  /-- The boundary is interpreted as a Freudenthal charge horizon. -/
  boundary :
    OperatorFreudenthalBoundary A bdry F

  /-- Generalized Stokes witness for the Clifford-resolvent field. -/
  stokes :
    StokesFluxWitness R bdry normalization

  /-- The geometric flux projector is idempotent. -/
  projector_idempotent :
    let Pcore := geometricFluxProjector bdry R.R normalization
    Pcore * Pcore = Pcore

  /-- The geometric flux projector commutes with the bounded operator. -/
  projector_commutes :
    let Pcore := geometricFluxProjector bdry R.R normalization
    Pcore * A = A * Pcore

  /--
  The scalar topological flux equals the entropy of the distinguished
  Freudenthal charge.
  -/
  flux_eq_entropy :
    scalarBoundaryFlux probe R bdry normalization =
      F.entropy boundary.distinguishedCharge

namespace StokesFreudenthalFluxBridge

variable
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    {R : CliffordResolventField ρ A}
    {bdry : DirectedBoundary P E}
    {normalization : ℝ}
    {probe : OperatorFluxProbe E}
    {F : FreudenthalHorizonDatum Charge}

/--
The geometric flux projector is idempotent.
-/
theorem coreProjector_idempotent
    (W : StokesFreudenthalFluxBridge R bdry normalization probe F) :
    geometricFluxProjector bdry R.R normalization *
      geometricFluxProjector bdry R.R normalization =
    geometricFluxProjector bdry R.R normalization := by
  simpa using W.projector_idempotent

/--
The geometric flux projector commutes with the operator.
-/
theorem coreProjector_commutes
    (W : StokesFreudenthalFluxBridge R bdry normalization probe F) :
    geometricFluxProjector bdry R.R normalization * A =
      A * geometricFluxProjector bdry R.R normalization := by
  simpa using W.projector_commutes

/--
The scalar boundary flux equals the Freudenthal entropy.
-/
theorem scalarFlux_eq_entropy
    (W : StokesFreudenthalFluxBridge R bdry normalization probe F) :
    scalarBoundaryFlux probe R bdry normalization =
      F.entropy W.boundary.distinguishedCharge :=
  W.flux_eq_entropy

/--
The scalar boundary flux equals the D=4 Freudenthal quartic entropy expression.
-/
theorem scalarFlux_eq_quarticEntropy
    (W : StokesFreudenthalFluxBridge R bdry normalization probe F) :
    scalarBoundaryFlux probe R bdry normalization =
      Real.pi *
        Real.sqrt |F.quarticInvariant W.boundary.distinguishedCharge| := by
  calc
    scalarBoundaryFlux probe R bdry normalization
        = F.entropy W.boundary.distinguishedCharge :=
          W.flux_eq_entropy
    _ = Real.pi *
        Real.sqrt |F.quarticInvariant W.boundary.distinguishedCharge| :=
          F.entropy_eq_quartic_on_horizon
            W.boundary.distinguishedCharge
            W.boundary.distinguished_on_horizon

/--
The distinguished charge represented by the Stokes boundary is on the
rank-collapse locus.
-/
theorem distinguished_rankCollapse
    (W : StokesFreudenthalFluxBridge R bdry normalization probe F) :
    F.IsRankCollapse W.boundary.distinguishedCharge :=
  OperatorFreudenthalBoundary.distinguished_rankCollapse W.boundary

end StokesFreudenthalFluxBridge

/-! ## 5. Owner target -/

universe uP uE uCharge uBoundary

/--
Owner target for the future theorem that constructs a Stokes-Freudenthal bridge.

This proposition is intentionally not proved here. It is the integration point
for the future Clifford-resolvent, Stokes, Freudenthal-charge, and entropy APIs.
-/
def StokesFreudenthalFluxBridgeOwnerTarget : Prop :=
  ∀ (P : Type uP) [NormedAddCommGroup P] [NormedSpace ℝ P],
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
  ∀ (Charge : Type uCharge),
  ∀ (ρ : ParavectorRepresentation P E),
  ∀ (A : RealEnd E),
  ∀ (R : CliffordResolventField ρ A),
  ∀ (bdry : DirectedBoundary.{uP, uE, uBoundary} P E),
  ∀ (normalization : ℝ),
  ∀ (probe : OperatorFluxProbe E),
  ∀ (F : FreudenthalHorizonDatum Charge),
    Nonempty (StokesFreudenthalFluxBridge R bdry normalization probe F)

end

end InfoGeometry.Canonical.GeometricCalculus
