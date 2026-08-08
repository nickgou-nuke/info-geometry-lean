import Mathlib.Tactic
import InfoGeometry.Canonical.GeometricCalculusFreudenthalBridge
import InfoGeometry.Exceptional.STUDatum
import InfoGeometry.Applications.STUBlackHoleQubit
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry/Canonical/GeometricCalculusSTUBridge.lean

STU-specific adapters for the Stokes/Freudenthal boundary bridge.

This file does not construct a Clifford resolvent, a Stokes boundary, or a
black-hole entropy theorem.  It only connects the generic bridge interface to
the concrete STU/Freudenthal pieces already present in the repository:

* `FreudenthalCharge.quarticInvariant`;
* the concrete diagonal `STU_Datum`;
* Cayley's hyperdeterminant on `ThreeQubitState`;
* the proof-carrying `BlackHoleQubitDictionary`.

The analytic equality between scalar geometric flux and entropy remains a
field of `OperatorFreudenthalBoundaryFluxBridge`.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open InfoGeometry.Exceptional.Freudenthal
open InfoGeometry.Exceptional.STUDatum
open InfoGeometry.Applications.STUQubit

noncomputable section

universe uE uP uΩ

/-! ## 1. Freudenthal charge geometry from a cubic Jordan datum -/

/--
Freudenthal charge geometry attached to any cubic Jordan datum.

The horizon locus is intentionally left as `Set.univ`: this adapter only
supplies the quartic invariant and entropy normalization.  More refined large
or small black-hole strata should be supplied by a stronger charge-boundary
property.
-/
def freudenthalChargeGeometry
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (D : CubicJordanDatum J) :
    FreudenthalChargeGeometry (FreudenthalCharge J) where
  I4 := FreudenthalCharge.quarticInvariant D
  entropy := freudenthalEntropyFromQuartic (FreudenthalCharge.quarticInvariant D)
  chargeHorizon := Set.univ
  rankCollapseLocus := {Q : FreudenthalCharge J | FreudenthalCharge.quarticInvariant D Q = 0}
  rankCollapseLocus_spec := rfl
  entropy_eq_quartic := by
    intro Q
    rfl

/-- The concrete Freudenthal charge geometry for the diagonal STU datum. -/
def stuFreudenthalChargeGeometry :
    FreudenthalChargeGeometry (FreudenthalCharge STUCarrier) :=
  freudenthalChargeGeometry STU_Datum

@[simp]
theorem stuFreudenthalChargeGeometry_I4
    (Q : FreudenthalCharge STUCarrier) :
    stuFreudenthalChargeGeometry.I4 Q =
      FreudenthalCharge.quarticInvariant STU_Datum Q :=
  rfl

/-! ## 2. Qubit-side STU geometry -/

/--
The qubit-side STU geometry whose quartic invariant is Cayley's
hyperdeterminant.

This is the coordinate-side model.  The bridge to Freudenthal charges is
provided separately by `BlackHoleQubitDictionary`.
-/
def stuQubitChargeGeometry :
    FreudenthalChargeGeometry ThreeQubitState where
  I4 := ThreeQubitState.cayleyHyperdeterminant
  entropy := freudenthalEntropyFromQuartic ThreeQubitState.cayleyHyperdeterminant
  chargeHorizon := Set.univ
  rankCollapseLocus := {ψ : ThreeQubitState | ThreeQubitState.cayleyHyperdeterminant ψ = 0}
  rankCollapseLocus_spec := rfl
  entropy_eq_quartic := by
    intro ψ
    rfl

@[simp]
theorem stuQubitChargeGeometry_I4
    (ψ : ThreeQubitState) :
    stuQubitChargeGeometry.I4 ψ =
      ThreeQubitState.cayleyHyperdeterminant ψ :=
  rfl

theorem stuQubit_rankCollapse_iff_hyperdeterminant_zero
    (ψ : ThreeQubitState) :
    ψ ∈ stuQubitChargeGeometry.rankCollapseLocus ↔
      ThreeQubitState.cayleyHyperdeterminant ψ = 0 :=
  Iff.rfl

/--
The repository's STU black-hole/qubit dictionary identifies the Freudenthal
quartic invariant of the embedded charge with Cayley's hyperdeterminant.
-/
theorem embedded_STU_quartic_eq_hyperdeterminant
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    {D : CubicJordanDatum J}
    (Dict : BlackHoleQubitDictionary D)
    (ψ : ThreeQubitState) :
    (freudenthalChargeGeometry D).I4 (Dict.embedSTU ψ) =
      stuQubitChargeGeometry.I4 ψ := by
  rw [stuQubitChargeGeometry_I4]
  exact Dict.quartic_eq_hyperdeterminant ψ

/-! ## 3. STU-specialized boundary bridge aliases -/

/--
An operator Freudenthal boundary datum whose charge labels are STU qubit
states.
-/
abbrev STUQubitBoundaryDatum
    (E P : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :=
  OperatorFreudenthalBoundaryDatum E P ThreeQubitState

/--
Constructor for an STU qubit boundary datum using the canonical
hyperdeterminant entropy geometry.
-/
def STUQubitBoundaryDatum.ofBoundaryCharges
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (Ω : DirectedBoundary P)
    (charges : FreudenthalBoundaryCharge Ω stuQubitChargeGeometry)
    (horizonOperator : RealEnd E) :
    STUQubitBoundaryDatum E P where
  A := A
  geometry := stuQubitChargeGeometry
  boundary := Ω
  boundaryCharges := charges
  horizonOperator := horizonOperator

/--
The STU boundary flux bridge is exactly the generic operator/Freudenthal bridge
specialized to qubit charge labels.
-/
abbrev STUQubitBoundaryFluxBridge
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : STUQubitBoundaryDatum E P) :=
  OperatorFreudenthalBoundaryFluxBridge D

/--
For an STU qubit boundary bridge, the scalar flux equals the quartic boundary
entropy, i.e. the integral of `π sqrt |Det₂₂₂|` over the supplied boundary
charge map.
-/
theorem STUQubitBoundaryFluxBridge.scalarFlux_eq_hyperdeterminantEntropy
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {D : STUQubitBoundaryDatum E P}
    (W : STUQubitBoundaryFluxBridge D) :
    FluxEqualsQuarticEntropy
      D.A W.resolvent D.boundary W.normalizationFactor W.observer
      D.geometry D.boundaryCharges :=
  OperatorFreudenthalBoundaryFluxBridge.scalarFlux_eq_quarticEntropy W

/--
Owner target for reading the STU-specialized boundary bridge.

The construction remains property-gated: the Clifford resolvent family,
boundary, observer, and flux/entropy equality must still be supplied by future
analytic geometry.
-/
@[owner_target_tag]
def STUQubitBoundaryFluxOwnerTarget : Prop :=
  ∀ (E : Type uE) (P : Type uP)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P],
    ∀ D : STUQubitBoundaryDatum.{uE, uP, uΩ} E P,
      D.geometry = stuQubitChargeGeometry →
        ∀ W : STUQubitBoundaryFluxBridge.{uE, uP, uΩ, uΩ} D,
          FluxEqualsQuarticEntropy
            D.A W.resolvent D.boundary W.normalizationFactor W.observer
            D.geometry D.boundaryCharges

/-- A supplied STU boundary bridge reads out scalar flux as quartic entropy. -/
theorem stuQubitBoundaryFluxOwnerTarget :
    STUQubitBoundaryFluxOwnerTarget.{uE, uP, uΩ} := by
  intro E P _ _ _ _ _ D _ W
  exact STUQubitBoundaryFluxBridge.scalarFlux_eq_hyperdeterminantEntropy W

end

end InfoGeometry.Canonical.GeometricCalculus
