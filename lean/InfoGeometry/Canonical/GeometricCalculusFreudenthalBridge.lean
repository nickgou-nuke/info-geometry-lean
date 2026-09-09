import Mathlib.Tactic
import InfoGeometry.Canonical.GeometricCalculusSurgery

/-!
# InfoGeometry/Canonical/GeometricCalculusFreudenthalBridge.lean

Structural bridge from Stokes/Clifford boundary flux to Freudenthal charge
horizons.

The bridge is witness-gated. It does not assert that every Stokes flux equals
black-hole entropy. Instead, it records the exact data needed for such a
statement:

* a real operator `A`;
* a Clifford resolvent family for `A`;
* a directed paravector boundary;
* a Freudenthal charge geometry with quartic invariant `I₄`;
* a boundary-to-charge map landing on the Freudenthal horizon;
* a scalar observer/trace extracting a real number from the operator-valued
  projector;
* a proof that the extracted flux equals the boundary entropy.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open MeasureTheory
open Topology

noncomputable section

set_option autoImplicit false

/-! ## 1. Freudenthal charge geometry -/

/--
The standard quartic black-hole entropy density associated to a Freudenthal
quartic invariant.

This is only the scalar formula. The structure below decides whether a given
charge model uses it.
-/
def freudenthalEntropyFromQuartic
    {Q : Type*}
    (I4 : Q → ℝ)
    (q : Q) : ℝ :=
  Real.pi * Real.sqrt (|I4 q|)

/--
Abstract Freudenthal charge geometry.

`Q` is the charge space.

`I4` is the Freudenthal quartic invariant.

`entropy` is the scalar entropy assigned to a charge.

`chargeHorizon` is the charge-side horizon locus.

`rankCollapseLocus` is the locus `I4 = 0`.

The field `entropy_eq_quartic` is a real proof field, not a placeholder.
-/
structure FreudenthalChargeGeometry (Q : Type*) where
  I4 : Q → ℝ
  entropy : Q → ℝ
  chargeHorizon : Set Q
  rankCollapseLocus : Set Q
  rankCollapseLocus_spec :
    rankCollapseLocus = {q : Q | I4 q = 0}
  entropy_eq_quartic :
    ∀ q : Q, entropy q = freudenthalEntropyFromQuartic I4 q

/-! ## 2. Boundary charge maps -/

/-- A map from the geometric boundary into the Freudenthal charge horizon. -/
structure FreudenthalBoundaryCharge
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Ω : DirectedBoundary P)
    (F : FreudenthalChargeGeometry Q) where
  charge : Ω.Carrier → Q
  landsOnHorizon :
    ∀ x : Ω.Carrier, charge x ∈ F.chargeHorizon

/--
A boundary charge map that lands on the rank-collapse locus `I₄ = 0`.

This should be used only for the strict rank-collapse boundary. For a nonzero
entropy horizon, use `FreudenthalBoundaryCharge` without this extension.
-/
structure RankCollapseBoundaryCharge
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Ω : DirectedBoundary P)
    (F : FreudenthalChargeGeometry Q)
    extends FreudenthalBoundaryCharge Ω F where
  landsOnRankCollapse :
    ∀ x : Ω.Carrier, charge x ∈ F.rankCollapseLocus

namespace RankCollapseBoundaryCharge

theorem I4_eq_zero
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    {F : FreudenthalChargeGeometry Q}
    (C : RankCollapseBoundaryCharge Ω F)
    (x : Ω.Carrier) :
    F.I4 (C.charge x) = 0 := by
  have hx : C.charge x ∈ F.rankCollapseLocus :=
    C.landsOnRankCollapse x
  rw [F.rankCollapseLocus_spec] at hx
  exact hx

theorem entropy_eq_zero
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    {F : FreudenthalChargeGeometry Q}
    (C : RankCollapseBoundaryCharge Ω F)
    (x : Ω.Carrier) :
    F.entropy (C.charge x) = 0 := by
  rw [F.entropy_eq_quartic]
  have hI4 : F.I4 (C.charge x) = 0 :=
    C.I4_eq_zero x
  simp [freudenthalEntropyFromQuartic, hI4]

end RankCollapseBoundaryCharge

/-! ## 3. Boundary entropy functionals -/

/-- Entropy density induced on the geometric boundary by a charge map. -/
def boundaryEntropyDensity
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F)
    (x : Ω.Carrier) : ℝ :=
  F.entropy (C.charge x)

/-- Boundary entropy integral induced by a charge map. -/
def boundaryEntropy
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F) : ℝ :=
  letI : MeasurableSpace Ω.Carrier := Ω.instMeasurableSpace
  MeasureTheory.integral Ω.boundaryMeasure
    (fun x => boundaryEntropyDensity F C x)

/-- Quartic entropy density on the boundary. -/
def quarticBoundaryEntropyDensity
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F)
    (x : Ω.Carrier) : ℝ :=
  freudenthalEntropyFromQuartic F.I4 (C.charge x)

/-- Boundary integral of the quartic entropy density. -/
def quarticBoundaryEntropy
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F) : ℝ :=
  letI : MeasurableSpace Ω.Carrier := Ω.instMeasurableSpace
  MeasureTheory.integral Ω.boundaryMeasure
    (fun x => quarticBoundaryEntropyDensity F C x)

theorem boundaryEntropyDensity_eq_quartic
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F)
    (x : Ω.Carrier) :
    boundaryEntropyDensity F C x =
      quarticBoundaryEntropyDensity F C x := by
  exact F.entropy_eq_quartic (C.charge x)

theorem boundaryEntropy_eq_quarticBoundaryEntropy
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F) :
    boundaryEntropy F C = quarticBoundaryEntropy F C := by
  letI : MeasurableSpace Ω.Carrier := Ω.instMeasurableSpace
  simp [
    boundaryEntropy,
    quarticBoundaryEntropy,
    boundaryEntropyDensity,
    quarticBoundaryEntropyDensity,
    F.entropy_eq_quartic
  ]

theorem rankCollapse_boundaryEntropy_eq_zero
    {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : DirectedBoundary P}
    {F : FreudenthalChargeGeometry Q}
    (C : RankCollapseBoundaryCharge Ω F) :
    boundaryEntropy F C.toFreudenthalBoundaryCharge = 0 := by
  letI : MeasurableSpace Ω.Carrier := Ω.instMeasurableSpace
  simp [
    boundaryEntropy,
    boundaryEntropyDensity,
    RankCollapseBoundaryCharge.entropy_eq_zero C
  ]

/-! ## 4. Scalar extraction of operator-valued flux -/

/-- Scalar observer/trace applied to the operator-valued geometric flux projector. -/
def scalarGeometricFlux
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ)
    (observer : RealEnd E →L[ℝ] ℝ) : ℝ :=
  observer (geometricCoreProjector A R Ω normalizationFactor)

/-- The bridge equation: scalar Stokes/Clifford flux equals boundary entropy. -/
def FluxEqualsBoundaryEntropy
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ)
    (observer : RealEnd E →L[ℝ] ℝ)
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F) : Prop :=
  scalarGeometricFlux A R Ω normalizationFactor observer =
    boundaryEntropy F C

/-- Same bridge equation, rewritten using the Freudenthal quartic invariant. -/
def FluxEqualsQuarticEntropy
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ)
    (observer : RealEnd E →L[ℝ] ℝ)
    (F : FreudenthalChargeGeometry Q)
    (C : FreudenthalBoundaryCharge Ω F) : Prop :=
  scalarGeometricFlux A R Ω normalizationFactor observer =
    quarticBoundaryEntropy F C

theorem FluxEqualsBoundaryEntropy.to_quartic
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : RealEnd E}
    {R : CliffordResolventFamily (P := P) A}
    {Ω : DirectedBoundary P}
    {normalizationFactor : ℝ}
    {observer : RealEnd E →L[ℝ] ℝ}
    {F : FreudenthalChargeGeometry Q}
    {C : FreudenthalBoundaryCharge Ω F}
    (h : FluxEqualsBoundaryEntropy A R Ω normalizationFactor observer F C) :
    FluxEqualsQuarticEntropy A R Ω normalizationFactor observer F C := by
  change scalarGeometricFlux A R Ω normalizationFactor observer = quarticBoundaryEntropy F C
  rw [← boundaryEntropy_eq_quarticBoundaryEntropy F C]
  exact h

/-! ## 5. Operator-Freudenthal boundary bridge -/

/--
Minimal interface for an operator-side Freudenthal boundary.

`horizonOperator` is the operator-side object that the Stokes flux is supposed
to realize.
-/
structure OperatorFreudenthalBoundaryDatum
    (E P Q : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] where
  A : RealEnd E
  geometry : FreudenthalChargeGeometry Q
  boundary : DirectedBoundary P
  boundaryCharges : FreudenthalBoundaryCharge boundary geometry
  horizonOperator : RealEnd E

/--
Witness that the operator Freudenthal boundary is realized by Clifford/Stokes
flux, and that the scalar flux measures the induced Freudenthal entropy.
-/
structure OperatorFreudenthalBoundaryFluxBridge
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : OperatorFreudenthalBoundaryDatum E P Q) where
  phase : BivectorPhase E
  resolvent : CliffordResolventFamily (P := P) D.A
  normalizationFactor : ℝ
  observer : RealEnd E →L[ℝ] ℝ
  stokes :
    StokesTheoremWitness D.A resolvent D.boundary
  horizonOperator_eq_flux :
    D.horizonOperator =
      geometricCoreProjector D.A resolvent D.boundary normalizationFactor
  scalarFlux_eq_entropy :
    FluxEqualsBoundaryEntropy
      D.A resolvent D.boundary normalizationFactor observer
      D.geometry D.boundaryCharges

namespace OperatorFreudenthalBoundaryFluxBridge

/-- The operator-valued Stokes flux projector associated to the bridge. -/
def projector
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {D : OperatorFreudenthalBoundaryDatum E P Q}
    (W : OperatorFreudenthalBoundaryFluxBridge D) : RealEnd E :=
  geometricCoreProjector D.A W.resolvent D.boundary W.normalizationFactor

theorem horizonOperator_eq_projector
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {D : OperatorFreudenthalBoundaryDatum E P Q}
    (W : OperatorFreudenthalBoundaryFluxBridge D) :
    D.horizonOperator = W.projector := by
  simpa [projector] using W.horizonOperator_eq_flux

theorem scalarFlux_eq_quarticEntropy
    {E P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {D : OperatorFreudenthalBoundaryDatum E P Q}
    (W : OperatorFreudenthalBoundaryFluxBridge D) :
    FluxEqualsQuarticEntropy
      D.A W.resolvent D.boundary W.normalizationFactor W.observer
      D.geometry D.boundaryCharges := by
  exact FluxEqualsBoundaryEntropy.to_quartic W.scalarFlux_eq_entropy

end OperatorFreudenthalBoundaryFluxBridge

/-! ## 6. Constructive bridge packaging -/

universe uE uP uQ uΩ uVolume

/--
Per-data construction type for an operator/Freudenthal flux bridge.

This is intentionally data, not a proposition saying “for all data, a bridge
exists,” because the bridge contains the nontrivial compatibility equation
`scalarGeometricFlux = boundaryEntropy`.
-/
abbrev OperatorFreudenthalBoundaryFluxConstructionProblem
    (E : Type uE) (P : Type uP) (Charge : Type uQ)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : OperatorFreudenthalBoundaryDatum.{uE, uP, uQ, uΩ} E P Charge) :=
  OperatorFreudenthalBoundaryFluxBridge.{uE, uP, uQ, uΩ, uVolume} D

/--
Construct an operator/Freudenthal flux bridge from explicit witnesses.

This is the correct replacement for a universal owner target.  For an arbitrary
observer and arbitrary Freudenthal charge geometry, the scalar flux/entropy
equality is not constructible; it must be supplied by the concrete
Clifford/Stokes/Freudenthal model.
-/
def operatorFreudenthalBoundaryFluxBridge_from_witnesses
    {E : Type uE} {P : Type uP} {Q : Type uQ}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {D : OperatorFreudenthalBoundaryDatum.{uE, uP, uQ, uΩ} E P Q}
    (phase : BivectorPhase E)
    (resolvent : CliffordResolventFamily (P := P) D.A)
    (normalizationFactor : ℝ)
    (observer : RealEnd E →L[ℝ] ℝ)
    (stokes : StokesTheoremWitness.{uE, uP, uVolume, uΩ} D.A resolvent D.boundary)
    (horizonOperator_eq_flux :
      D.horizonOperator =
        geometricCoreProjector D.A resolvent D.boundary normalizationFactor)
    (scalarFlux_eq_entropy :
      FluxEqualsBoundaryEntropy
        D.A resolvent D.boundary normalizationFactor observer
        D.geometry D.boundaryCharges) :
    OperatorFreudenthalBoundaryFluxBridge.{uE, uP, uQ, uΩ, uVolume} D where
  phase := phase
  resolvent := resolvent
  normalizationFactor := normalizationFactor
  observer := observer
  stokes := stokes
  horizonOperator_eq_flux := horizonOperator_eq_flux
  scalarFlux_eq_entropy := scalarFlux_eq_entropy

end

end InfoGeometry.Canonical.GeometricCalculus
