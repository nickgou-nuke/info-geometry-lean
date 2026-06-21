import Mathlib

/-!
# InfoGeometry/Canonical/GeometricCalculusSurgery.lean

Real geometric-calculus roadmap for operator surgery on double real Krein spaces.

This module does not assert analytic theorems about arbitrary boundaries. It
provides the structural API for Stokes/Clifford functional calculus.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open MeasureTheory
open Topology

noncomputable section

/-- Bounded real-linear endomorphisms. -/
abbrev RealEnd
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E

/--
A real geometric phase generator.

Elliptic phases satisfy `B² = -1`; hyperbolic/split phases satisfy `B² = +1`.
-/
structure BivectorPhase
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  B : RealEnd E
  isGenerator :
    B * B = -(ContinuousLinearMap.id ℝ E) ∨
      B * B = ContinuousLinearMap.id ℝ E

/--
A directed boundary in paravector space.

The explicit measurable-space field is necessary for Bochner integration.
-/
structure DirectedBoundary
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  Carrier : Type*
  instMeasurableSpace : MeasurableSpace Carrier
  boundaryMeasure : MeasureTheory.Measure Carrier
  directedSurfaceElement : Carrier → P

attribute [instance] DirectedBoundary.instMeasurableSpace

/--
A Clifford resolvent family for a fixed operator `A`.

This replaces the non-canonical placeholder

`cliffordResolvent A p := 0`.

The future Clifford-algebra API should refine this with the actual inverse law
for `(p - A)⁻¹`.
-/
structure CliffordResolventFamily
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (_A : RealEnd E) where
  resolvent : P → RealEnd E

/--
Boundary Stokes integral

`∫_{∂Ω} dS f(p)`.
-/
def stokesBoundaryIntegral
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Ω : DirectedBoundary P)
    (f : P → RealEnd E) : RealEnd E :=
  letI : MeasurableSpace Ω.Carrier := Ω.instMeasurableSpace
  MeasureTheory.integral Ω.boundaryMeasure
    (fun x => f (Ω.directedSurfaceElement x))

/--
Geometric core projector produced by the boundary flux of a Clifford resolvent.
-/
def geometricCoreProjector
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ) : RealEnd E :=
  normalizationFactor • stokesBoundaryIntegral Ω R.resolvent

/--
Finite monogenicity socket on a parameterized volume.

Until a full Dirac-operator API is supplied, monogenicity is represented by the
non-vacuous algebraic resolvent commutation law along the parameterized volume.
-/
def IsMonogenicOn
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (_Ω : DirectedBoundary P)
    (Volume : Type*)
    (param : Volume → P) : Prop :=
  ∀ v : Volume, R.resolvent (param v) * A = A * R.resolvent (param v)

/-- Non-vacuous Stokes defect/flux socket: every boundary resolvent has zero
commutator defect against the surgery operator. -/
def BoundaryFluxEqualsDefectSum
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (_Ω : DirectedBoundary P) : Prop :=
  ∀ p : P, R.resolvent p * A - A * R.resolvent p = 0

/--
Stokes witness for the Clifford resolvent field.

The fields are proofs of named predicates, not arbitrary `Prop` slots.
-/
structure StokesTheoremWitness
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P) where
  Volume : Type*
  parameterization : Volume → P
  monogenic :
    IsMonogenicOn A R Ω Volume parameterization
  boundaryFluxEqDefectSum :
    BoundaryFluxEqualsDefectSum A R Ω

namespace GeometricCoreProjector

/-- Idempotence statement for an admissible geometric flux projector. -/
def IsIdempotentStatement
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ) : Prop :=
  let Pcore := geometricCoreProjector A R Ω normalizationFactor
  Pcore * Pcore = Pcore

/-- Commutation statement for an admissible geometric flux projector. -/
def CommutesStatement
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ) : Prop :=
  let Pcore := geometricCoreProjector A R Ω normalizationFactor
  Pcore * A = A * Pcore

/--
Admissibility certificate for a geometric Stokes projector.

Projection laws require analytic/topological hypotheses; they are not true for
an arbitrary boundary and arbitrary resolvent family.
-/
structure IsAdmissibleFluxProjector
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : RealEnd E)
    (R : CliffordResolventFamily (P := P) A)
    (Ω : DirectedBoundary P)
    (normalizationFactor : ℝ) : Prop where
  idempotent :
    IsIdempotentStatement A R Ω normalizationFactor
  commutes :
    CommutesStatement A R Ω normalizationFactor

theorem idempotent_of_admissible
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : RealEnd E}
    {R : CliffordResolventFamily (P := P) A}
    {Ω : DirectedBoundary P}
    {normalizationFactor : ℝ}
    (h : IsAdmissibleFluxProjector A R Ω normalizationFactor) :
    IsIdempotentStatement A R Ω normalizationFactor :=
  h.idempotent

theorem commutes_of_admissible
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : RealEnd E}
    {R : CliffordResolventFamily (P := P) A}
    {Ω : DirectedBoundary P}
    {normalizationFactor : ℝ}
    (h : IsAdmissibleFluxProjector A R Ω normalizationFactor) :
    CommutesStatement A R Ω normalizationFactor :=
  h.commutes

end GeometricCoreProjector

end

end InfoGeometry.Canonical.GeometricCalculus
