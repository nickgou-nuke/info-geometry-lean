import Mathlib

/-!
# InfoGeometry/Canonical/GeometricCalculusSurgery.lean

Real geometric-calculus roadmap for operator surgery on real Banach/Krein
spaces.

This file does not replace the complex Dunford-Taylor owner theorem. It states
the real Clifford/Stokes API that should eventually be bridged to the
complexified Riesz projection and Koliha-Drazin calculus.

The key rule is:

* no fake resolvent definitions;
* no untyped expression `(p - A)⁻¹`;
* no theorem-shaped placeholders asserting new mathematics;
* all analytic claims are routed through named proposition targets.
-/

namespace InfoGeometry.Canonical.GeometricCalculus

open MeasureTheory
open Topology

noncomputable section

/-- Real bounded endomorphisms of a normed real space. -/
abbrev RealEnd
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E

/-! ## 1. Real phase generators -/

/--
A real geometric phase generator.

The elliptic case `B² = -1` behaves like a compatible complex structure.
The split/hyperbolic case `B² = +1` is a boost generator and should not be
silently identified with ordinary complex holomorphic calculus.
-/
structure BivectorPhase
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  B : RealEnd E
  square_eq_neg_or_pos :
    B * B = -ContinuousLinearMap.id ℝ E ∨
    B * B = ContinuousLinearMap.id ℝ E

/-! ## 2. Paravector representation and Clifford resolvent field -/

/--
A representation of paravector spectral parameters as bounded real
endomorphisms.

This is the missing typing layer behind the informal expression `p - A`.
-/
structure ParavectorRepresentation
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toEnd : P → RealEnd E

/--
A Clifford resolvent field for a bounded real operator `A`.

`R p` is intended to model `(ρ(p) - A)⁻¹` on its admissible parameter domain.
The inverse identities are stated as proof fields, not hidden behind a fake
definition returning `0`.
-/
structure CliffordResolventField
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ParavectorRepresentation P E)
    (A : RealEnd E) where
  domain : Set P
  R : P → RealEnd E

  left_inverse_on_domain :
    ∀ p : P, p ∈ domain →
      (ρ.toEnd p - A) * R p = 1

  right_inverse_on_domain :
    ∀ p : P, p ∈ domain →
      R p * (ρ.toEnd p - A) = 1

/-! ## 3. Directed boundaries and Stokes flux -/

/--
A directed boundary in paravector space.

The field `surfaceAction` encodes the Clifford directed surface element `dS`
acting on the operator-valued field. This avoids pretending that a bare
parameter point is itself the oriented surface element.
-/
structure DirectedBoundary
    (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Param : Type*
  [measurableSpace : MeasurableSpace Param]
  μ : Measure Param

  /-- Boundary parametrization. -/
  point : Param → P

  /--
  Directed surface action.

  Mathematically this represents multiplication by the Clifford surface element
  `dS`. It is left abstract until the repository has a concrete Clifford
  algebra API.
  -/
  surfaceAction : Param → RealEnd E → RealEnd E

/--
Boundary flux integral

`∫_{∂Ω} dS · F(p)`,

encoded by the boundary's `surfaceAction`.
-/
def stokesBoundaryIntegral
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (bdry : DirectedBoundary P E)
    (F : P → RealEnd E) : RealEnd E :=
  letI := bdry.measurableSpace
  ∫ x, bdry.surfaceAction x (F (bdry.point x)) ∂bdry.μ

/--
Geometric flux projector candidate.

This is only a construction from a chosen Clifford resolvent field and a chosen
directed boundary. Idempotence is a separate proposition target.
-/
def geometricFluxProjector
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (bdry : DirectedBoundary P E)
    (R : P → RealEnd E)
    (normalization : ℝ) : RealEnd E :=
  normalization • stokesBoundaryIntegral bdry R

/-! ## 4. Named proposition targets -/

/--
Admissibility of a boundary for a Clifford resolvent field.

A future concrete version should assert:

* the boundary lies in the resolvent domain;
* the boundary encloses the intended spectral defect/horizon;
* the orientation and normalization are compatible with the Clifford Cauchy
  kernel;
* no unintended spectral branch crosses the boundary.
-/
def BoundaryAdmissible
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (_R : CliffordResolventField ρ A)
    (_bdry : DirectedBoundary P E) : Prop :=
  True

/--
Placeholder for monogenicity of the Clifford resolvent field away from the
defect locus.

Mathematically this is the condition `∇R = 0` on the punctured domain.
-/
def MonogenicOffDefects
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (_R : CliffordResolventField ρ A) : Prop :=
  True

/--
Placeholder for the generalized Stokes/Cauchy flux statement.

The concrete version should express that the boundary flux depends only on the
enclosed defect data.
-/
def BoundaryFluxEqualsDefectSum
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (_R : CliffordResolventField ρ A)
    (_bdry : DirectedBoundary P E)
    (_normalization : ℝ) : Prop :=
  True

/--
Bridge target: the real geometric flux projector agrees with the
complexified Riesz projector after choosing compatible data.

This is the key theorem needed before the geometric calculus layer can replace
any complex Dunford-Taylor owner theorem downstream.
-/
def GeometricFluxMatchesComplexifiedRieszProjection
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (phase : BivectorPhase E)
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ)
    (complexifiedRieszAsReal : RealEnd E) : Prop :=
  phase.B * phase.B = -ContinuousLinearMap.id ℝ E →
    geometricFluxProjector bdry R.R normalization = complexifiedRieszAsReal

/-! ## 5. Stokes witness and projector statements -/

/--
Witness package for the real Stokes/Clifford flux layer.

This is not yet a Drazin theorem. It is the geometric-calculus owner surface
that a later bridge theorem may connect to the Dunford/Riesz projector.
-/
structure StokesFluxWitness
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ) where

  boundary_admissible :
    BoundaryAdmissible R bdry

  monogenic_off_defects :
    MonogenicOffDefects R

  boundary_flux_eq_defect_sum :
    BoundaryFluxEqualsDefectSum R bdry normalization

namespace GeometricFluxProjector

/--
Statement that a geometric boundary flux is idempotent.

This is deliberately conditional on the Stokes/Clifford witness.
-/
def idempotentStatement
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ) : Prop :=
  StokesFluxWitness R bdry normalization →
    let Pcore := geometricFluxProjector bdry R.R normalization
    Pcore * Pcore = Pcore

/--
Statement that the geometric flux projector commutes with the bounded operator.

For unbounded closed operators, this must be replaced by a domain-sensitive
reduction statement.
-/
def commutesStatement
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ρ : ParavectorRepresentation P E}
    {A : RealEnd E}
    (R : CliffordResolventField ρ A)
    (bdry : DirectedBoundary P E)
    (normalization : ℝ) : Prop :=
  StokesFluxWitness R bdry normalization →
    let Pcore := geometricFluxProjector bdry R.R normalization
    Pcore * A = A * Pcore

end GeometricFluxProjector

end

end InfoGeometry.Canonical.GeometricCalculus
