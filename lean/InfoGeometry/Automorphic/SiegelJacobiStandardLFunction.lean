import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Automorphic.ProjectedLFunction

/-!
# InfoGeometry.Automorphic.SiegelJacobiStandardLFunction

Witness-gated owner surface for standard L-functions attached to
Siegel--Jacobi modular forms.

This module is designed for the Bouganis--Marzec style input:
standard L-functions of Siegel--Jacobi modular forms, Euler-product data, and
analytic-continuation / Eisenstein-series data.

It does not prove the analytic theorem. It records the theorem-safe packet shape
and adapters into the existing projected automorphic L-function lane.
-/

noncomputable section

namespace InfoGeometry.Automorphic.SiegelJacobi

open InfoGeometry.Automorphic.SiegelResonance

universe uBulk uBoundary

/--
A formal Siegel--Jacobi datum.

This keeps the geometric/arithmetic input abstract: Jacobi group, domain,
index, level, and form data are supplied as witnesses.
-/
structure SiegelJacobiDatum where
  /-- Jacobi group / Heisenberg-semidirect-symplectic datum. -/
  JacobiGroupData : Type
  [jacobiGroup : Group JacobiGroupData]

  /-- Siegel--Jacobi domain datum. -/
  SiegelJacobiDomain : Type
  [domainAction : MulAction JacobiGroupData SiegelJacobiDomain]

  /-- Matrix index / Jacobi index datum. -/
  IndexData : Type

  /-- Level / congruence subgroup datum. -/
  LevelData : Type

  /-- Weight datum. -/
  WeightData : Type

  /-- Nebentypus / character datum, if present. -/
  CharacterData : Type

attribute [instance] SiegelJacobiDatum.jacobiGroup
  SiegelJacobiDatum.domainAction

/--
A Siegel--Jacobi modular form packet.

This is deliberately structural: it records the form and the automorphy law as
external data, not as a theorem of this file.
-/
structure SiegelJacobiFormPacket
    (D : SiegelJacobiDatum) where
  /-- The underlying complex-valued Siegel--Jacobi modular form. -/
  form : D.SiegelJacobiDomain → ℂ

  /-- Automorphy factor for the supplied Jacobi group action. -/
  automorphyFactor : D.JacobiGroupData → D.SiegelJacobiDomain → ℂ

  /-- Fourier coefficient data. -/
  FourierCoefficientData : Type

  /-- Cuspidality datum, if the form is cuspidal. -/
  CuspidalityData : Type

  /-- Hecke action datum. -/
  HeckeActionData : Type

  /-- Hecke eigenform witness/data. -/
  HeckeEigenData : Type

  /-- Exact automorphy law for the supplied form and factor. -/
  automorphyLaw :
    ∀ g z,
      form (g • z) = automorphyFactor g z * form z

/-!
The following carriers replace theorem-shaped `Type` sockets in the standard
L-function packet with the actual analytic data used by the corresponding
Mathlib predicates.
-/

/-- A holomorphic continuation of a complex-valued function on an open set. -/
structure AnalyticContinuationData (L : ℂ → ℂ) where
  domain : Set ℂ
  domain_open : IsOpen domain
  continuation : ℂ → ℂ
  continuation_eq : ∀ z, z ∈ domain → continuation z = L z
  holomorphic : DifferentiableOn ℂ continuation domain

/-- A convergent series realization of a complex-valued function. -/
structure DirichletSeriesRealization (L : ℂ → ℂ) where
  term : ℕ → ℂ → ℂ
  convergenceRegion : Set ℂ
  convergenceRegion_open : IsOpen convergenceRegion
  summable : ∀ s, s ∈ convergenceRegion → Summable (fun n => term n s)
  realizes : ∀ s, s ∈ convergenceRegion → L s = ∑' n, term n s

/--
Standard L-function data attached to a Siegel--Jacobi modular form.

The Euler product and analytic continuation are explicit witnesses. This is the
theorem-safe surface corresponding to the analytic theorem layer.
-/
structure SiegelJacobiStandardLFunctionPacket
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D) where
  /-- The standard L-function as a complex-valued function of the spectral parameter. -/
  L : ℂ → ℂ

  /-- Dirichlet-series / coefficient readout datum. -/
  DirichletSeriesData : Type

  /-- Euler-product witness compatible with the existing automorphic lane. -/
  eulerProduct : EulerProductWitness L

  /-- Completed L-function witness compatible with the existing automorphic lane. -/
  completedLFunction : CompletedLFunctionWitness L

  /-- Klingen-type Eisenstein-series or integral-representation datum. -/
  EisensteinSeriesData : Type

  /-- Actual holomorphic continuation data. -/
  analyticContinuation : AnalyticContinuationData L

  /-- Actual convergent series realization of `L`. -/
  dirichletSeries : DirichletSeriesRealization L

namespace SiegelJacobiStandardLFunctionPacket

variable {D : SiegelJacobiDatum}
variable {F : SiegelJacobiFormPacket D}

/-- The completed packet supplies the functional-equation law. -/
def functionalEquationWitness
    (P : SiegelJacobiStandardLFunctionPacket D F) : Prop :=
  HasCompletedFunctionalEquation P.L P.completedLFunction.completedL

/-- The Euler-product owner supplies its realization law. -/
def eulerProductWitness
    (P : SiegelJacobiStandardLFunctionPacket D F) : Prop :=
  HasEulerProduct P.L P.eulerProduct.PrimeIndex
    P.eulerProduct.localFactor P.eulerProduct.convergenceRegion

/-- The series owner supplies its realization law. -/
def dirichletSeriesWitness
    (P : SiegelJacobiStandardLFunctionPacket D F) : Prop :=
  ∀ s, s ∈ P.dirichletSeries.convergenceRegion →
    P.L s = ∑' n, P.dirichletSeries.term n s

/-- The continuation owner supplies an actual holomorphic continuation. -/
def analyticContinuationWitness
    (P : SiegelJacobiStandardLFunctionPacket D F) : Prop :=
  DifferentiableOn ℂ P.analyticContinuation.continuation
    P.analyticContinuation.domain

/--
Forget the strong Siegel--Jacobi packet to the existing weak Euler-product data
used by `LanglandsPrimeResonanceWitness`.
-/
def toEulerProductData
    (P : SiegelJacobiStandardLFunctionPacket D F) :
    EulerProductData P.L :=
  P.eulerProduct.toEulerProductData

/--
Forget the strong Siegel--Jacobi completed-L packet to the existing
completed-functional-equation predicate.
-/
theorem toHasCompletedFunctionalEquation
    (P : SiegelJacobiStandardLFunctionPacket D F) :
    HasCompletedFunctionalEquation P.L P.completedLFunction.completedL :=
  P.completedLFunction.toHasCompletedFunctionalEquation

end SiegelJacobiStandardLFunctionPacket

/--
Projected realization packet.

This connects a Siegel--Jacobi standard L-function packet to the existing
`ProjectedAutomorphicLFunctionWitness` API.

The equality `projected.L = sj.L` is carried explicitly, because the projected
automorphic realization is model-specific arithmetic/geometric input.
-/
def SiegelJacobiProjectedRealization
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D)
    (SJ : SiegelJacobiStandardLFunctionPacket D F) :=
  { projected : ProjectedAutomorphicLFunctionWitness W //
      projected.L = SJ.L }

namespace SiegelJacobiProjectedRealization

variable
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {D : SiegelJacobiDatum}
    {F : SiegelJacobiFormPacket D}
    {SJ : SiegelJacobiStandardLFunctionPacket D F}

/--
Evaluation of the projected L-function agrees with the Siegel--Jacobi standard
L-function.
-/
theorem projected_eval_eq_standard
    (R : SiegelJacobiProjectedRealization W D F SJ)
    (s : ℂ) :
    R.1.L s = SJ.L s := by
  rw [R.2]

/--
A zero/resonance of the projected L-function is a zero/resonance of the
standard Siegel--Jacobi L-function.
-/
theorem projected_resonance_iff_standard_zero
    (R : SiegelJacobiProjectedRealization W D F SJ)
    (s : ℂ) :
    IsAutomorphicResonance R.1.L s ↔ SJ.L s = 0 := by
  unfold IsAutomorphicResonance
  rw [R.projected_eval_eq_standard s]

end SiegelJacobiProjectedRealization

/-- Transport an Euler-product witness across equality of L-functions. -/
def transportEulerProductWitness
    {L₁ L₂ : ℂ → ℂ}
    (h : L₁ = L₂)
    (E : EulerProductWitness L₂) :
    EulerProductWitness L₁ := by
  rw [h]
  exact E

/-- Transport a completed-L-function witness across equality of L-functions. -/
def transportCompletedLFunctionWitness
    {L₁ L₂ : ℂ → ℂ}
    (h : L₁ = L₂)
    (C : CompletedLFunctionWitness L₂) :
    CompletedLFunctionWitness L₁ := by
  rw [h]
  exact C

/--
Adapter from a Siegel--Jacobi projected realization to the existing strong
Langlands-prime resonance witness.
-/
def toLanglandsPrimeResonanceStrongWitness
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {D : SiegelJacobiDatum}
    {F : SiegelJacobiFormPacket D}
    {SJ : SiegelJacobiStandardLFunctionPacket D F}
    (R : SiegelJacobiProjectedRealization W D F SJ) :
    LanglandsPrimeResonanceStrongWitness R.1 where
  eulerProduct :=
    transportEulerProductWitness R.2 SJ.eulerProduct
  completed :=
    transportCompletedLFunctionWitness R.2 SJ.completedLFunction

/--
Adapter from a Siegel--Jacobi projected realization to the existing weak
Langlands-prime resonance witness.
-/
def toLanglandsPrimeResonanceWitness
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    {W : SiegelEisensteinWitness Bulk Boundary}
    {D : SiegelJacobiDatum}
    {F : SiegelJacobiFormPacket D}
    {SJ : SiegelJacobiStandardLFunctionPacket D F}
    (R : SiegelJacobiProjectedRealization W D F SJ) :
    LanglandsPrimeResonanceWitness R.1 :=
  (toLanglandsPrimeResonanceStrongWitness R).toWeakWitness

/-- Owner target for a supplied Siegel--Jacobi standard L-function packet. -/
abbrev SiegelJacobiStandardLFunctionTarget
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D) : Type 1 :=
  SiegelJacobiStandardLFunctionPacket D F

/-- Constructor for the Siegel--Jacobi standard L-function target. -/
def constructSiegelJacobiStandardLFunctionTarget
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D)
    (P : SiegelJacobiStandardLFunctionPacket D F) :
    SiegelJacobiStandardLFunctionTarget D F :=
  P

/--
Owner target for a supplied projected realization of a Siegel--Jacobi standard
L-function inside the existing Siegel-projector automorphic lane.
-/
abbrev SiegelJacobiProjectedRealizationTarget
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D)
    (SJ : SiegelJacobiStandardLFunctionPacket D F) : Type _ :=
  SiegelJacobiProjectedRealization W D F SJ

/-- Constructor for the projected-realization target. -/
def constructSiegelJacobiProjectedRealizationTarget
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D)
    (SJ : SiegelJacobiStandardLFunctionPacket D F)
    (R : SiegelJacobiProjectedRealization W D F SJ) :
    SiegelJacobiProjectedRealizationTarget W D F SJ :=
  R

end InfoGeometry.Automorphic.SiegelJacobi
