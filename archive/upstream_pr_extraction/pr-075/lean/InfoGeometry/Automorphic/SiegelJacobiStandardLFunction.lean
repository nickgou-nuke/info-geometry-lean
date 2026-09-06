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

  /-- Hecke eigenform property/data. -/
  HeckeEigenData : Type

  /-- Exact automorphy law for the supplied form and factor. -/
  automorphyLaw :
    ∀ g z,
      form (g • z) = automorphyFactor g z * form z

/-!
The following carriers replace theorem-shaped `Type` placeholders in the standard
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

theorem AnalyticContinuationData.continuousOn
    {L : ℂ → ℂ} (A : AnalyticContinuationData L) :
    ContinuousOn A.continuation A.domain := by
  exact A.holomorphic.continuousOn

/-- A convergent series realization of a complex-valued function. -/
structure DirichletSeriesRealization (L : ℂ → ℂ) where
  term : ℕ → ℂ → ℂ
  convergenceRegion : Set ℂ
  convergenceRegion_open : IsOpen convergenceRegion
  summable : ∀ s, s ∈ convergenceRegion → Summable (fun n => term n s)
  realizes : ∀ s, s ∈ convergenceRegion → L s = ∑' n, term n s

theorem DirichletSeriesRealization.hasSum
    {L : ℂ → ℂ} (D : DirichletSeriesRealization L)
    {s : ℂ} (hs : s ∈ D.convergenceRegion) :
    HasSum (fun n => D.term n s) (L s) := by
  rw [D.realizes s hs]
  exact (D.summable s hs).hasSum

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

  /-- Euler-product property compatible with the existing automorphic lane. -/
  eulerProduct : EulerProductProperty L

  /-- Completed L-function property compatible with the existing automorphic lane. -/
  completedLFunction : CompletedLFunctionData L

  /-- Klingen-type Eisenstein-series or integral-representation datum. -/
  EisensteinSeriesData : Type

  /-- Actual holomorphic continuation data. -/
  analyticContinuation : AnalyticContinuationData L

  /-- Actual convergent series realization of `L`. -/
  dirichletSeries : DirichletSeriesRealization L

namespace SiegelJacobiStandardLFunctionPacket

variable {D : SiegelJacobiDatum}
variable {F : SiegelJacobiFormPacket D}

end SiegelJacobiStandardLFunctionPacket

/--
Projected realization packet.

This connects a Siegel--Jacobi standard L-function packet to the existing
`ProjectedAutomorphicLFunctionData` API.

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
  { projected : ProjectedAutomorphicLFunctionData W //
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

end InfoGeometry.Automorphic.SiegelJacobi
