import Mathlib
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

  /-- Siegel--Jacobi domain datum. -/
  SiegelJacobiDomain : Type

  /-- Matrix index / Jacobi index datum. -/
  IndexData : Type

  /-- Level / congruence subgroup datum. -/
  LevelData : Type

  /-- Weight datum. -/
  WeightData : Type

  /-- Nebentypus / character datum, if present. -/
  CharacterData : Type

/--
A Siegel--Jacobi modular form packet.

This is deliberately structural: it records the form and the automorphy law as
external data, not as a theorem of this file.
-/
structure SiegelJacobiFormPacket
    (D : SiegelJacobiDatum) where
  /-- The underlying Siegel--Jacobi modular form object. -/
  form : Type

  /-- Fourier coefficient data. -/
  FourierCoefficientData : Type

  /-- Cuspidality datum, if the form is cuspidal. -/
  CuspidalityData : Type

  /-- Hecke action datum. -/
  HeckeActionData : Type

  /-- Hecke eigenform witness/data. -/
  HeckeEigenData : Type

  /-- Automorphy law witness. -/
  automorphyLawWitness : Type

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

  /-- Analytic continuation witness. -/
  analyticContinuationWitness : Type

  /-- Functional-equation witness, if separated from the completed-L packet. -/
  functionalEquationWitness : Type

  /-- Witness that the Dirichlet-series readout realizes `L` in its convergence region. -/
  dirichletSeriesWitness : Type

  /-- Witness that the Euler product realizes `L` in its convergence region. -/
  eulerProductWitness : Type

namespace SiegelJacobiStandardLFunctionPacket

variable {D : SiegelJacobiDatum}
variable {F : SiegelJacobiFormPacket D}

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
structure SiegelJacobiProjectedRealization
    {Bulk : Type uBulk} {Boundary : Type uBoundary}
    [AddCommGroup Bulk] [Module ℝ Bulk]
    [AddCommGroup Boundary] [Module ℝ Boundary]
    (W : SiegelEisensteinWitness Bulk Boundary)
    (D : SiegelJacobiDatum)
    (F : SiegelJacobiFormPacket D)
    (SJ : SiegelJacobiStandardLFunctionPacket D F) where
  /-- Existing projected automorphic L-function witness. -/
  projected : ProjectedAutomorphicLFunctionWitness W

  /-- Compatibility between the projected automorphic L-function and `SJ.L`. -/
  projected_eq_standard :
    projected.L = SJ.L

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
    R.projected.L s = SJ.L s := by
  rw [R.projected_eq_standard]

/--
A zero/resonance of the projected L-function is a zero/resonance of the
standard Siegel--Jacobi L-function.
-/
theorem projected_resonance_iff_standard_zero
    (R : SiegelJacobiProjectedRealization W D F SJ)
    (s : ℂ) :
    IsAutomorphicResonance R.projected.L s ↔ SJ.L s = 0 := by
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
    LanglandsPrimeResonanceStrongWitness R.projected where
  eulerProduct :=
    transportEulerProductWitness R.projected_eq_standard SJ.eulerProduct
  completed :=
    transportCompletedLFunctionWitness R.projected_eq_standard SJ.completedLFunction

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
    LanglandsPrimeResonanceWitness R.projected :=
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
