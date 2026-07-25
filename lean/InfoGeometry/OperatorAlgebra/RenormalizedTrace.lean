/-
InfoGeometry/OperatorAlgebra/RenormalizedTrace.lean

Singular traces, Dixmier-style logarithmic traces, and zeta regularization.

This module separates ordinary traces, modular weights, core traces,
singular/Dixmier traces, and zeta-regularized finite-part or residue readouts.

For type III algebras, singular traces should be routed through the continuous
core or another semifinite backend, not placed directly on the type III base.
-/

import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ModularWeightTrace

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Singular trace backends -/

/--
A singular trace backend on an ambient operator algebra or ideal.

This is the abstract socket for Dixmier/Macaev/weak-L¹ traces. The analytic
ideal, measurability, and vanishing-on-trace-class properties are carried as
certificates because they depend on the concrete operator model.
-/
structure SingularTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  /-- Domain/ideal on which the singular trace is intended to be meaningful. -/
  ideal : Set A
  /-- Singular trace readout. -/
  singularTrace : A → ℝ≥0∞
  /-- Cyclicity on the chosen ideal. -/
  cyclic_on_ideal :
    ∀ a b : A,
      a ∈ ideal → b ∈ ideal →
        singularTrace (a * b) = singularTrace (b * a)
  /-- Certificate that this trace vanishes on ordinary trace-class noise. -/
  vanishes_on_trace_class : Prop
  /-- Certificate that this backend detects logarithmic spectral divergence. -/
  logarithmic_growth_backend : Prop

/--
A Dixmier-style trace datum.

This is a specialization marker over a singular trace. Concrete modules may
supply weak-L¹/Macaev ideal membership and measurability hypotheses.
-/
structure DixmierTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  singular : SingularTraceDatum A
  /-- Operators whose Dixmier trace is independent of generalized limit. -/
  measurable : Set A

namespace DixmierTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (Dix : DixmierTraceDatum A)

/-- The Dixmier trace readout. -/
def trace : A → ℝ≥0∞ :=
  Dix.singular.singularTrace

/-- Re-export cyclicity on the singular-trace ideal. -/
theorem cyclic_apply
    {a b : A}
    (ha : a ∈ Dix.singular.ideal)
    (hb : b ∈ Dix.singular.ideal) :
    Dix.trace (a * b) = Dix.trace (b * a) :=
  Dix.singular.cyclic_on_ideal a b ha hb

end DixmierTraceDatum

/-! ## 2. Zeta regularization backends -/

/--
Zeta-function regularization datum.

This packages the meromorphic/zeta readout `ζ_T(s)` together with residue and
finite-part extraction. It does not assume a particular analytic continuation
theorem; that theorem is supplied by concrete models.
-/
structure ZetaRegularizationDatum
    (A : Type*) where
  /-- Zeta function attached to an operator/readout. -/
  zeta : A → ℂ → ℂ
  /-- Points where the zeta function is regular. -/
  regularAt : A → ℂ → Prop
  /-- Points where the zeta function may have a pole/residue. -/
  singularAt : A → ℂ → Prop
  /-- Residue extraction at a point. -/
  residue : A → ℂ → ℂ
  /-- Finite-part extraction at a point. -/
  finitePart : A → ℂ → ℂ
  /-- Analytic continuation certificate. -/
  meromorphic_continuation : Prop

/--
Compatibility alias for older spectral-triple sockets that used the
`ZetaRegularizedTraceDatum` name.
-/
abbrev ZetaRegularizedTraceDatum
    (A : Type*) : Type _ :=
  ZetaRegularizationDatum A

/--
A real-valued zeta potential extracted from a regularized determinant or zeta
readout.
-/
structure ZetaPotentialDatum
    (A : Type*) where
  zetaRegularization : ZetaRegularizationDatum A
  /-- Positive amplitude readout used inside `-log`. -/
  amplitude : A → ℝ
  /-- Domain where the amplitude is strictly positive. -/
  admissible : A → Prop
  amplitude_pos :
    ∀ x : A, admissible x → 0 < amplitude x

namespace ZetaPotentialDatum

variable {A : Type*}
variable (Z : ZetaPotentialDatum A)

/-- Zeta/logarithmic potential. -/
def potential (x : A) : ℝ :=
  - Real.log (Z.amplitude x)

end ZetaPotentialDatum

/-! ## 3. Residue trace bridges -/

/--
Bridge between a singular trace and a zeta residue.

This is the abstract version of Connes-trace-type formulas:

`singularTrace(T) = constant * residue ζ_T(s₀)`

under regularity/measurability hypotheses.
-/
structure ResidueTraceBridge
    (A : Type*) [AddCommMonoid A] [Mul A] where
  singular : SingularTraceDatum A
  zeta : ZetaRegularizationDatum A
  /-- Distinguished pole/dimension point. -/
  pole : ℂ
  /-- Normalizing constant. -/
  constant : ℂ
  /-- Chosen complex readout of the extended nonnegative singular trace. -/
  singularTraceComplex : ℝ≥0∞ → ℂ
  /-- Bridge formula certificate. -/
  residue_trace_formula :
    ∀ T : A,
      T ∈ singular.ideal →
        singularTraceComplex (singular.singularTrace T) =
          constant * zeta.residue T pole

/-! ## 4. Type III routing through the core -/

/--
A singular trace backend routed through a crossed-product/continuous core.

This is the type III-safe version: the base algebra `M` is not given a bare
Dixmier trace. The singular trace lives on `Core`, where the core trace or
semifinite singular-value theory can be used.
-/
structure CoreSingularTraceDatum
    (M Core : Type*) [AddCommMonoid Core] [Mul Core] where
  coreTrace : CoreTraceDatum M Core
  singularCoreTrace : SingularTraceDatum Core
  /-- Base readout routed through the core embedding. -/
  baseSingularTrace : M → ℝ≥0∞ :=
    fun x => singularCoreTrace.singularTrace (coreTrace.embed x)

/--
A type III renormalized integration socket:

base integration uses a modular weight; singular/logarithmic readouts are
computed on the crossed-product core.
-/
structure TypeIIIRenormalizedTraceDatum
    (M Core : Type*)
    [AddCommMonoid M]
    [AddCommMonoid Core] [Mul Core] where
  typeIIIIntegration : TypeIIIIntegrationDatum M Core
  coreSingular : CoreSingularTraceDatum M Core

/-! ## 5. Cyclic cocycle backend socket -/

/--
A cyclic-cocycle or JLO/local-index backend.

This consumes one of the previous integration mechanisms. It is intentionally
abstract: the concrete cocycle formula depends on summability, heat-kernel
regularity, dimension spectrum, and grading.
-/
structure RenormalizedCyclicCocycleDatum
    (A : Type*) where
  degree : ℕ
  /-- Multilinear cocycle readout. -/
  cocycle : List A → ℂ
  /-- Cyclicity or twisted cyclicity certificate. -/
  cyclicity : Prop
  /-- Closedness/cocycle equation certificate. -/
  cocycle_condition : Prop
  /-- Backend kind used to construct the cocycle. -/
  backendKind : IntegrationBackendKind

/--
Separated renormalized integration backends.

This compatibility socket keeps existing spectral-triple layers explicit about
whether a readout is singular, zeta-regularized, or cocycle-based.
-/
inductive RenormalizedTraceBackend
    (A : Type*) [AddCommMonoid A] [Mul A] where
  | dixmierTrace (τ : DixmierTraceDatum A)
  | zetaRegularizedTrace (ζ : ZetaRegularizationDatum A)
  | singularTrace (τ : SingularTraceDatum A)
  | renormalizedCyclicCocycle (φ : RenormalizedCyclicCocycleDatum A)

/-! ## 6. Owner targets -/

/-- Owner target for choosing a singular/Dixmier trace backend. -/
def SingularTraceOwnerTarget
    (A : Type*) [AddCommMonoid A] [Mul A] : Prop :=
  ∃ τ : SingularTraceDatum A,
    ∀ a b : A,
      a ∈ τ.ideal → b ∈ τ.ideal →
        τ.singularTrace (a * b) = τ.singularTrace (b * a)

/-- Owner target for choosing a zeta-regularization backend. -/
def ZetaRegularizationOwnerTarget
    (A : Type*) : Prop :=
  ∃ ζ : ZetaRegularizationDatum A,
    ζ.meromorphic_continuation

/-- Owner target for a type III-safe renormalized trace backend. -/
def TypeIIIRenormalizedTraceOwnerTarget
    (M Core : Type*)
    [AddCommMonoid M]
    [AddCommMonoid Core] [Mul Core] : Prop :=
  ∃ T : TypeIIIRenormalizedTraceDatum M Core,
    ∀ x : M,
      T.coreSingular.baseSingularTrace x =
        T.coreSingular.singularCoreTrace.singularTrace
          (T.coreSingular.coreTrace.embed x)

end InfoGeometry.OperatorAlgebra
