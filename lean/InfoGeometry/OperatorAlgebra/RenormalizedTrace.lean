/-
InfoGeometry/OperatorAlgebra/RenormalizedTrace.lean

Singular traces, Dixmier-style logarithmic traces, and zeta regularization.

This module separates ordinary traces, modular weights, core traces,
singular/Dixmier traces, and zeta-regularized finite-part or residue readouts.

For type III algebras, singular traces should be routed through the continuous
core or another semifinite backend, not placed directly on the type III base.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Meromorphic.Basic
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
  /-- The ordinary trace-class part of the ambient singular ideal. -/
  traceClassIdeal : Set A
  /-- Trace-class operators belong to the domain of the singular trace. -/
  traceClassIdeal_le_ideal : traceClassIdeal ⊆ ideal
  /-- A singular trace vanishes on every ordinary trace-class operator. -/
  singularTrace_eq_zero_of_mem_traceClass :
    ∀ T : A, T ∈ traceClassIdeal → singularTrace T = 0
  /--
  Logarithmic Cesàro/singular-value mean supplied by the concrete weak-`L¹`
  model.  Keeping this readout explicit prevents a Boolean or bare-`Prop`
  marker from standing in for the analytic backend.
  -/
  logarithmicMean : A → ℝ≥0∞
  /-- On the singular ideal, the trace is the logarithmic-mean readout. -/
  singularTrace_eq_logarithmicMean :
    ∀ T : A, T ∈ ideal → singularTrace T = logarithmicMean T

namespace SingularTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (τ : SingularTraceDatum A)

/-- Re-export vanishing of a singular trace on its trace-class subideal. -/
theorem traceClass_vanishes {T : A} (hT : T ∈ τ.traceClassIdeal) :
    τ.singularTrace T = 0 :=
  τ.singularTrace_eq_zero_of_mem_traceClass T hT

/-- Re-export realization by the logarithmic mean on the singular ideal. -/
theorem trace_eq_logarithmicMean {T : A} (hT : T ∈ τ.ideal) :
    τ.singularTrace T = τ.logarithmicMean T :=
  τ.singularTrace_eq_logarithmicMean T hT

end SingularTraceDatum

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
  /-- Chosen continuation of the initial zeta readout. -/
  continuedZeta : A → ℂ → ℂ
  /-- The chosen continuation is genuinely meromorphic on the complex plane. -/
  continuedZeta_meromorphic :
    ∀ T : A, MeromorphicOn (continuedZeta T) Set.univ
  /-- The continuation agrees with the original readout at every regular point. -/
  continuedZeta_eq_zeta_of_regularAt :
    ∀ T : A, ∀ s : ℂ, regularAt T s → continuedZeta T s = zeta T s

namespace ZetaRegularizationDatum

variable {A : Type*}
variable (ζ : ZetaRegularizationDatum A)

/-- The regularized continuation is meromorphic everywhere. -/
theorem meromorphic_continuation (T : A) :
    MeromorphicOn (ζ.continuedZeta T) Set.univ :=
  ζ.continuedZeta_meromorphic T

/-- On the original regular locus, continuation does not change the zeta readout. -/
theorem continuation_agrees {T : A} {s : ℂ} (hs : ζ.regularAt T s) :
    ζ.continuedZeta T s = ζ.zeta T s :=
  ζ.continuedZeta_eq_zeta_of_regularAt T s hs

end ZetaRegularizationDatum

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

namespace CoreSingularTraceDatum

/-- Base readout routed through the core embedding. -/
def baseSingularTrace
    {M Core : Type*} [AddCommMonoid Core] [Mul Core]
    (T : CoreSingularTraceDatum M Core) : M → ℝ≥0∞ :=
  fun x => T.singularCoreTrace.singularTrace (T.coreTrace.embed x)

end CoreSingularTraceDatum

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

/-- Rotate the first entry of a Hochschild chain to the final position. -/
def cyclicRotate {A : Type*} : List A → List A
  | [] => []
  | a :: as => as ++ [a]

/-- Multiply the entries in positions `i` and `i + 1` of a Hochschild chain. -/
def multiplyAdjacent {A : Type*} [Mul A] : List A → ℕ → List A
  | [], _ => []
  | [a], _ => [a]
  | a :: b :: as, 0 => a * b :: as
  | a :: b :: as, i + 1 => a :: multiplyAdjacent (b :: as) i

/-- The closing Hochschild face, multiplying the last entry by the first. -/
def closingFace {A : Type*} [Mul A] : List A → List A
  | [] => []
  | [a] => [a]
  | a :: b :: as => (List.getLast (b :: as) (by simp) * a) :: (b :: as).dropLast

/--
The degree-`n` Hochschild coboundary of a list-valued complex cochain.

On a chain `[a₀, …, aₙ₊₁]` this is the alternating sum of the adjacent
multiplication faces, followed by the closing face
`[aₙ₊₁a₀, a₁, …, aₙ]`.
-/
def hochschildCoboundary
    {A : Type*} [Mul A]
    (n : ℕ) (φ : List A → ℂ) (chain : List A) : ℂ :=
  ((List.range (n + 1)).map
      (fun i => (-1 : ℂ) ^ i * φ (multiplyAdjacent chain i))).sum +
    (-1 : ℂ) ^ (n + 1) * φ (closingFace chain)

/--
A cyclic-cocycle or JLO/local-index backend.

This consumes one of the previous integration mechanisms. It is intentionally
abstract: the concrete cocycle formula depends on summability, heat-kernel
regularity, dimension spectrum, and grading.
-/
structure RenormalizedCyclicCocycleDatum
    (A : Type*) [Ring A] where
  degree : ℕ
  /-- Multilinear cocycle readout. -/
  cocycle : List A → ℂ
  /-- Signed cyclic invariance on chains of the owned arity. -/
  cyclicity :
    ∀ chain : List A,
      chain.length = degree + 1 →
        cocycle (cyclicRotate chain) = (-1 : ℂ) ^ degree * cocycle chain
  /-- Vanishing of the Hochschild coboundary on chains of the owned arity. -/
  cocycle_condition :
    ∀ chain : List A,
      chain.length = degree + 2 →
        hochschildCoboundary degree cocycle chain = 0
  /-- Backend kind used to construct the cocycle. -/
  backendKind : IntegrationBackendKind

namespace RenormalizedCyclicCocycleDatum

variable {A : Type*} [Ring A]
variable (φ : RenormalizedCyclicCocycleDatum A)

/-- Re-export the signed cyclic rotation law. -/
theorem cyclic_rotate
    {chain : List A} (hchain : chain.length = φ.degree + 1) :
    φ.cocycle (cyclicRotate chain) =
      (-1 : ℂ) ^ φ.degree * φ.cocycle chain :=
  φ.cyclicity chain hchain

/-- Re-export Hochschild closedness of the renormalized cocycle. -/
theorem hochschild_closed
    {chain : List A} (hchain : chain.length = φ.degree + 2) :
    hochschildCoboundary φ.degree φ.cocycle chain = 0 :=
  φ.cocycle_condition chain hchain

end RenormalizedCyclicCocycleDatum

/--
Separated renormalized integration backends.

This compatibility socket keeps existing spectral-triple layers explicit about
whether a readout is singular, zeta-regularized, or cocycle-based.
-/
inductive RenormalizedTraceBackend
    (A : Type*) [Ring A] where
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
    ∀ T : A, MeromorphicOn (ζ.continuedZeta T) Set.univ

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
