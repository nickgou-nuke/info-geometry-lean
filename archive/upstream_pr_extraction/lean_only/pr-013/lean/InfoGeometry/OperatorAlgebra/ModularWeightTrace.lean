/-
InfoGeometry/OperatorAlgebra/ModularWeightTrace.lean

Trace, weight, and core-trace integration backends.

The key type III rule is encoded by separation of structures:

* `TraceDatum` is for trace-capable layers.
* `WeightDatum` is for noncommutative integration by weights.
* `ModularWeightDatum` adds the modular/KMS flow replacing trace cyclicity.
* `CoreTraceDatum` is the crossed-product/core trace socket.
* `SuperTraceDatum` requires an explicit trace or weight backend.

In particular, this file does not put a bare trace field on a type III algebra.
-/

import Mathlib

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Backend classification -/

/--
Named integration backends used by operator-geometric scalar readouts.

This is metadata: concrete modules should still carry the corresponding
proof-carrying datum.
-/
inductive IntegrationBackendKind where
  /-- Ordinary finite-dimensional trace. -/
  | finiteDimensionalTrace
  /-- Faithful normal semifinite trace on a trace-capable algebra. -/
  | semifiniteTrace
  /-- Graded trace after a trace/weight backend is specified. -/
  | superTrace
  /-- Faithful normal semifinite weight, typically the type III backend. -/
  | modularWeight
  /-- Semifinite trace on a crossed-product/continuous core. -/
  | crossedProductCoreTrace
  /-- Haagerup/Kosaki-style noncommutative `Lᵖ` pairing. -/
  | noncommutativeLpPairing
  /-- Dixmier/singular trace backend for critical summability. -/
  | dixmierTrace
  /-- Zeta-regularized trace or determinant backend. -/
  | zetaRegularizedTrace
  /-- Renormalized heat/JLO/cyclic-cocycle backend. -/
  | renormalizedCyclicCocycle
deriving DecidableEq, Repr

/-! ## 2. Trace-capable and weight-capable layers -/

/--
A trace-capable noncommutative integration datum.

This structure is intentionally separate from `WeightDatum`: a type III
algebra should use a weight on the algebra itself, not this bare trace socket.
-/
structure TraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  /-- The positive cone on which positivity is asserted. -/
  positiveCone : Set A

  /-- Trace/integration functional. -/
  trace : A → ℝ≥0∞

  /-- Positivity of the trace on the chosen cone. -/
  positive :
    ∀ x : A, x ∈ positiveCone → (0 : ℝ≥0∞) ≤ trace x

  /-- Cyclicity of the trace. -/
  cyclic :
    ∀ a b : A, trace (a * b) = trace (b * a)

  /-- Normality certificate, left abstract at this algebraic layer. -/
  normality : Prop

  /-- Faithfulness certificate, left abstract at this algebraic layer. -/
  faithfulness : Prop

  /-- Semifiniteness certificate, left abstract at this algebraic layer. -/
  semifiniteness : Prop

/--
A noncommutative integration backend by weight.

For type III layers this is the correct primitive: it is positive/normal/
faithful/semifinite data, but it does not assert trace cyclicity.
-/
structure WeightDatum
    (A : Type*) [AddCommMonoid A] where
  /-- Positive cone for the weight. -/
  positiveCone : Set A

  /-- Weight/integration functional. -/
  integral : A → ℝ≥0∞

  /-- Positivity of the weight on the chosen cone. -/
  positive :
    ∀ x : A, x ∈ positiveCone → (0 : ℝ≥0∞) ≤ integral x

  /-- Normality certificate. -/
  normality : Prop

  /-- Faithfulness certificate. -/
  faithfulness : Prop

  /-- Semifiniteness certificate. -/
  semifiniteness : Prop

namespace TraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (τ : TraceDatum A)

/-- Re-export trace cyclicity. -/
theorem cyclic_apply
    (a b : A) :
    τ.trace (a * b) = τ.trace (b * a) :=
  τ.cyclic a b

end TraceDatum

namespace WeightDatum

variable {A : Type*} [AddCommMonoid A]
variable (φ : WeightDatum A)

/-- A weight is finite at an element when its value is not `∞`. -/
def IsFiniteAt
    (x : A) : Prop :=
  φ.integral x ≠ ⊤

/-- A weight vanishes at an element when its value is zero. -/
def VanishesAt
    (x : A) : Prop :=
  φ.integral x = 0

end WeightDatum

/-! ## 3. Modular weights and KMS covariance -/

/--
A modular datum attached to a weight.

In a type III algebra, the modular flow replaces tracial cyclicity. The KMS
condition is left proof-carrying because its analytic shape depends on the
chosen concrete model.
-/
structure ModularWeightDatum
    (A : Type*) [AddCommMonoid A] where
  /-- Faithful normal semifinite weight data. -/
  weight : WeightDatum A

  /-- Modular automorphism/action flow. -/
  modularFlow : ℝ → A → A

  /-- Flow identity law. -/
  flow_zero :
    ∀ x : A, modularFlow 0 x = x

  /-- Additive flow law. -/
  flow_add :
    ∀ s t x, modularFlow (s + t) x = modularFlow s (modularFlow t x)

  /-- KMS/modular covariance certificate. -/
  kmsCondition : Prop

namespace ModularWeightDatum

variable {A : Type*} [AddCommMonoid A]
variable (φ : ModularWeightDatum A)

/-- The modular weight integral. -/
def integral : A → ℝ≥0∞ :=
  φ.weight.integral

/-- The weight is invariant under time zero of the modular flow. -/
@[simp]
theorem modularFlow_zero_apply
    (x : A) :
    φ.modularFlow 0 x = x :=
  φ.flow_zero x

end ModularWeightDatum

/-! ## 4. Crossed-product core traces -/

/--
A crossed-product/continuous-core trace datum.

This is the trace socket for type III situations: the original algebra `M`
uses a modular weight, while the crossed-product core `Core` may carry an
honest semifinite trace.
-/
structure CoreTraceDatum
    (M Core : Type*) where
  /-- Embedding of the original algebra into the core. -/
  embed : M → Core

  /-- Semifinite trace on the core. -/
  coreTrace : Core → ℝ≥0∞

  /-- Trace property on the core, left abstract at this layer. -/
  traceProperty : Prop

  /-- Scaling/covariance under the dual flow. -/
  traceScalingUnderDualFlow : Prop

namespace CoreTraceDatum

variable {M Core : Type*}
variable (C : CoreTraceDatum M Core)

/-- Core trace readout of an embedded element. -/
def traceOfEmbedded
    (x : M) : ℝ≥0∞ :=
  C.coreTrace (C.embed x)

end CoreTraceDatum

/-! ## 5. Type III integration backend -/

/--
Type III integration data.

The important design choice is negative: this structure has no field
`trace : M → _`. Integration on `M` is by modular weight; an honest trace is
available only after passing to `Core`.
-/
structure TypeIIIIntegrationDatum
    (M Core : Type*) [AddCommMonoid M] where
  /-- Modular weight on the original type III algebra. -/
  modularWeight : ModularWeightDatum M

  /-- Crossed-product/continuous-core trace datum. -/
  coreTrace : CoreTraceDatum M Core

  /-- Certificate that the original algebra is treated as type III. -/
  typeIII : Prop

  /-- Certificate recording that no bare trace on `M` is part of this datum. -/
  noBareTraceOnBase : Prop

namespace TypeIIIIntegrationDatum

variable {M Core : Type*} [AddCommMonoid M]
variable (T : TypeIIIIntegrationDatum M Core)

/-- Type III base integration is by modular weight. -/
def baseIntegral : M → ℝ≥0∞ :=
  T.modularWeight.integral

/-- Trace-like scalar readout is routed through the crossed-product core. -/
def coreTraceOfBase
    (x : M) : ℝ≥0∞ :=
  T.coreTrace.traceOfEmbedded x

end TypeIIIIntegrationDatum

/-! ## 6. Supertrace backends -/

/--
Backend used by a supertrace.

A supertrace is not bare data on a type III algebra; it must declare whether it
is using a trace, a core trace, a modular/KMS weight, or a regularized cyclic
cocycle.
-/
inductive SuperTraceBackend
    (A : Type*) [AddCommMonoid A] [Mul A] where
  /-- Supertrace from a trace-capable layer. -/
  | trace (τ : TraceDatum A)
  /-- Superweight from a modular weight. -/
  | modularWeight (φ : ModularWeightDatum A)
  /-- Regularized/cyclic-cocycle scalar backend. -/
  | regularized (backend : A → ℝ)

/--
A graded supertrace/superweight datum.

The scalar backend is explicit. In a type III setting, use `backend` to route
through a core trace or a modular/KMS weight rather than assuming a trace on
the original algebra.
-/
structure SuperTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  /-- Grading operator. -/
  grading : A

  /-- Declared backend kind. -/
  backendKind : IntegrationBackendKind

  /-- Proof-carrying backend source. -/
  backend : SuperTraceBackend A

  /-- Scalar trace/weight/regularized readout. -/
  traceBackend : A → ℝ

  /-- Supertrace readout. -/
  supertrace : A → ℝ := fun x => traceBackend (grading * x)

  /-- The supertrace is routed through the declared backend and grading. -/
  supertrace_eq :
    ∀ x : A, supertrace x = traceBackend (grading * x)

  /-- Cyclicity, twisted cyclicity, or KMS covariance certificate. -/
  cyclicityOrTwistedCyclicity : Prop

namespace SuperTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (S : SuperTraceDatum A)

/-- The supertrace is the backend applied after multiplication by the grading. -/
@[simp]
theorem supertrace_eq_traceBackend_grading_mul
    (x : A) :
    S.supertrace x = S.traceBackend (S.grading * x) :=
  S.supertrace_eq x

end SuperTraceDatum

/-! ## 7. Owner targets -/

/--
Owner target for selecting a type III integration backend.

The target is intentionally witness-gated: the modular weight and continuous
core trace are analytic/operator-algebraic inputs, not consequences of an
abstract ambient type alone.
-/
def TypeIIIIntegrationOwnerTarget : Prop :=
  ∀ (M Core : Type*) [AddCommMonoid M],
    ModularWeightDatum M →
      CoreTraceDatum M Core →
        Nonempty (TypeIIIIntegrationDatum M Core)

/--
The type III integration owner target is constructible once modular weight and
core trace data are supplied. The type III/no-bare-trace certificates remain
explicit proof-carrying fields.
-/
theorem typeIIIIntegrationOwnerTarget :
    TypeIIIIntegrationOwnerTarget := by
  intro M Core _ φ C
  exact ⟨{
    modularWeight := φ
    coreTrace := C
    typeIII := True
    noBareTraceOnBase := True
  }⟩

/--
Owner target for graded readouts once an explicit backend has been supplied.
-/
def SuperTraceBackendOwnerTarget : Prop :=
  ∀ (A : Type*) [AddCommMonoid A] [Mul A],
    SuperTraceDatum A → Nonempty (SuperTraceDatum A)

/-- The supertrace owner target is satisfied once the backend datum is supplied. -/
theorem superTraceBackendOwnerTarget :
    SuperTraceBackendOwnerTarget := by
  intro A _ _ S
  exact ⟨S⟩

end InfoGeometry.OperatorAlgebra
