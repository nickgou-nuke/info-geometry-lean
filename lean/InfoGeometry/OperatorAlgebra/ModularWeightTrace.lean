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

import Mathlib.Tactic

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
`x` is the least upper bound of an increasing sequence for an explicitly
installed positive order.  Operator algebras need not carry a lattice order on
all elements, so the order is supplied on the integration datum.
-/
def IsIncreasingSequentialSup
    {A : Type*} (le : A → A → Prop) (u : ℕ → A) (x : A) : Prop :=
  (∀ n, le (u n) (u (n + 1))) ∧
    (∀ y, (∀ n, le (u n) y) ↔ le x y)

/--
A trace-capable noncommutative integration datum.

This structure is intentionally separate from `WeightDatum`: a type III
algebra should use a weight on the algebra itself, not this bare trace socket.
-/
structure TraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  /-- The positive cone on which positivity is asserted. -/
  positiveCone : Set A

  /-- Positive order used by the sequential normality law. -/
  positiveLE : A → A → Prop

  /-- Trace/integration functional. -/
  trace : A → ℝ≥0∞

  /-- Cyclicity of the trace. -/
  cyclic :
    ∀ a b : A, trace (a * b) = trace (b * a)

  /-- Sequential normality on increasing positive elements. -/
  normality :
    ∀ (u : ℕ → A) (x : A),
      (∀ n, u n ∈ positiveCone) →
      IsIncreasingSequentialSup positiveLE u x →
      trace x = ⨆ n, trace (u n)

  /-- Faithfulness on the selected positive cone. -/
  faithfulness :
    ∀ x : A, x ∈ positiveCone → trace x = 0 → x = 0

  /--
  Semifiniteness through an explicit positive subdomain on which the trace is
  finite.
  -/
  semifiniteness :
    ∃ S : Set A, S ⊆ positiveCone ∧ ∀ x ∈ S, trace x < ⊤

/--
A noncommutative integration backend by weight.

For type III layers this is the correct primitive: it is positive/normal/
faithful/semifinite data, but it does not assert trace cyclicity.
-/
structure WeightDatum
    (A : Type*) [AddCommMonoid A] where
  /-- Positive cone for the weight. -/
  positiveCone : Set A

  /-- Positive order used by the sequential normality law. -/
  positiveLE : A → A → Prop

  /-- Weight/integration functional. -/
  integral : A → ℝ≥0∞

  /-- Sequential normality on increasing positive elements. -/
  normality :
    ∀ (u : ℕ → A) (x : A),
      (∀ n, u n ∈ positiveCone) →
      IsIncreasingSequentialSup positiveLE u x →
      integral x = ⨆ n, integral (u n)

  /-- Faithfulness on the selected positive cone. -/
  faithfulness :
    ∀ x : A, x ∈ positiveCone → integral x = 0 → x = 0

  /--
  Semifiniteness through an explicit positive subdomain on which the weight is
  finite.
  -/
  semifiniteness :
    ∃ S : Set A, S ⊆ positiveCone ∧ ∀ x ∈ S, integral x < ⊤

namespace TraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (τ : TraceDatum A)

/-- Nonnegativity is native to the `ℝ≥0∞` codomain; it is not stored evidence. -/
theorem positive
    (x : A) (_hx : x ∈ τ.positiveCone) :
    (0 : ℝ≥0∞) ≤ τ.trace x :=
  bot_le

/-- Re-export trace cyclicity. -/
theorem cyclic_apply
    (a b : A) :
    τ.trace (a * b) = τ.trace (b * a) :=
  τ.cyclic a b

/-- A positive element with zero trace is zero. -/
theorem eq_zero_of_mem_positiveCone_of_trace_eq_zero
    {x : A}
    (hx : x ∈ τ.positiveCone)
    (htrace : τ.trace x = 0) :
    x = 0 :=
  τ.faithfulness x hx htrace

/-- The trace has an explicit positive finite-valued subdomain. -/
theorem exists_finite_positive_subdomain :
    ∃ S : Set A, S ⊆ τ.positiveCone ∧
      ∀ x ∈ S, τ.trace x < ⊤ :=
  τ.semifiniteness

end TraceDatum

/-! ## 2a. No-wrapper cyclic linear trace selection rule -/

/-- Algebra commutator used by the no-wrapper spectral selection rule. -/
def modularSpectralCommutator {A : Type*} [Ring A] (H X : A) : A :=
  H * X - X * H

/-- Eigenstate equation `[H, X] = λX` for a real algebra. -/
def IsModularSpectralEigenstate {A : Type*} [Ring A] [Algebra ℝ A]
    (H X : A) (lam : ℝ) : Prop :=
  modularSpectralCommutator H X = (algebraMap ℝ A lam) * X

/-- A cyclic real-linear trace vanishes on algebra commutators. -/
theorem linearTrace_modularSpectralCommutator_zero
    {A : Type*} [Ring A] [Algebra ℝ A]
    (tau : A →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : A, tau (x * y) = tau (y * x))
    (H X : A) :
    tau (modularSpectralCommutator H X) = 0 := by
  unfold modularSpectralCommutator
  rw [tau.map_sub]
  rw [hcyclic H X]
  ring

/--
No-wrapper modular spectral selection rule.

If a real-linear cyclic trace is compatible with left scalar multiplication and
`X` is a nonzero-frequency commutator eigenmode, then the trace of `X` is zero.
-/
theorem modular_spectral_selection_rule
    {A : Type*} [Ring A] [Algebra ℝ A]
    (tau : A →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : A, tau (x * y) = tau (y * x))
    (hscale : ∀ (c : ℝ) (x : A), tau ((algebraMap ℝ A c) * x) = c * tau x)
    (H X : A) (lam : ℝ)
    (hEig : IsModularSpectralEigenstate H X lam) (hlam : lam ≠ 0) :
    tau X = 0 := by
  have htr := linearTrace_modularSpectralCommutator_zero tau hcyclic H X
  unfold IsModularSpectralEigenstate at hEig
  rw [hEig] at htr
  rw [hscale lam X] at htr
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero hlam htr

namespace WeightDatum

variable {A : Type*} [AddCommMonoid A]
variable (φ : WeightDatum A)

/-- Nonnegativity is native to the `ℝ≥0∞` codomain; it is not stored evidence. -/
theorem positive
    (x : A) (_hx : x ∈ φ.positiveCone) :
    (0 : ℝ≥0∞) ≤ φ.integral x :=
  bot_le

/-- A weight is finite at an element when its value is not `∞`. -/
def IsFiniteAt
    (x : A) : Prop :=
  φ.integral x ≠ ⊤

/-- A weight vanishes at an element when its value is zero. -/
def VanishesAt
    (x : A) : Prop :=
  φ.integral x = 0

/-- A positive element with zero weight is zero. -/
theorem eq_zero_of_mem_positiveCone_of_integral_eq_zero
    {x : A}
    (hx : x ∈ φ.positiveCone)
    (hintegral : φ.integral x = 0) :
    x = 0 :=
  φ.faithfulness x hx hintegral

/-- The weight has an explicit positive finite-valued subdomain. -/
theorem exists_finite_positive_subdomain :
    ∃ S : Set A, S ⊆ φ.positiveCone ∧
      ∀ x ∈ S, φ.integral x < ⊤ :=
  φ.semifiniteness

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

  /--
  Modular invariance of the weight.

  This is the exact real-time covariance law available at this algebraic
  layer.  A full KMS boundary condition additionally needs multiplication,
  complex-time analyticity, and boundary values, none of which are hidden in
  this structure.
  -/
  weight_invariant :
    ∀ t x, weight.integral (modularFlow t x) = weight.integral x

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

/-- The modular flow preserves the installed noncommutative weight. -/
theorem integral_modularFlow
    (t : ℝ) (x : A) :
    φ.integral (φ.modularFlow t x) = φ.integral x :=
  φ.weight_invariant t x

end ModularWeightDatum

/-! ## 4. Crossed-product core traces -/

/--
A crossed-product/continuous-core trace datum.

This is the trace socket for type III situations: the original algebra `M`
uses a modular weight, while the crossed-product core `Core` may carry an
honest semifinite trace.
-/
structure CoreTraceDatum
    (M Core : Type*) [Mul Core] where
  /-- Embedding of the original algebra into the core. -/
  embed : M → Core

  /-- Semifinite trace on the core. -/
  coreTrace : Core → ℝ≥0∞

  /-- Dual action on the crossed-product/continuous core. -/
  dualAction : ℝ → Core → Core

  /-- The zero parameter acts identically on the core. -/
  dualAction_zero :
    ∀ x : Core, dualAction 0 x = x

  /-- The additive real parameter acts by composition. -/
  dualAction_add :
    ∀ (s t : ℝ) (x : Core),
      dualAction (s + t) x = dualAction s (dualAction t x)

  /-- Genuine cyclic trace law on the noncommutative core. -/
  traceProperty :
    ∀ x y : Core, coreTrace (x * y) = coreTrace (y * x)

  /--
  Covariance law under the dual flow.

  This owner follows the invariant convention already used by
  `TypeIIIContinuousCoreReal.RealContinuousCoreInterface`.
  -/
  traceScalingUnderDualFlow :
    ∀ (t : ℝ) (x : Core),
      coreTrace (dualAction t x) = coreTrace x

namespace CoreTraceDatum

variable {M Core : Type*} [Mul Core]
variable (C : CoreTraceDatum M Core)

/-- Core trace readout of an embedded element. -/
def traceOfEmbedded
    (x : M) : ℝ≥0∞ :=
  C.coreTrace (C.embed x)

/-- The core trace is cyclic on products. -/
theorem coreTrace_mul_comm (x y : Core) :
    C.coreTrace (x * y) = C.coreTrace (y * x) :=
  C.traceProperty x y

/-- Readback of the identity element of the real dual action. -/
theorem dualAction_zero_apply (x : Core) :
    C.dualAction 0 x = x :=
  C.dualAction_zero x

/-- Readback of composition for the real dual action. -/
theorem dualAction_add_apply (s t : ℝ) (x : Core) :
    C.dualAction (s + t) x =
      C.dualAction s (C.dualAction t x) :=
  C.dualAction_add s t x

/-- The continuous-core trace is invariant under the selected dual action. -/
theorem coreTrace_dualAction (t : ℝ) (x : Core) :
    C.coreTrace (C.dualAction t x) = C.coreTrace x :=
  C.traceScalingUnderDualFlow t x

end CoreTraceDatum

/-! ## 5. Type III integration backend -/

/--
Type III integration data.

The important design choice is negative: this structure has no field
`trace : M → _`. Integration on `M` is by modular weight; an honest trace is
available only after passing to `Core`.
-/
structure TypeIIIIntegrationDatum
    (M Core : Type*) [AddCommMonoid M] [Mul Core] where
  /-- Modular weight on the original type III algebra. -/
  modularWeight : ModularWeightDatum M

  /-- Crossed-product/continuous-core trace datum. -/
  coreTrace : CoreTraceDatum M Core

namespace TypeIIIIntegrationDatum

variable {M Core : Type*} [AddCommMonoid M] [Mul Core]
variable (T : TypeIIIIntegrationDatum M Core)

/-- The base integration backend is definitionally a modular weight. -/
def typeIII (_T : TypeIIIIntegrationDatum M Core) : IntegrationBackendKind :=
  .modularWeight

/--
The absence of a bare base trace is enforced by the type of
`TypeIIIIntegrationDatum`: its only base functional is the modular weight.
-/
theorem noBareTraceOnBase :
    T.typeIII = IntegrationBackendKind.modularWeight :=
  rfl

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

  /-- Supertrace is grading-twist by `grading`. -/
  supertrace_eq :
      ∀ x : A, supertrace x = traceBackend (grading * x) := by
    intro x
    rfl

  /-- Twist used by a KMS or graded backend; ordinary cyclicity uses `id`. -/
  twist : A → A := id

  /-- Concrete twisted-cyclicity law for the selected supertrace backend. -/
  cyclicityOrTwistedCyclicity :
    ∀ x y : A, supertrace (x * y) = supertrace (twist y * x)

namespace SuperTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (S : SuperTraceDatum A)

/-- The supertrace is the backend applied after multiplication by the grading. -/
@[simp]
theorem supertrace_eq_traceBackend_grading_mul
    (x : A) :
    S.supertrace x = S.traceBackend (S.grading * x) :=
  by
    simpa [SuperTraceDatum.supertrace] using S.supertrace_eq x

/-- The selected supertrace backend satisfies its installed twisted cyclicity law. -/
theorem supertrace_mul_eq_twisted_mul
    (x y : A) :
    S.supertrace (x * y) = S.supertrace (S.twist y * x) :=
  S.cyclicityOrTwistedCyclicity x y

end SuperTraceDatum

end InfoGeometry.OperatorAlgebra
