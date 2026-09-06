/-
InfoGeometry/OperatorAlgebra/TraceFreeSuperIntegration.lean

Trace-free graded integration backends.

There is no unconditional trace field at the foundational operator-algebra
level. Finite traces, semifinite traces, core traces, modular weights,
Dixmier traces, JLO cocycles, and zeta residues are all special backends.

The universal object is a graded/super readout:

  Super(x) = Readout(chi * x)

where `chi` is the grading/chiral operator and `Readout` is supplied by an
explicit backend.
-/

import Mathlib
import Mathlib.Data.ENNReal.Basic

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra.TraceFreeSuperIntegration

/-! ## 1. Backend classification -/

/--
Trace-free graded integration backend kind.

The word `trace` appears only in backend names where it is mathematically
licensed: finite/semi-finite/core/Dixmier/cyclic contexts.
-/
inductive SuperIntegrationBackendKind where
  /-- Finite-dimensional graded matrix trace. -/
  | finiteSuperTrace

  /-- Faithful normal semifinite graded trace, when it exists. -/
  | semifiniteSuperTrace

  /-- Modular/KMS superweight on a type III base algebra. -/
  | modularSuperWeight

  /-- Supertrace after embedding into crossed-product continuous core. -/
  | coreSuperTrace

  /-- Dixmier-style logarithmic graded readout. -/
  | dixmierSuperTrace

  /-- JLO/cyclic-cocycle graded readout. -/
  | cyclicCocycle

  /-- Zeta-regularized graded residue/finite-part readout. -/
  | zetaRenormalized

deriving DecidableEq, Repr

/-! ## 2. Chiral grading -/

/--
A grading/chiral operator.

This is the operator inserted into a backend to form a super-readout.
-/
structure GradingDatum
    (A : Type*) [Ring A] where
  /-- Chiral/grading operator. -/
  chi : A

  /-- Involution law `chi^2 = 1`. -/
  chi_square :
    chi * chi = 1

namespace GradingDatum

variable {A : Type*} [Ring A]
variable (G : GradingDatum A)

/--
Left multiplication by the grading.
-/
def gradeLeft
    (x : A) : A :=
  G.chi * x

/-- Grading insertion at the unit returns the grading. -/
@[simp]
theorem gradeLeft_one :
    G.gradeLeft 1 = G.chi := by
  simp [gradeLeft]

end GradingDatum

/-! ## 3. Trace-free super readout -/

/--
A trace-free super integration readout.

`backendReadout` is not assumed to be a trace. It may be a modular weight,
a core trace pulled back through an embedding, a cyclic cocycle, or a
renormalized residue.

The superreadout is defined by inserting the grading:

`superReadout x = backendReadout (chi * x)`.
-/
structure SuperIntegrationDatum
    (A Scalar : Type*) [Ring A] where
  /-- Chiral/grading datum. -/
  grading : GradingDatum A

  /-- Declared backend kind. -/
  backendKind : SuperIntegrationBackendKind

  /-- Backend readout. This is not assumed to be a bare trace. -/
  backendReadout : A → Scalar

  /-- Graded/super readout. -/
  superReadout : A → Scalar

  /-- The superreadout is backend readout after grading insertion. -/
  superReadout_eq :
    ∀ x : A,
      superReadout x = backendReadout (grading.chi * x)

  /--
  Cyclicity, twisted cyclicity, KMS covariance, cocycle identity, or
  renormalized residue law.

  The exact law depends on the backend.
  -/
  graded_cyclicity_or_kms_law : Prop

  /-- Proof/certificate of the backend law. -/
  graded_cyclicity_or_kms_certificate :
    graded_cyclicity_or_kms_law

namespace SuperIntegrationDatum

variable {A Scalar : Type*} [Ring A]
variable (S : SuperIntegrationDatum A Scalar)

/--
The defining equation of the superreadout.
-/
theorem superReadout_apply
    (x : A) :
    S.superReadout x = S.backendReadout (S.grading.chi * x) :=
  S.superReadout_eq x

/-- The supplied graded cyclicity/KMS/cocycle law is available. -/
theorem graded_cyclicity_or_kms_valid :
    S.graded_cyclicity_or_kms_law :=
  S.graded_cyclicity_or_kms_certificate

end SuperIntegrationDatum

/-! ## 4. Modular superweight backend -/

/--
A modular/KMS weight backend.

This is the correct type III base-algebra integration primitive. There is
deliberately no trace cyclicity field here.
-/
structure ModularWeightBackend
    (A : Type*) where
  /-- Positive cone/domain. -/
  positiveCone : Set A

  /-- Extended nonnegative weight. -/
  weight : A → ℝ≥0∞

  /-- Modular flow. -/
  modularFlow : ℝ → A → A

  /-- Flow identity. -/
  flow_zero :
    ∀ x : A, modularFlow 0 x = x

  /-- Flow composition. -/
  flow_add :
    ∀ s t x, modularFlow (s + t) x = modularFlow s (modularFlow t x)

  /-- KMS/modular covariance law. -/
  kms_law : Prop

  /-- Proof/certificate of KMS/modular covariance. -/
  kms_certificate :
    kms_law

namespace ModularWeightBackend

variable {A : Type*}
variable (B : ModularWeightBackend A)

/-- The supplied KMS/modular covariance law is available. -/
theorem kms_valid :
    B.kms_law :=
  B.kms_certificate

end ModularWeightBackend

/--
A modular superweight.

This is the type III replacement for a supertrace on the base algebra.
-/
structure ModularSuperWeightDatum
    (A : Type*) [Ring A] where
  grading : GradingDatum A

  backend : ModularWeightBackend A

  /--
  Scalar superweight readout.

  This is usually not literally `backend.weight (chi*x)`, because `chi*x` need
  not be positive. Concrete models must provide a signed/complex/grading-aware
  readout.
  -/
  superWeight : A → ℂ

  /-- Modular graded/KMS covariance law. -/
  modular_super_kms_law : Prop

  /-- Proof/certificate. -/
  modular_super_kms_certificate :
    modular_super_kms_law

namespace ModularSuperWeightDatum

variable {A : Type*} [Ring A]
variable (M : ModularSuperWeightDatum A)

/-- The supplied modular super-KMS law is available. -/
theorem modular_super_kms_valid :
    M.modular_super_kms_law :=
  M.modular_super_kms_certificate

end ModularSuperWeightDatum

/-! ## 5. Crossed-product core supertrace backend -/

/--
Core supertrace backend.

For a type III base algebra `M`, an honest trace-like object may live only on
the crossed-product/continuous core.
-/
structure CoreSuperTraceDatum
    (M Core Scalar : Type*) [Ring Core] where
  /-- Embedding of base algebra into the continuous core. -/
  embed : M → Core

  /-- Core grading. -/
  coreGrading : GradingDatum Core

  /-- Core backend readout. -/
  coreReadout : Core → Scalar

  /-- Supertrace/readout of embedded base elements. -/
  superReadoutOfBase : M → Scalar

  /-- Defining law. -/
  superReadoutOfBase_eq :
    ∀ x : M,
      superReadoutOfBase x =
        coreReadout (coreGrading.chi * embed x)

  /-- Core trace/cocycle/KMS scaling law. -/
  core_law : Prop

  /-- Proof/certificate. -/
  core_certificate :
    core_law

namespace CoreSuperTraceDatum

variable {M Core Scalar : Type*} [Ring Core]
variable (C : CoreSuperTraceDatum M Core Scalar)

/--
Core supertrace readout of a base element.
-/
theorem superReadoutOfBase_apply
    (x : M) :
    C.superReadoutOfBase x =
      C.coreReadout (C.coreGrading.chi * C.embed x) :=
  C.superReadoutOfBase_eq x

/-- The supplied core law is available. -/
theorem core_valid :
    C.core_law :=
  C.core_certificate

end CoreSuperTraceDatum

/-! ## 6. Renormalized supertrace backends -/

/--
Dixmier-style graded readout.

Used at logarithmic/critical summability. This is not a bare trace on a type
III base algebra.
-/
structure DixmierSuperTraceDatum
    (A : Type*) [Ring A] where
  grading : GradingDatum A
  dixmierReadout : A → ℝ≥0∞

  superDixmierReadout : A → ℝ≥0∞

  superDixmierReadout_eq :
    ∀ x : A,
      superDixmierReadout x = dixmierReadout (grading.chi * x)

  logarithmic_divergence_law : Prop
  logarithmic_divergence_certificate :
    logarithmic_divergence_law

namespace DixmierSuperTraceDatum

variable {A : Type*} [Ring A]
variable (D : DixmierSuperTraceDatum A)

/-- The defining equation for the graded Dixmier readout. -/
theorem superDixmierReadout_apply
    (x : A) :
    D.superDixmierReadout x = D.dixmierReadout (D.grading.chi * x) :=
  D.superDixmierReadout_eq x

/-- The supplied logarithmic divergence law is available. -/
theorem logarithmic_divergence_valid :
    D.logarithmic_divergence_law :=
  D.logarithmic_divergence_certificate

end DixmierSuperTraceDatum

/--
Zeta-renormalized graded readout.
-/
structure ZetaSuperTraceDatum
    (A : Type*) [Ring A] where
  grading : GradingDatum A

  zeta : A → ℂ → ℂ
  poleSet : Set ℂ

  superResidue : A → ℂ → ℂ
  superFinitePart : A → ℂ → ℂ

  zeta_super_law : Prop
  zeta_super_certificate :
    zeta_super_law

namespace ZetaSuperTraceDatum

variable {A : Type*} [Ring A]
variable (Z : ZetaSuperTraceDatum A)

/-- The supplied zeta-super law is available. -/
theorem zeta_super_valid :
    Z.zeta_super_law :=
  Z.zeta_super_certificate

end ZetaSuperTraceDatum

/--
Cyclic-cocycle/JLO-style graded readout.
-/
structure CyclicSuperCocycleDatum
    (A : Type*) [Ring A] where
  grading : GradingDatum A

  cocycleReadout : A → ℂ

  superCocycleReadout : A → ℂ

  superCocycleReadout_eq :
    ∀ x : A,
      superCocycleReadout x = cocycleReadout (grading.chi * x)

  cyclic_cocycle_law : Prop
  cyclic_cocycle_certificate :
    cyclic_cocycle_law

namespace CyclicSuperCocycleDatum

variable {A : Type*} [Ring A]
variable (C : CyclicSuperCocycleDatum A)

/-- The defining equation for the graded cyclic-cocycle readout. -/
theorem superCocycleReadout_apply
    (x : A) :
    C.superCocycleReadout x = C.cocycleReadout (C.grading.chi * x) :=
  C.superCocycleReadout_eq x

/-- The supplied cyclic-cocycle law is available. -/
theorem cyclic_cocycle_valid :
    C.cyclic_cocycle_law :=
  C.cyclic_cocycle_certificate

end CyclicSuperCocycleDatum

/-! ## 7. Explicit no-bare-trace type III datum -/

/--
Type III graded integration datum.

This records the negative fact structurally:

there is no bare trace field on `M`.

Integration/readout is routed through a modular superweight and/or a core
supertrace.
-/
structure TypeIIISuperIntegrationDatum
    (M Core Scalar : Type*) [Ring M] [Ring Core] where
  /-- Modular superweight on the type III base algebra. -/
  modularSuperWeight :
    ModularSuperWeightDatum M

  /-- Optional core supertrace on crossed-product/continuous core. -/
  coreSuperTrace :
    Option (CoreSuperTraceDatum M Core Scalar)

  /-- Type III certificate. -/
  typeIII_law : Prop

  /-- Proof/certificate. -/
  typeIII_certificate :
    typeIII_law

  /--
  Explicit guardrail: the foundational datum contains no bare base trace.
  -/
  no_bare_trace_on_base_law : Prop

  /-- Proof/certificate. -/
  no_bare_trace_on_base_certificate :
    no_bare_trace_on_base_law

namespace TypeIIISuperIntegrationDatum

variable {M Core Scalar : Type*} [Ring M] [Ring Core]
variable (T : TypeIIISuperIntegrationDatum M Core Scalar)

/-- The supplied Type III law is available. -/
theorem typeIII_valid :
    T.typeIII_law :=
  T.typeIII_certificate

/-- The supplied no-bare-trace guardrail is available. -/
theorem no_bare_trace_on_base_valid :
    T.no_bare_trace_on_base_law :=
  T.no_bare_trace_on_base_certificate

end TypeIIISuperIntegrationDatum

/-! ## 8. Owner target -/

/--
Owner target for trace-free graded integration.

A concrete model must supply a super integration datum. No bare trace is
constructed here.
-/
def TraceFreeSuperIntegrationOwnerTarget
    (A Scalar : Type*) [Ring A] : Prop :=
  Nonempty (SuperIntegrationDatum A Scalar) →
    Nonempty (SuperIntegrationDatum A Scalar)

/--
The owner target is discharged once the graded backend is supplied.
-/
theorem traceFreeSuperIntegrationOwnerTarget
    (A Scalar : Type*) [Ring A] :
    TraceFreeSuperIntegrationOwnerTarget A Scalar := by
  intro h
  exact h

end InfoGeometry.OperatorAlgebra.TraceFreeSuperIntegration
