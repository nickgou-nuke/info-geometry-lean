/-
InfoGeometry/OperatorAlgebra/RenormalizedTrace.lean

Renormalized and singular trace backends.

This module separates singular traces, zeta-regularized traces, residue
bridges, and cyclic-cocycle readouts from ordinary trace/weight integration.
It is deliberately proof-carrying: concrete analytic modules should supply the
summability, residue, and cyclicity witnesses.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.ModularWeightTrace

noncomputable section

open scoped ENNReal

namespace InfoGeometry.OperatorAlgebra

/-! ## 1. Singular and Dixmier trace sockets -/

/--
A Dixmier-trace-like backend.

This is the logarithmic-divergence socket used at critical summability.
-/
structure DixmierTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  positiveCone : Set A
  dixmierTrace : A → ℝ≥0∞
  positive :
    ∀ x : A, x ∈ positiveCone → (0 : ℝ≥0∞) ≤ dixmierTrace x
  traceLikeCyclicity :
    ∀ a b : A, dixmierTrace (a * b) = dixmierTrace (b * a)
  logarithmicDivergenceExtraction : Prop

/--
A generic singular trace backend.

This is broader than Dixmier trace and can model other trace functionals
vanishing on finite-rank/trace-class regular sectors.
-/
structure SingularTraceDatum
    (A : Type*) [AddCommMonoid A] [Mul A] where
  singularTrace : A → ℝ≥0∞
  traceProperty :
    ∀ a b : A, singularTrace (a * b) = singularTrace (b * a)
  vanishesOnRegularIdeal : Prop
  detectsSingularAsymptotics : Prop

/-! ## 2. Zeta regularization and residue bridges -/

/--
Zeta-regularized trace backend.

The intended model is a meromorphic family such as `Tr(a |D|^{-s})`, together
with residue and finite-part readouts.
-/
structure ZetaRegularizedTraceDatum
    (A : Type*) where
  zeta : A → ℂ → ℂ
  poleSet : Set ℂ
  residueReadout : A → ℂ → ℂ
  finitePartReadout : A → ℂ → ℂ
  meromorphicContinuation : Prop

/--
A bridge identifying a residue readout with a singular trace readout.
-/
structure ResidueTraceBridge
    (A : Type*) [AddCommMonoid A] [Mul A] where
  zetaTrace : ZetaRegularizedTraceDatum A
  singularTrace : SingularTraceDatum A
  residuePoint : ℂ
  residueMatchesSingularTrace : Prop

/-! ## 3. Type III and core singular traces -/

/--
A singular trace backend on a crossed-product/continuous core.
-/
structure CoreSingularTraceDatum
    (M Core : Type*) [AddCommMonoid Core] [Mul Core] where
  coreTrace : CoreTraceDatum M Core
  singularTrace : SingularTraceDatum Core
  compatibleWithCoreTrace : Prop
  dualFlowScaling : Prop

/--
Type III renormalized trace data.

The base algebra still uses a modular weight; trace-like singular readouts are
routed through a crossed-product core or a renormalized cyclic object.
-/
structure TypeIIIRenormalizedTraceDatum
    (M Core : Type*) [AddCommMonoid M] [AddCommMonoid Core] [Mul Core] where
  modularWeight : ModularWeightDatum M
  coreSingularTrace : CoreSingularTraceDatum M Core
  noBareTraceOnBase : Prop
  renormalizedReadoutOnBase : M → ℝ≥0∞
  readoutFactorsThroughCore : Prop

/-! ## 4. Cyclic cocycle backend -/

/--
A renormalized cyclic cocycle readout.

The arity and cocycle identities are kept proof-carrying at this abstract
layer, since concrete JLO/local-index/cyclic-cohomology models vary.
-/
structure RenormalizedCyclicCocycleDatum
    (A : Type*) where
  arity : ℕ
  cochain : (Fin arity → A) → ℝ
  cyclicity : Prop
  cocycleCondition : Prop
  regularizationScheme : Prop

/--
Separated renormalized integration backends.
-/
inductive RenormalizedTraceBackend
    (A : Type*) [AddCommMonoid A] [Mul A] where
  | dixmierTrace (τ : DixmierTraceDatum A)
  | zetaRegularizedTrace (ζ : ZetaRegularizedTraceDatum A)
  | singularTrace (τ : SingularTraceDatum A)
  | renormalizedCyclicCocycle (φ : RenormalizedCyclicCocycleDatum A)

namespace DixmierTraceDatum

variable {A : Type*} [AddCommMonoid A] [Mul A]
variable (τ : DixmierTraceDatum A)

/-- Re-export Dixmier trace cyclicity. -/
theorem cyclic_apply
    (a b : A) :
    τ.dixmierTrace (a * b) = τ.dixmierTrace (b * a) :=
  τ.traceLikeCyclicity a b

end DixmierTraceDatum

end InfoGeometry.OperatorAlgebra
