import InfoGeometry.Canonical.GradedTraceBridge
import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge

/-!
# Graded Trace Colimit Bridge

This file crosses the categorical boundary for the graded-trace/KMS identity.

`GradedTraceBridge` proves the normalized projection-level identity

`τL0(S*_n S_m) = ζβ * Φ.φ(S*_n S_m)`.

The theorem below transports any such identity through a compatible categorical
cone into an algebraic direct limit.  It does not assert an analytic infinite
trace formula, a topological completion, or `Tr(q^L0) = ζ(β)`.  It proves only
the category-induction fact: stage-zero identity plus compatible finite-stage
transport implies the same identity on every canonical direct-limit image.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `gradedTrace_identity_crosses_colimit`: compatible-cone induction carries a
  graded-trace identity from stage zero to every direct-limit image.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.  The theorem is generic and depends only on explicit cone compatibility
and a stage-zero identity.

#### BUCKET 3: OPEN CLOSURE DEBT

This file does not construct the analytic Sugawara trace, prove zeta as an
infinite trace, or prove uniqueness/classification of KMS states.
-/

noncomputable section

namespace InfoGeometry.Canonical.GradedTraceColimitBridge

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/--
Category-induction transport of the graded-trace/KMS identity to the colimit.

Given a compatible cone `toLimit` over a stage tower, a compatible observable
family `observable`, and a stage-zero identity

`τL0(toLimit 0 observable₀) = ζβ * φ(toLimit 0 observable₀)`,

the same identity holds after reading every stage through the universal
direct-limit lift.
-/
theorem gradedTrace_identity_crosses_colimit
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : CompatibleCone bond toLimit)
    (observable : ∀ n : Nat, Stage n)
    (hobservable : ∀ n : Nat, bond n (observable n) = observable (n + 1))
    (τL0 φ : Limit → ℝ) (ζβ : ℝ)
    (h0 : τL0 (toLimit 0 (observable 0)) = ζβ * φ (toLimit 0 (observable 0))) :
    ∀ n : Nat,
      τL0 (directLimitLift bond toLimit hcone (directLimitOf bond n (observable n))) =
        ζβ * φ (directLimitLift bond toLimit hcone (directLimitOf bond n (observable n))) := by
  intro n
  rw [directLimit_readback bond toLimit hcone n (observable n)]
  have hconst : toLimit n (observable n) = toLimit 0 (observable 0) :=
    cone_stageImage_constant bond toLimit hcone observable hobservable n
  rw [hconst]
  exact h0

end InfoGeometry.Canonical.GradedTraceColimitBridge
