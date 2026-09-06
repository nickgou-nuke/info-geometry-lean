import InfoGeometry.Canonical.StandardFormNaturalConeBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.StandardFormExpectationUpdate

Dual-vector pairing bridge for modular expectation updates.

This file stays theorem-safe: it does not build a von Neumann algebra,
construct a predual, or derive a genuine Radon--Nikodym cocycle.  Instead, it
packages the exact witness form needed to express how a recursive modular
scaling engine updates the expectation readout through the cone-vector carrier.
-/

namespace InfoGeometry.Canonical.StandardFormExpectationUpdate

open InfoGeometry.Canonical.StandardFormNaturalConeBridge

/--
A standard-form expectation-update carrier.

The carrier records a cone-preserving recursive update on vectors together with
an update on normal positive functionals.  The only theorem-facing content is
that the updated functional is still read out by the updated cone vector.
-/
@[rep_depth operator]
structure StandardFormExpectationUpdateBridge
    (Alg Hilb NormalPositive : Type*) where
  /-- Underlying standard-form natural-cone interface. -/
  standardForm : NaturalConeStandardFormInterface Alg Hilb NormalPositive

  /-- Recursive modular scaling engine on the Hilbert carrier. -/
  composeModularScale : Nat → Hilb → Hilb

  /-- The recursive modular scaling engine preserves the natural cone. -/
  composeModularScale_mem :
    ∀ n : Nat, ∀ ξ : Hilb,
      ξ ∈ standardForm.cone → composeModularScale n ξ ∈ standardForm.cone

  /-- Update map on normal positive functionals. -/
  updateFunctional : Nat → NormalPositive → NormalPositive

  /-- Updated functionals remain normal positive. -/
  updateFunctional_mem :
    ∀ n : Nat, ∀ ω : NormalPositive,
      standardForm.isNormalPositive ω → standardForm.isNormalPositive (updateFunctional n ω)

  /-- The updated cone vector is exactly the recursively scaled cone vector. -/
  coneVector_composeModularScale :
    ∀ n : Nat, ∀ ω : NormalPositive,
      standardForm.coneVector (updateFunctional n ω) =
        composeModularScale n (standardForm.coneVector ω)

namespace StandardFormExpectationUpdateBridge

variable {Alg Hilb NormalPositive : Type*}
variable (B : StandardFormExpectationUpdateBridge Alg Hilb NormalPositive)

/--
The recursive modular scaling engine sends a cone vector to another cone vector.
-/
@[rep_depth operator]
theorem composeModularScale_coneVector_mem
    (n : Nat) (ω : NormalPositive)
    (hω : B.standardForm.isNormalPositive ω) :
    B.composeModularScale n (B.standardForm.coneVector ω) ∈ B.standardForm.cone := by
  exact
    B.composeModularScale_mem n (B.standardForm.coneVector ω)
      (B.standardForm.coneVector_mem ω hω)

/--
The updated normal positive functional is still represented by the scaled cone
vector.
-/
@[rep_depth operator]
theorem eval_update_eq_vector_readout
    (n : Nat) (ω : NormalPositive) (A : Alg)
    (hω : B.standardForm.isNormalPositive ω) :
    B.standardForm.eval (B.updateFunctional n ω) A =
      B.standardForm.innerReadout
        (B.standardForm.act A (B.composeModularScale n (B.standardForm.coneVector ω)))
        (B.composeModularScale n (B.standardForm.coneVector ω)) := by
  simpa [B.coneVector_composeModularScale n ω] using
    B.standardForm.eval_eq_vector_readout_of_normal
      (B.updateFunctional n ω) A (B.updateFunctional_mem n ω hω)

/--
The updated cone vector is fixed by Tomita reflection.
-/
@[rep_depth operator]
theorem J_fixes_scaled_coneVector
    (n : Nat) (ω : NormalPositive)
    (hω : B.standardForm.isNormalPositive ω) :
    B.standardForm.J (B.composeModularScale n (B.standardForm.coneVector ω)) =
      B.composeModularScale n (B.standardForm.coneVector ω) := by
  apply B.standardForm.J_fixes_cone
  exact B.composeModularScale_coneVector_mem n ω hω

end StandardFormExpectationUpdateBridge

end InfoGeometry.Canonical.StandardFormExpectationUpdate
