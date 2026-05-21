import Mathlib.Algebra.Ring.Associator
import Mathlib.Tactic
import InfoGeometry.Canonical.ZornSpinor

/-!
# Split-Octonion Associator Layer

This module formalizes the associator defect layer that sits above the split
`ZornMatrix` carrier.  It does **not** replace the current-algebra Wick
theorem; it only records the triple-bracketing defect and the fact that this
defect vanishes in associative targets.

The supporting `ZornMatrix` carrier is defined in
`InfoGeometry.Canonical.ZornSpinor`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionAssociator

open scoped BigOperators

namespace ZornMatrix

variable {R : Type*} [CommRing R]

/-- The split-octonion associator defect on the Zorn carrier. -/
def associatorDefect (x y z : InfoGeometry.Canonical.ZornMatrix R) :
    InfoGeometry.Canonical.ZornMatrix R :=
  (x * y) * z - x * (y * z)

@[simp]
theorem associatorDefect_apply
    (x y z : InfoGeometry.Canonical.ZornMatrix R) :
    associatorDefect x y z = (x * y) * z - x * (y * z) :=
  rfl

/--
The associator defect vanishes in any associative target.

This is the formal coherence layer: the octonionic obstruction is exactly the
failure of associativity, so it disappears once the target multiplication is
associative.
-/
theorem associatorDefect_zero_of_associative
    {A : Type*} [AddGroup A] [Mul A]
    [Std.Associative (fun a b : A => a * b)]
    (x y z : A) :
    (x * y) * z - x * (y * z) = 0 := by
  simp [Std.Associative.assoc]

/--
Associator defect of a candidate split-octonionic cocycle.

This is the coherence obstruction for triple composition; it is independent of
the current-algebra Wick theorem.
-/
def cocycleAssociatorDefect {Γ : Type*}
    (c : Γ → InfoGeometry.Canonical.ZornMatrix R) (γ η ζ : Γ) :
    InfoGeometry.Canonical.ZornMatrix R :=
  associatorDefect (c γ) (c η) (c ζ)

@[simp]
theorem cocycleAssociatorDefect_apply {Γ : Type*}
    (c : Γ → InfoGeometry.Canonical.ZornMatrix R) (γ η ζ : Γ) :
    cocycleAssociatorDefect c γ η ζ = associatorDefect (c γ) (c η) (c ζ) :=
  rfl

/--
The Zorn associator defect is identically the difference of the two
bracketings.  This keeps the split-octonion layer explicit without pretending
that the carrier is associative.
-/
theorem cocycleAssociatorDefect_def {Γ : Type*}
    (c : Γ → InfoGeometry.Canonical.ZornMatrix R) (γ η ζ : Γ) :
    cocycleAssociatorDefect c γ η ζ =
      (c γ * c η) * c ζ - c γ * (c η * c ζ) := by
  rfl

end ZornMatrix

end InfoGeometry.Canonical.SplitOctonionAssociator

