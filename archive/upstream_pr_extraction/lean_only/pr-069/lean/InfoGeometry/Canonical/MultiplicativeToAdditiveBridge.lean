import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Commute.Basic

namespace InfoGeometry.Canonical

/-!
# Multiplicative-to-Additive Bridge

Canonical abstraction for the repeated descent pattern

`noncommutative multiplicative object -> commutative multiplicative invariant -> additive potential`.

The key separation is:

1. descent to a commutative multiplicative invariant;
2. additive linearization of that commutative invariant.

We use bundled structures rather than global typeclasses because the same source
type may support several distinct bridges (determinant, scalar cocycle,
Radon-Nikodym character, index character, cyclic pairing, ...).
-/

/--
Exact descent from a multiplicative source to a commutative multiplicative
character.
-/
abbrev ExactAbelianizingBridge (M S : Type*) [Monoid M] [CommMonoid S] :=
  M →* S

namespace ExactAbelianizingBridge

/-- Compatibility accessor for the native multiplicative character. -/
abbrev character {M S : Type*} [Monoid M] [CommMonoid S]
    (B : ExactAbelianizingBridge M S) : M →* S := B

variable {M S : Type*} [Monoid M] [CommMonoid S]

/-- The descended commutative character is multiplicative. -/
theorem map_mul (B : ExactAbelianizingBridge M S) (x y : M) :
    B (x * y) = B x * B y :=
  MonoidHom.map_mul B x y

end ExactAbelianizingBridge

/--
Defective descent from a multiplicative source to a commutative multiplicative
character. The `defect` records the failure of strict multiplicative descent.
-/
structure DefectiveAbelianizingBridge (M S : Type*) [Monoid M] [CommMonoid S] where
  character : M → S
  defect : M → M → S
  map_mul_defect :
    ∀ x y, character (x * y) = defect x y * (character x * character y)

namespace DefectiveAbelianizingBridge

variable {M S : Type*} [Monoid M] [CommMonoid S]

/-- Defective multiplicative descent law. -/
theorem map_mul (B : DefectiveAbelianizingBridge M S) (x y : M) :
    B.character (x * y) = B.defect x y * (B.character x * B.character y) :=
  B.map_mul_defect x y

/-- A unit defect is exactly the ordinary multiplicativity law. -/
theorem map_mul_of_defect_one
    (B : DefectiveAbelianizingBridge M S) (x y : M)
    (hdefect : ∀ x y, B.defect x y = 1) :
    B.character (x * y) = B.character x * B.character y := by
  rw [B.map_mul_defect x y, hdefect x y]
  simp

end DefectiveAbelianizingBridge

namespace ExactAbelianizingBridge

variable {M S : Type*} [Monoid M] [CommMonoid S]

/-- Exact descent yields a defective descent with trivial defect. -/
def toDefective (B : ExactAbelianizingBridge M S) : DefectiveAbelianizingBridge M S where
  character := B
  defect := fun _ _ => 1
  map_mul_defect := by
    intro x y
    simp [ExactAbelianizingBridge.map_mul]

end ExactAbelianizingBridge

/--
Exact additive linearization of a commutative multiplicative invariant.

Typical examples are `log`, `-log`, `trace ∘ log`, or any additive character on
the commutative target.
-/
structure AdditiveLinearization (S A : Type*) [CommMonoid S] [AddCommMonoid A] where
  linearize : S → A
  map_mul : ∀ x y, linearize (x * y) = linearize x + linearize y

namespace AdditiveLinearization

variable {S A : Type*} [CommMonoid S] [AddCommMonoid A]

/-- Additive linearization of a commutative product. -/
theorem map_mul_apply (L : AdditiveLinearization S A) (x y : S) :
    L.linearize (x * y) = L.linearize x + L.linearize y :=
  L.map_mul x y

end AdditiveLinearization

/--
Linearization by functional calculus before full abelianization.

This covers patterns such as the operator logarithm on commuting positive
operators, where linearization happens before descent to a scalar or central
character.
-/
structure FunctionalCalculusLinearization (M A : Type*) [Monoid M] [AddCommMonoid A] where
  linearize : M → A
  map_mul_of_commute : ∀ {x y : M}, Commute x y → linearize (x * y) = linearize x + linearize y

namespace FunctionalCalculusLinearization

variable {M A : Type*} [Monoid M] [AddCommMonoid A]

/-- Functional-calculus linearization on commuting products. -/
theorem map_mul_of_commute_apply (L : FunctionalCalculusLinearization M A) {x y : M}
    (hxy : Commute x y) :
    L.linearize (x * y) = L.linearize x + L.linearize y :=
  L.map_mul_of_commute hxy

end FunctionalCalculusLinearization

/--
Exact multiplicative-to-additive bridge: exact commutative descent followed by
exact additive linearization.
-/
structure ExactMultiplicativeToAdditiveBridge (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] where
  toExactAbelianizingBridge : ExactAbelianizingBridge M S
  toAdditiveLinearization : AdditiveLinearization S A

namespace ExactMultiplicativeToAdditiveBridge

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- The additive invariant attached to the exact bridge. -/
def additiveInvariant (B : ExactMultiplicativeToAdditiveBridge M S A) : M → A :=
  fun x => B.toAdditiveLinearization.linearize (B.toExactAbelianizingBridge x)

/-- Exact descent plus exact linearization yields an additive law upstairs. -/
theorem additiveInvariant_mul (B : ExactMultiplicativeToAdditiveBridge M S A) (x y : M) :
    B.additiveInvariant (x * y) = B.additiveInvariant x + B.additiveInvariant y := by
  unfold additiveInvariant
  rw [ExactAbelianizingBridge.map_mul B.toExactAbelianizingBridge,
    AdditiveLinearization.map_mul_apply B.toAdditiveLinearization]

end ExactMultiplicativeToAdditiveBridge

/--
Defective multiplicative-to-additive bridge: defective descent followed by exact
additive linearization. The additive defect is the linearized descent defect.
-/
structure DefectiveMultiplicativeToAdditiveBridge (M S A : Type*)
    [Monoid M] [CommMonoid S] [AddCommMonoid A] where
  toDefectiveAbelianizingBridge : DefectiveAbelianizingBridge M S
  toAdditiveLinearization : AdditiveLinearization S A

namespace DefectiveMultiplicativeToAdditiveBridge

variable {M S A : Type*} [Monoid M] [CommMonoid S] [AddCommMonoid A]

/-- The additive invariant attached to the defective bridge. -/
def additiveInvariant (B : DefectiveMultiplicativeToAdditiveBridge M S A) : M → A :=
  fun x => B.toAdditiveLinearization.linearize (B.toDefectiveAbelianizingBridge.character x)

/-- Linearized obstruction to exact multiplicative descent. -/
def additiveDefect (B : DefectiveMultiplicativeToAdditiveBridge M S A) : M → M → A :=
  fun x y => B.toAdditiveLinearization.linearize (B.toDefectiveAbelianizingBridge.defect x y)

/--
Defective descent becomes additive after linearization, with the anomaly
recorded as an additive defect term.
-/
theorem additiveInvariant_mul
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) (x y : M) :
    B.additiveInvariant (x * y) =
      B.additiveDefect x y + (B.additiveInvariant x + B.additiveInvariant y) := by
  unfold additiveInvariant additiveDefect
  rw [DefectiveAbelianizingBridge.map_mul B.toDefectiveAbelianizingBridge,
    AdditiveLinearization.map_mul_apply B.toAdditiveLinearization,
    AdditiveLinearization.map_mul_apply B.toAdditiveLinearization]

/-- A defective bridge is exact on any pair whose descent defect is one. -/
theorem additiveInvariant_mul_of_defect_one
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) (x y : M)
    (hdefect : ∀ u v, B.toDefectiveAbelianizingBridge.defect u v = 1) :
    B.additiveInvariant (x * y) =
      B.additiveInvariant x + B.additiveInvariant y := by
  unfold additiveInvariant
  have hmul := DefectiveAbelianizingBridge.map_mul_of_defect_one
    B.toDefectiveAbelianizingBridge x y hdefect
  rw [hmul, AdditiveLinearization.map_mul_apply B.toAdditiveLinearization]

/-!
The exactness condition is local: a single product is additive whenever its
descent defect is the unit.  This is strictly stronger than requiring every
pair in the source to have unit defect.
-/
theorem additiveInvariant_mul_of_defect_one_at
    (B : DefectiveMultiplicativeToAdditiveBridge M S A) (x y : M)
    (hdefect : B.toDefectiveAbelianizingBridge.defect x y = 1) :
    B.additiveInvariant (x * y) =
      B.additiveInvariant x + B.additiveInvariant y := by
  unfold additiveInvariant
  rw [B.toDefectiveAbelianizingBridge.map_mul_defect x y, hdefect]
  simp only [one_mul]
  simpa using
    B.toAdditiveLinearization.map_mul_apply
      (B.toDefectiveAbelianizingBridge.character x)
      (B.toDefectiveAbelianizingBridge.character y)

end DefectiveMultiplicativeToAdditiveBridge

end InfoGeometry.Canonical
