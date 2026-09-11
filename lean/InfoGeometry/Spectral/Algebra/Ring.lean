import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native ring interface

The old reference rebuilds ring structures from a custom additive-group
record. In Lean 4 the `Ring` typeclass is the canonical carrier, so this file
only exposes the small reusable maps used by the old development.
-/

namespace InfoGeometry.Spectral.Algebra.Ring

universe u v

variable {R : Type u} [Ring R]

/-- Right multiplication by a fixed ring element. -/
def rightMul (r : R) : R →ₗ[R] R :=
  LinearMap.mulRight R r

@[simp] theorem rightMul_apply (r x : R) :
    rightMul r x = x * r :=
  rfl

@[simp] theorem rightMul_one (x : R) :
    rightMul 1 x = x := by
  simp [rightMul]

@[simp] theorem rightMul_mul (r s x : R) :
    rightMul (r * s) x = rightMul s (rightMul r x) := by
  simp [rightMul, mul_assoc]

/-! Graded rings -/

/-- A graded ring-like multiplication on additively commutative components. -/
structure GradedRing (G : Type v) [Monoid G] where
  carrier : G → Type u
  addCommGroup : ∀ g, AddCommGroup (carrier g)
  mul : ∀ {g h : G}, carrier g → carrier h → carrier (g * h)
  one : carrier 1
  mul_one : ∀ {g : G} (x : carrier g), HEq (mul x one) x
  one_mul : ∀ {g : G} (x : carrier g), HEq (mul one x) x
  mul_assoc : ∀ {g h k : G} (x : carrier g) (y : carrier h) (z : carrier k),
    HEq (mul (mul x y) z) (mul x (mul y z))
  mul_left_distrib : ∀ {g h : G} (x : carrier g)
    (y z : carrier h), mul x (y + z) = mul x y + mul x z
  mul_right_distrib : ∀ {g h : G} (x y : carrier g)
    (z : carrier h), mul (x + y) z = mul x z + mul y z

namespace GradedRing

variable {G : Type v} [Monoid G] (A : GradedRing G)

instance (g : G) : AddCommGroup (A.carrier g) := A.addCommGroup g

theorem mul_one_apply {g : G} (x : A.carrier g) :
    HEq (A.mul x A.one) x := A.mul_one x

theorem one_mul_apply {g : G} (x : A.carrier g) :
    HEq (A.mul A.one x) x := A.one_mul x

theorem mul_assoc_apply {g h k : G}
    (x : A.carrier g) (y : A.carrier h) (z : A.carrier k) :
    HEq (A.mul (A.mul x y) z) (A.mul x (A.mul y z)) := A.mul_assoc x y z

theorem mul_left_distrib_apply {g h : G}
    (x : A.carrier g) (y z : A.carrier h) :
    A.mul x (y + z) = A.mul x y + A.mul x z := A.mul_left_distrib x y z

theorem mul_right_distrib_apply {g h : G}
    (x y : A.carrier g) (z : A.carrier h) :
    A.mul (x + y) z = A.mul x z + A.mul y z := A.mul_right_distrib x y z

end GradedRing

end InfoGeometry.Spectral.Algebra.Ring
