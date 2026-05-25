import Mathlib.Tactic
import InfoGeometry.Algebra.NilpotentNonunit

/-!
# InfoGeometry.Algebra.HypercomplexTriad

Concrete algebraic lemmas for the three real two-dimensional
hypercomplex signatures:

* elliptic:   `x^2 = -1`;
* hyperbolic: `x^2 =  1`;
* parabolic:  `x^2 =  0`.

The first two give invertible elements.  A nonzero square-zero element cannot
be a unit.  This is the algebraic reason nilpotent/dual-number directions
appear as boundary/Fock/BRST data rather than as global symmetry-group
operators.
-/

namespace InfoGeometry.Algebra

/--
An element with square `1` is a unit.

This covers the hyperbolic/split-complex involutive case.
-/
theorem isUnit_of_sq_eq_one
    {R : Type*} [Monoid R]
    (x : R) (hx : x * x = 1) :
    IsUnit x := by
  exact ⟨Units.mk x x hx hx, rfl⟩

/--
An element with square `-1` is a unit.

This covers the elliptic/complex case.
-/
theorem isUnit_of_sq_eq_neg_one
    {R : Type*} [Ring R]
    (x : R) (hx : x * x = -1) :
    IsUnit x := by
  refine ⟨Units.mk x (-x) ?_ ?_, rfl⟩
  · rw [mul_neg, hx]
    simp
  · rw [neg_mul, hx]
    simp

/--
If a unit has square zero, then it is zero.

This is the core obstruction behind nilpotent/parabolic directions:
a square-zero element cannot be an invertible symmetry unless it is zero.
-/
theorem eq_zero_of_isUnit_of_sq_eq_zero
    {R : Type*} [MonoidWithZero R]
    {x : R}
    (hxUnit : IsUnit x)
    (hxSq : x * x = 0) :
    x = 0 := by
  rcases hxUnit with ⟨u, rfl⟩
  calc
    (u : R) = (u : R) * 1 := by
      simp
    _ = (u : R) * ((u : R) * ((u⁻¹ : Rˣ) : R)) := by
      simp
    _ = ((u : R) * (u : R)) * ((u⁻¹ : Rˣ) : R) := by
      rw [mul_assoc]
    _ = 0 * ((u⁻¹ : Rˣ) : R) := by
      rw [hxSq]
    _ = 0 := by
      simp

/--
A nonzero square-zero element is not a unit.

This is the parabolic/dual-number exclusion from invertible symmetry groups.
-/
theorem triad_not_isUnit_of_sq_eq_zero_of_ne_zero
    {R : Type*} [MonoidWithZero R]
    {x : R}
    (hxSq : x * x = 0)
    (hxNonzero : x ≠ 0) :
    ¬ IsUnit x := by
  intro hxUnit
  exact hxNonzero (eq_zero_of_isUnit_of_sq_eq_zero hxUnit hxSq)

/--
The three algebraic cases in one theorem statement:

* square `1` gives a unit;
* square `-1` gives a unit;
* nonzero square `0` gives a nonunit.

This packages no new data; it only records the three consequences together.
-/
theorem hypercomplex_triad_unit_status
    {R : Type*} [Ring R]
    (x : R) :
    (x * x = 1 → IsUnit x) ∧
    (x * x = -1 → IsUnit x) ∧
    ((x * x = 0 ∧ x ≠ 0) → ¬ IsUnit x) := by
  constructor
  · intro hx
    exact isUnit_of_sq_eq_one x hx
  constructor
  · intro hx
    exact isUnit_of_sq_eq_neg_one x hx
  · intro hx
    exact triad_not_isUnit_of_sq_eq_zero_of_ne_zero hx.1 hx.2

/--
Cross-reference to the generic nilpotent non-unit firewall.

This specializes the reusable algebra lemma from
`InfoGeometry.Algebra.NilpotentNonunit` to the triad context.
-/
theorem triad_not_isUnit_via_generic_firewall
    {R : Type*} [Ring R] [Nontrivial R]
    {x : R}
    (hxSq : x * x = 0)
    (hxNonzero : x ≠ 0) :
    ¬ IsUnit x :=
  not_isUnit_of_sq_eq_zero_of_ne_zero hxSq hxNonzero

end InfoGeometry.Algebra
