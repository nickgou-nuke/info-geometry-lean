import Mathlib.Tactic

/-!
# Nilpotent elements are not units

Small algebraic firewall used by operator/state geometry lanes:

* if `a^2 = 0`, then `a` is not invertible;
* in particular, if `a^2 = 0` and `a ≠ 0`, then `a` is not a unit.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Algebra

/--
If `a^2 = 0` in a monoid-with-zero, then `a` is not a unit.
-/
theorem not_isUnit_of_sq_eq_zero
    {R : Type*} [MonoidWithZero R] [Nontrivial R]
    {a : R}
    (ha : a * a = 0) :
    ¬ IsUnit a := by
  intro hua
  rcases hua with ⟨u, rfl⟩
  have hu0 : ((u : R) * (u : R)) = 0 := ha
  have hmul : (↑u⁻¹ : R) * ((u : R) * (u : R)) = (↑u⁻¹ : R) * 0 := by
    simpa [hu0]
  have hval0 : (u : R) = 0 := by
    simpa [mul_assoc] using hmul
  exact Units.ne_zero u hval0

/--
If `a^2 = 0` and `a ≠ 0`, then `a` is not a unit.
-/
theorem not_isUnit_of_sq_eq_zero_of_ne_zero
    {R : Type*} [MonoidWithZero R] [Nontrivial R]
    {a : R}
    (ha : a * a = 0)
    (_ha0 : a ≠ 0) :
    ¬ IsUnit a :=
  not_isUnit_of_sq_eq_zero ha

end InfoGeometry.Algebra
