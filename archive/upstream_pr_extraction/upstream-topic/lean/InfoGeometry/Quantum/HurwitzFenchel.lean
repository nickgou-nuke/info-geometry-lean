import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# InfoGeometry.Quantum.HurwitzFenchel

This file formalizes an exact two-dimensional real-coordinate computation of a
Fenchel-style conjugation identity.  The carrier below is the complex plane;
it is not a general octonionic or non-associative algebra.

In classical convex analysis, the Fenchel conjugate requires a supremum:
$f^*(y) = \sup_x (\langle x, y \rangle - f(x))$

For the coordinate product below, the elementary identity
$\langle x \bullet \overline{y}, 1 \rangle = \langle x, y \rangle$
provides a finite algebraic readout.
-/

namespace InfoGeometry.Quantum

/-- Two real coordinates for the complex-plane model. -/
abbrev ComplexCoordinate := ℝ × ℝ

/-- The unit element $1$ in the Hurwitz space. -/
noncomputable def hurwitz_one : ComplexCoordinate := (1, 0)

/-- The quadratic norm $n(x) = \langle x, x \rangle$. -/
noncomputable def hurwitz_norm (x : ComplexCoordinate) : ℝ :=
  x.1^2 + x.2^2

/-- The Hurwitz conjugation involution $\overline{x}$. -/
noncomputable def hurwitz_conj (x : ComplexCoordinate) : ComplexCoordinate :=
  (x.1, -x.2)

/-- The Hurwitz bilinear inner product. -/
noncomputable def hurwitz_inner (x y : ComplexCoordinate) : ℝ :=
  x.1 * y.1 + x.2 * y.2

/-- The complex-coordinate product. -/
noncomputable def hurwitz_mul (x y : ComplexCoordinate) : ComplexCoordinate :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)

/-- The coordinate identity underlying the finite Fenchel readout. -/
theorem complex_coordinate_fenchel_equality (x y : ComplexCoordinate) :
    hurwitz_inner (hurwitz_mul x (hurwitz_conj y)) hurwitz_one = hurwitz_inner x y := by
  dsimp [hurwitz_inner, hurwitz_mul, hurwitz_conj, hurwitz_one]
  ring

end InfoGeometry.Quantum
