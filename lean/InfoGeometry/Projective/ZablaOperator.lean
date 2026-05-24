import InfoGeometry.Projective.SplitQuaternionMatrix

/-!
# InfoGeometry.Projective.ZablaOperator

This file defines the `Zabla` (split-nabla) differential operator and `zarmonic` functions.
These tools use the split-quaternion structure to represent vortex motions such as
those found in the Couette-Taylor system.

Unlike the classical harmonic functions ($\nabla^2 f = 0$), zarmonic functions
satisfy a split-signature Laplace equation corresponding to the squares of the
split-quaternion basis elements $i, j, k$.
-/

namespace InfoGeometry.Projective

/-- A velocity potential is a scalar field over $\mathbb{R}^3$. -/
abbrev VelocityPotential := (ℝ × ℝ × ℝ) → ℝ

/-- A velocity field is a vector field over $\mathbb{R}^3$, often represented via quaternions. -/
abbrev VelocityField := (ℝ × ℝ × ℝ) → SplitQuaternion

/--
Placeholder for the partial derivative with respect to the $x$-coordinate.

-- DEBT_KIND: SORRY
-/
noncomputable def partial_x (f : VelocityPotential) : VelocityPotential := sorry

/--
Placeholder for the partial derivative with respect to the $y$-coordinate.

-- DEBT_KIND: SORRY
-/
noncomputable def partial_y (f : VelocityPotential) : VelocityPotential := sorry

/--
Placeholder for the partial derivative with respect to the $z$-coordinate.

-- DEBT_KIND: SORRY
-/
noncomputable def partial_z (f : VelocityPotential) : VelocityPotential := sorry

/--
The `Zabla` differential operator for split-quaternions.
$\nabla = i \frac{\partial}{\partial x} + j \frac{\partial}{\partial y} + k \frac{\partial}{\partial z}$

When applied to a velocity potential, it yields a velocity field.
-/
noncomputable def zabla (f : VelocityPotential) : VelocityField :=
  fun p => {
    w := 0
    x := partial_x f p
    y := partial_y f p
    z := partial_z f p
  }

/--
The squared `Zabla` operator (split-Laplacian).
Because $i^2 = -1$ while $j^2 = +1$ and $k^2 = +1$, the squared operator is:
$\nabla^2 = -\frac{\partial^2}{\partial x^2} + \frac{\partial^2}{\partial y^2} + \frac{\partial^2}{\partial z^2}$
-/
noncomputable def zabla_sq (f : VelocityPotential) : VelocityPotential :=
  fun p =>
    -(partial_x (partial_x f) p) +
    (partial_y (partial_y f) p) +
    (partial_z (partial_z f) p)

/--
A function is `zarmonic` if it is in the kernel of the squared zabla operator.
$\nabla^2 f = 0$
-/
def IsZarmonic (f : VelocityPotential) : Prop :=
  zabla_sq f = 0

end InfoGeometry.Projective
