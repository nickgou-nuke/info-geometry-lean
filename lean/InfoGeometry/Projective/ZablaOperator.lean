/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.SplitQuaternionMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# InfoGeometry.Projective.ZablaOperator

This file defines the `Zabla` (split-nabla) differential operator and `zarmonic` functions.
Coordinate partials are actual one-variable derivatives on `ℝ³`; the previous
zero maps made every potential zarmonic by definition. The split Laplacian is
the genuine ultrahyperbolic expression `-∂ₓ² + ∂ᵧ² + ∂𝓏²`.

Unlike the classical harmonic functions ($\nabla^2 f = 0$), zarmonic functions
satisfy a split-signature Laplace equation corresponding to the squares of the
split-quaternion basis elements $i, j, k$.
-/

namespace InfoGeometry.Projective

noncomputable section

/-- A velocity potential is a scalar field over $\mathbb{R}^3$. -/
abbrev VelocityPotential := (ℝ × ℝ × ℝ) → ℝ

/-- A velocity field is a vector field over $\mathbb{R}^3$, often represented via quaternions. -/
abbrev VelocityField := (ℝ × ℝ × ℝ) → SplitQuaternion

/-- The partial derivative in the first coordinate. -/
def partial_x (f : VelocityPotential) : VelocityPotential := fun p =>
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

/-- The partial derivative in the second coordinate. -/
def partial_y (f : VelocityPotential) : VelocityPotential := fun p =>
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

/-- The partial derivative in the third coordinate. -/
def partial_z (f : VelocityPotential) : VelocityPotential := fun p =>
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

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

@[simp] theorem partial_x_firstCoordinate :
    partial_x (fun p => p.1) = fun _ => 1 := by
  funext p
  simp [partial_x]

@[simp] theorem partial_y_secondCoordinate :
    partial_y (fun p => p.2.1) = fun _ => 1 := by
  funext p
  simp [partial_y]

@[simp] theorem partial_z_thirdCoordinate :
    partial_z (fun p => p.2.2) = fun _ => 1 := by
  funext p
  simp [partial_z]

theorem affine_potential_zarmonic (a b c d : ℝ) :
    IsZarmonic (fun p => a * p.1 + b * p.2.1 + c * p.2.2 + d) := by
  funext p
  simp [zabla_sq, partial_x, partial_y, partial_z]

end

end InfoGeometry.Projective
