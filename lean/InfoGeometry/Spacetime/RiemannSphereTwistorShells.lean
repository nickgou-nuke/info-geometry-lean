/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Section 113: Algebraic Light-Shell Determinant Identities

This file proves polynomial identities for scalar coordinates `(t, x, y, z)` and
an explicit parameter `I` satisfying `I * I = -1`. The determinant is represented
by a scalar formula; no matrix-valued spinor, projective `CP¹` map, twistor
factorization, Tomita operator, or modular logarithm is constructed here. The
proved scope is the quadratic identity `det = t² - r²`, its vanishing on the
defined light-shell predicate, and an ordered-ring positivity implication.
-/

namespace InfoGeometry.Spacetime.RiemannShells

variable {R : Type*} [CommRing R]

/-! ### 1. 3D Space and Relativistic Interval -/

@[ext]
structure Space3D (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

def zeroSpace3D : Space3D R := ⟨0, 0, 0⟩

def sampleSpace3DInt : Space3D ℤ := ⟨3, 4, 12⟩

theorem sampleSpace3DInt_ne_zero :
    sampleSpace3DInt ≠ zeroSpace3D := by
  decide

/-- Squared spatial radius `r² = x² + y² + z²`. -/
def radiusSq (v : Space3D R) : R :=
  v.x^2 + v.y^2 + v.z^2

/--
Predicate for a point on the light shell:
The squared time equals the squared 3D spatial radius (`t² = x² + y² + z²`).
-/
def isLightShell (t : R) (v : Space3D R) : Prop :=
  t^2 = radiusSq v

/-! ### 2. Bispinor Representation and Quantum Imaginary Unit -/

/-- Scalar formula for a `2 × 2` determinant. -/
def det2 (a b c d : R) : R :=
  a * d - b * c

/--
Scalar polynomial corresponding to the determinant formula for entries
`((t + z, x - I y), (x + I y, t - z))`. This definition does not construct a
matrix-valued bispinor or representation.
-/
def bispinorDet (I t : R) (v : Space3D R) : R :=
  det2 (t + v.z) (v.x - I * v.y)
       (v.x + I * v.y) (t - v.z)

/-- Scalar polynomial corresponding to `(t + z)(t - z) - (x² + y²)`. -/
def hermitianBispinorDet (t : R) (v : Space3D R) : R :=
  det2 (t + v.z) v.x v.x (t - v.z) - v.y^2

/-! ### 3. Scalar Determinant and Minkowski-Polynomial Identity -/

/--
In any commutative ring `R` containing an element `I` with `I * I = -1`, `bispinorDet I t v`
coincides with the real-algebraic Hermitian determinant `hermitianBispinorDet t v`.
-/
theorem bispinor_det_eq_hermitianBispinorDet (I t : R) (v : Space3D R) (hI : I * I = -1) :
    bispinorDet I t v = hermitianBispinorDet t v := by
  dsimp [bispinorDet, hermitianBispinorDet, det2]
  calc (t + v.z) * (t - v.z) - (v.x - I * v.y) * (v.x + I * v.y)
    _ = (t + v.z) * (t - v.z) - (v.x^2 - (I * I) * v.y^2) := by ring
    _ = (t + v.z) * (t - v.z) - (v.x^2 - (-1) * v.y^2) := by rw [hI]
    _ = (t + v.z) * (t - v.z) - v.x * v.x - v.y^2 := by ring

/--
Real-algebraic Minkowski interval identity:
`hermitianBispinorDet t v` equals the relativistic interval `t² - r²` over any commutative ring `R`.
-/
theorem hermitianBispinorDet_is_minkowski (t : R) (v : Space3D R) :
    hermitianBispinorDet t v = t^2 - radiusSq v := by
  dsimp [hermitianBispinorDet, det2, radiusSq]
  ring

/--
Minkowski interval identity:
Whenever `I * I = -1`, the determinant of the Van der Waerden bispinor equals the relativistic interval `t² - r²`.
-/
theorem bispinor_det_is_minkowski (I t : R) (v : Space3D R) (hI : I * I = -1) :
    bispinorDet I t v = t^2 - radiusSq v := by
  rw [bispinor_det_eq_hermitianBispinorDet I t v hI, hermitianBispinorDet_is_minkowski]

/--
Light-shell Hermitian determinant collapse:
On the light shell (`isLightShell t v`), `hermitianBispinorDet t v = 0`.
-/
theorem light_shell_hermitianBispinorDet_zero (t : R) (v : Space3D R)
    (h_shell : isLightShell t v) :
    hermitianBispinorDet t v = 0 := by
  dsimp [isLightShell] at h_shell
  rw [hermitianBispinorDet_is_minkowski t v, h_shell]
  exact sub_self (radiusSq v)

/--
Scalar light-shell vanishing:
Under `isLightShell t v`, the defined scalar polynomial `bispinorDet I t v` is zero.
This is a determinant identity only; it does not construct a rank-one matrix or a `CP¹` factorization.
-/
theorem light_shell_bispinor_det_zero (I t : R) (v : Space3D R)
    (hI : I * I = -1) (h_shell : isLightShell t v) :
    bispinorDet I t v = 0 := by
  rw [bispinor_det_eq_hermitianBispinorDet I t v hI]
  exact light_shell_hermitianBispinorDet_zero t v h_shell

/-! ### 4. Ordered-Ring Time-Cone Positivity -/

/-- Predicate for the interior of the causal time cone (`r² < t²`). -/
def isInsideTimeCone [LT R] (t : R) (v : Space3D R) : Prop :=
  radiusSq v < t^2

/--
Interior time-cone positivity:
Inside the time cone (`radiusSq v < t²`) over any linearly ordered commutative ring `K` (such as `ℤ` or `ℝ`),
the Hermitian bispinor determinant is strictly positive (`0 < hermitianBispinorDet t v`).
-/
theorem time_cone_det_strictly_positive {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (t : K) (v : Space3D K)
    (h_inside : radiusSq v < t^2) :
    0 < hermitianBispinorDet t v := by
  rw [hermitianBispinorDet_is_minkowski t v]
  exact sub_pos.mpr h_inside

end InfoGeometry.Spacetime.RiemannShells
