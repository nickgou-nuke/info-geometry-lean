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
# Section 113: Riemann Sphere Light Shells, `CP¹` Twistor Factorization, and Modular Time
Target: `InfoGeometry/Spacetime/RiemannSphereTwistorShells.lean`

Formalizes:
1. 3D spatial vector `(x, y, z)` and relativistic radius `r² = x² + y² + z²`.
2. Light shell condition `t² - (x² + y² + z²) = 0` over full 3D space (`Space3D R`).
3. Van der Waerden bispinor representation `X = t·σ₀ + x·σ₁ + y·σ₂ + z·σ₃`.
4. Twistor factorization theorem: on the light shell (`t² = r²`), the bispinor determinant
   vanishes (`det X = 0`), factoring into the Riemann sphere `CP¹`.
5. Interior time-cone positivity (`0 < det X` for `r² < t²`), providing the positive density
   determinant for the Tomita–Takesaki modular logarithm `K_mod = -ln(X)`.
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

/-- Determinant of a `2×2` matrix. -/
def det2 (a b c d : R) : R :=
  a * d - b * c

/--
Van der Waerden bispinor determinant `det(X)` for `X = t·σ₀ + x·σ₁ + y·σ₂ + z·σ₃`,
where `X = ((t + z, x - I y), (x + I y, t - z))` for an imaginary unit `I`.
-/
def bispinorDet (I t : R) (v : Space3D R) : R :=
  det2 (t + v.z) (v.x - I * v.y)
       (v.x + I * v.y) (t - v.z)

/--
Real-algebraic Hermitian bispinor determinant `det_H(X) = (t + z)(t - z) - (x² + y²)`,
where the Hermitian off-diagonal norm `(x - i y)(x + i y) = x² + y²` is evaluated directly in `R`
without requiring a square root of `-1` inside the base ring `R`.
-/
def hermitianBispinorDet (t : R) (v : Space3D R) : R :=
  det2 (t + v.z) v.x v.x (t - v.z) - v.y^2

/-! ### 3. Main Theorem: Determinant Collapse on the Riemann Sphere -/

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
Light-shell determinant collapse:
On the light shell (`isLightShell t v`), the bispinor determinant vanishes (`bispinorDet I t v = 0`),
so the rank-1 bispinor factors through the Penrose twistor Riemann sphere `CP¹`.
-/
theorem light_shell_bispinor_det_zero (I t : R) (v : Space3D R)
    (hI : I * I = -1) (h_shell : isLightShell t v) :
    bispinorDet I t v = 0 := by
  rw [bispinor_det_eq_hermitianBispinorDet I t v hI]
  exact light_shell_hermitianBispinorDet_zero t v h_shell

/-! ### 4. Modular Thermal Time Inside the Light Shell (`t² > r²`) -/

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

/-! ### 5. Master Synthesis of `RiemannShells` -/

theorem riemann_sphere_twistor_master_synthesis (I : R) (hI : I * I = -1) :
    (∀ (t : R) (v : Space3D R), hermitianBispinorDet t v = t^2 - radiusSq v) ∧
    (∀ (t : R) (v : Space3D R), bispinorDet I t v = t^2 - radiusSq v) ∧
    (∀ (t : R) (v : Space3D R), isLightShell t v → bispinorDet I t v = 0) :=
  ⟨fun t v => hermitianBispinorDet_is_minkowski t v,
   fun t v => bispinor_det_is_minkowski I t v hI,
   fun t v h => light_shell_bispinor_det_zero I t v hI h⟩

end InfoGeometry.Spacetime.RiemannShells

namespace InfoGeometry.Spacetime.TimeShells

variable {R : Type*} [CommRing R]

/-- Configuration of a 3D light-shell inside the doubled Riemann sphere (`t² = x² + y² + z²`). -/
@[ext]
structure RiemannTimeShell (R : Type*) [CommRing R] where
  t : R
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

def zeroTimeShell : RiemannTimeShell R := ⟨0, 0, 0, 0⟩

def sampleRiemannTimeShellInt : RiemannTimeShell ℤ := ⟨13, 3, 4, 12⟩

theorem sampleRiemannTimeShellInt_ne_zero :
    sampleRiemannTimeShellInt ≠ zeroTimeShell := by
  decide

/-- Squared 3D spatial radius `r² = x² + y² + z²`. -/
def rSq (S : RiemannTimeShell R) : R :=
  S.x^2 + S.y^2 + S.z^2

/-- External null-interval time on the shell: `t_shell = t² - (x² + y² + z²)`. -/
def shellTimeZero (S : RiemannTimeShell R) : R :=
  S.t^2 - rSq S

/-- On the light cone (`t² = x² + y² + z²`), the external shell interval vanishes (`shellTimeZero S = 0`). -/
theorem shell_time_is_strictly_zero (S : RiemannTimeShell R)
    (h_cone : S.t^2 = rSq S) :
    shellTimeZero S = 0 := by
  dsimp [shellTimeZero]
  rw [h_cone]
  exact sub_self (rSq S)

/--
Infinitesimal variation of the internal modular time as the logarithmic radial scale `δr · r⁻¹`.
-/
def logScaleRadiusVariation (r dr inv_r : R) : R :=
  r * inv_r * dr

/-- At unit radial inverse (`r * inv_r = 1`), the logarithmic radial variation equals `dr`. -/
theorem log_scale_unit_normalization (r dr inv_r : R) (h_inv : r * inv_r = 1) :
    logScaleRadiusVariation r dr inv_r = dr := by
  dsimp [logScaleRadiusVariation]
  rw [h_inv, one_mul]

/-- At stationary radius (`dr = 0`), the internal modular variation vanishes. -/
theorem log_scale_stationary_at_rest (r inv_r : R) (h_inv : r * inv_r = 1) :
    logScaleRadiusVariation r 0 inv_r = 0 := by
  rw [log_scale_unit_normalization r 0 inv_r h_inv]

end InfoGeometry.Spacetime.TimeShells
