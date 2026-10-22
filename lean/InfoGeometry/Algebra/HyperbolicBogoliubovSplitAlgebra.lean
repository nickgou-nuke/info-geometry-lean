/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra

/-- **Definition**: Split-Complex (Hyperbolic) Number over a Commutative Ring R.
    z = u + ε v where ε^2 = 1. -/
@[ext]
structure SplitComplex (R : Type*) [CommRing R] where
  real : R
  split : R

namespace SplitComplex

variable {R : Type*} [CommRing R]

instance : Inhabited (SplitComplex R) :=
  ⟨⟨0, 0⟩⟩

def add (z w : SplitComplex R) : SplitComplex R :=
  ⟨z.real + w.real, z.split + w.split⟩

def mul (z w : SplitComplex R) : SplitComplex R :=
  ⟨z.real * w.real + z.split * w.split, z.real * w.split + z.split * w.real⟩

def normSq (z : SplitComplex R) : R :=
  z.real * z.real - z.split * z.split

theorem mul_assoc (x y z : SplitComplex R) :
    mul (mul x y) z = mul x (mul y z) := by
  ext <;> dsimp [mul] <;> ring

theorem mul_one (x : SplitComplex R) :
    mul x ⟨1, 0⟩ = x := by
  ext <;> dsimp [mul] <;> ring

theorem one_mul (x : SplitComplex R) :
    mul ⟨1, 0⟩ x = x := by
  ext <;> dsimp [mul] <;> ring

theorem normSq_mul (x y : SplitComplex R) :
    normSq (mul x y) = normSq x * normSq y := by
  dsimp [normSq, mul]
  ring

/-- **Theorem**: Fundamental Split Relation ε^2 = 1. -/
theorem epsilon_squared :
    mul (⟨0, 1⟩ : SplitComplex R) ⟨0, 1⟩ = ⟨1, 0⟩ := by
  dsimp [mul]
  ext <;> ring

/-- **Definition**: Bogoliubov Squeezing Action on Mode Coordinates (u, v)
    u' = u c + v s
    v' = u s + v c
    where c^2 - s^2 = 1 (hyperbolic constraint cosh^2 θ - sinh^2 θ = 1). -/
def bogoliubovTransform (c s u v : R) : R × R :=
  (u * c + v * s, u * s + v * c)

/-- **Theorem**: Hyperbolic Interval Preservation under Bogoliubov Squeezing.
    (u')^2 - (v')^2 = (u^2 - v^2) (c^2 - s^2). -/
theorem bogoliubov_interval_invariance (c s u v : R) (h_hyperbolic : c * c - s * s = 1) :
    let (u', v') := bogoliubovTransform c s u v
    u' * u' - v' * v' = u * u - v * v := by
  dsimp [bogoliubovTransform]
  calc (u * c + v * s) * (u * c + v * s) - (u * s + v * c) * (u * s + v * c)
    _ = (u * u - v * v) * (c * c - s * s) := by ring
    _ = (u * u - v * v) * 1 := by rw [h_hyperbolic]
    _ = u * u - v * v := by ring

/-- **Theorem**: CCR normalization in expanded form.
    The hyperbolic constraint is equivalent to the coefficient identity
    `c^2 = 1 + s^2`, which is the normalization used by the transformed
    commutator. -/
theorem bogoliubov_ccr_preservation (c s : R) (h_hyperbolic : c * c - s * s = 1) :
    c * c = 1 + s * s := by
  calc
    c * c = (c * c - s * s) + s * s := by ring
    _ = 1 + s * s := by rw [h_hyperbolic]

/-- **Theorem**: Master Hyperbolic Bogoliubov Squeezing Synthesis.
    Unifies:
    1. Fundamental split relation ε^2 = 1.
    2. Hyperbolic metric invariance u'^2 - v'^2 = u^2 - v^2 under Bogoliubov transformation.
    3. The expanded mode normalization c^2 = 1 + s^2. -/
theorem master_hyperbolic_bogoliubov_synthesis
    {R : Type*} [CommRing R] (c s u v : R) (h_hyperbolic : c * c - s * s = 1) :
    (mul (⟨0, 1⟩ : SplitComplex R) ⟨0, 1⟩ = ⟨1, 0⟩) ∧
    (let (u', v') := bogoliubovTransform c s u v
     u' * u' - v' * v' = u * u - v * v) ∧
    (c * c = 1 + s * s) := ⟨
  epsilon_squared,
  bogoliubov_interval_invariance c s u v h_hyperbolic,
  bogoliubov_ccr_preservation c s h_hyperbolic
⟩

end SplitComplex

end InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
