/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra

/-- **Definition**: Split-Complex (Hyperbolic) Number over a Ring R.
    z = u + ε v where ε^2 = 1. -/
@[ext]
structure SplitComplex (R : Type*) [Ring R] where
  real : R
  split : R

namespace SplitComplex

variable {R : Type*} [Ring R]

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
  ext <;> dsimp [mul] <;> noncomm_ring

theorem mul_one (x : SplitComplex R) :
    mul x ⟨1, 0⟩ = x := by
  ext <;> dsimp [mul] <;> noncomm_ring

theorem one_mul (x : SplitComplex R) :
    mul ⟨1, 0⟩ x = x := by
  ext <;> dsimp [mul] <;> noncomm_ring

/-- Over any non-commutative ring `[Ring R]`, the split-complex norm is multiplicative
for commuting pairs of split-complex coordinates. -/
theorem normSq_mul_of_commute (x y : SplitComplex R)
    (h1 : Commute x.real y.real) (h2 : Commute x.real y.split)
    (h3 : Commute x.split y.real) (h4 : Commute x.split y.split)
    (hx : Commute x.real x.split) (hy : Commute y.real y.split) :
    normSq (mul x y) = normSq x * normSq y := by
  dsimp [normSq, mul]
  have t1 : (x.real * y.real) * (x.real * y.real) = (x.real * x.real) * (y.real * y.real) := by
    calc (x.real * y.real) * (x.real * y.real)
      _ = x.real * (y.real * x.real) * y.real := by simp only [_root_.mul_assoc]
      _ = x.real * (x.real * y.real) * y.real := by rw [h1.symm.eq]
      _ = (x.real * x.real) * (y.real * y.real) := by simp only [_root_.mul_assoc]
  have t2 : (x.real * y.real) * (x.split * y.split) = (x.real * x.split) * (y.real * y.split) := by
    calc (x.real * y.real) * (x.split * y.split)
      _ = x.real * (y.real * x.split) * y.split := by simp only [_root_.mul_assoc]
      _ = x.real * (x.split * y.real) * y.split := by rw [h3.symm.eq]
      _ = (x.real * x.split) * (y.real * y.split) := by simp only [_root_.mul_assoc]
  have t3 : (x.split * y.split) * (x.real * y.real) = (x.real * x.split) * (y.real * y.split) := by
    calc (x.split * y.split) * (x.real * y.real)
      _ = x.split * (y.split * x.real) * y.real := by simp only [_root_.mul_assoc]
      _ = x.split * (x.real * y.split) * y.real := by rw [h2.symm.eq]
      _ = (x.split * x.real) * (y.split * y.real) := by simp only [_root_.mul_assoc]
      _ = (x.real * x.split) * (y.real * y.split) := by rw [hx.symm.eq, hy.symm.eq]
  have t4 : (x.split * y.split) * (x.split * y.split) = (x.split * x.split) * (y.split * y.split) := by
    calc (x.split * y.split) * (x.split * y.split)
      _ = x.split * (y.split * x.split) * y.split := by simp only [_root_.mul_assoc]
      _ = x.split * (x.split * y.split) * y.split := by rw [h4.symm.eq]
      _ = (x.split * x.split) * (y.split * y.split) := by simp only [_root_.mul_assoc]
  have t5 : (x.real * y.split) * (x.real * y.split) = (x.real * x.real) * (y.split * y.split) := by
    calc (x.real * y.split) * (x.real * y.split)
      _ = x.real * (y.split * x.real) * y.split := by simp only [_root_.mul_assoc]
      _ = x.real * (x.real * y.split) * y.split := by rw [h2.symm.eq]
      _ = (x.real * x.real) * (y.split * y.split) := by simp only [_root_.mul_assoc]
  have t6 : (x.real * y.split) * (x.split * y.real) = (x.real * x.split) * (y.real * y.split) := by
    calc (x.real * y.split) * (x.split * y.real)
      _ = x.real * (y.split * x.split) * y.real := by simp only [_root_.mul_assoc]
      _ = x.real * (x.split * y.split) * y.real := by rw [h4.symm.eq]
      _ = (x.real * x.split) * (y.split * y.real) := by simp only [_root_.mul_assoc]
      _ = (x.real * x.split) * (y.real * y.split) := by rw [hy.symm.eq]
  have t7 : (x.split * y.real) * (x.real * y.split) = (x.real * x.split) * (y.real * y.split) := by
    calc (x.split * y.real) * (x.real * y.split)
      _ = x.split * (y.real * x.real) * y.split := by simp only [_root_.mul_assoc]
      _ = x.split * (x.real * y.real) * y.split := by rw [h1.symm.eq]
      _ = (x.split * x.real) * (y.real * y.split) := by simp only [_root_.mul_assoc]
      _ = (x.real * x.split) * (y.real * y.split) := by rw [hx.symm.eq]
  have t8 : (x.split * y.real) * (x.split * y.real) = (x.split * x.split) * (y.real * y.real) := by
    calc (x.split * y.real) * (x.split * y.real)
      _ = x.split * (y.real * x.split) * y.real := by simp only [_root_.mul_assoc]
      _ = x.split * (x.split * y.real) * y.real := by rw [h3.symm.eq]
      _ = (x.split * x.split) * (y.real * y.real) := by simp only [_root_.mul_assoc]
  simp only [add_mul, mul_add, t1, t2, t3, t4, t5, t6, t7, t8]
  noncomm_ring

theorem normSq_mul {R₀ : Type*} [CommRing R₀] (x y : SplitComplex R₀) :
    normSq (mul x y) = normSq x * normSq y :=
  normSq_mul_of_commute x y
    (Commute.all _ _) (Commute.all _ _) (Commute.all _ _) (Commute.all _ _)
    (Commute.all _ _) (Commute.all _ _)

/-- **Theorem**: Fundamental Split Relation ε^2 = 1. -/
theorem epsilon_squared :
    mul (⟨0, 1⟩ : SplitComplex R) ⟨0, 1⟩ = ⟨1, 0⟩ := by
  dsimp [mul]
  ext <;> noncomm_ring

/-- **Definition**: Bogoliubov Squeezing Action on Mode Coordinates (u, v)
    u' = u c + v s
    v' = u s + v c
    where c^2 - s^2 = 1 (hyperbolic constraint cosh^2 θ - sinh^2 θ = 1). -/
def bogoliubovTransform (c s u v : R) : R × R :=
  (u * c + v * s, u * s + v * c)

/-- **Theorem**: Over any non-commutative ring `[Ring R]`, Bogoliubov squeezing preserves
the hyperbolic interval `(u')² - (v')² = u² - v²` for commuting mode and squeezing parameters. -/
theorem bogoliubov_interval_invariance_of_commute
    (c s u v : R) (h_hyperbolic : c * c - s * s = 1)
    (huc : Commute u c) (hus : Commute u s) (hvc : Commute v c) (hvs : Commute v s)
    (huv : Commute u v) (hcs : Commute c s) :
    let (u', v') := bogoliubovTransform c s u v
    u' * u' - v' * v' = u * u - v * v := by
  have hnorm := normSq_mul_of_commute (⟨u, v⟩ : SplitComplex R) ⟨c, s⟩ huc hus hvc hvs huv hcs
  dsimp [normSq, mul] at hnorm
  dsimp [bogoliubovTransform]
  rw [hnorm, h_hyperbolic, _root_.mul_one]

/-- **Theorem**: Hyperbolic Interval Preservation under Bogoliubov Squeezing.
    (u')^2 - (v')^2 = (u^2 - v^2) (c^2 - s^2). -/
theorem bogoliubov_interval_invariance {R₀ : Type*} [CommRing R₀]
    (c s u v : R₀) (h_hyperbolic : c * c - s * s = 1) :
    let (u', v') := bogoliubovTransform c s u v
    u' * u' - v' * v' = u * u - v * v :=
  bogoliubov_interval_invariance_of_commute c s u v h_hyperbolic
    (Commute.all _ _) (Commute.all _ _) (Commute.all _ _) (Commute.all _ _)
    (Commute.all _ _) (Commute.all _ _)

/-- **Theorem**: CCR normalization in expanded form.
    The hyperbolic constraint is equivalent to the coefficient identity
    `c^2 = 1 + s^2`, which is the normalization used by the transformed
    commutator. -/
theorem bogoliubov_ccr_preservation (c s : R) (h_hyperbolic : c * c - s * s = 1) :
    c * c = 1 + s * s := by
  calc
    c * c = (c * c - s * s) + s * s := by abel
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

/-- **Theorem**: Master Non-Commutative `[Ring R]` Hyperbolic Bogoliubov Squeezing Synthesis. -/
theorem master_hyperbolic_bogoliubov_synthesis_of_commute
    (c s u v : R) (h_hyperbolic : c * c - s * s = 1)
    (huc : Commute u c) (hus : Commute u s) (hvc : Commute v c) (hvs : Commute v s)
    (huv : Commute u v) (hcs : Commute c s) :
    (mul (⟨0, 1⟩ : SplitComplex R) ⟨0, 1⟩ = ⟨1, 0⟩) ∧
    (let (u', v') := bogoliubovTransform c s u v
     u' * u' - v' * v' = u * u - v * v) ∧
    (c * c = 1 + s * s) := ⟨
  epsilon_squared,
  bogoliubov_interval_invariance_of_commute c s u v h_hyperbolic huc hus hvc hvs huv hcs,
  bogoliubov_ccr_preservation c s h_hyperbolic
⟩

open InfoGeometry.Algebra.FiniteSpin in
/-- Non-commutativity witness for the finite spin operator carrier. -/
theorem bogoliubov_spin_carrier_noncomm : J_plus * J_minus ≠ J_minus * J_plus :=
  j_plus_j_minus_ne

end SplitComplex

end InfoGeometry.Algebra.HyperbolicBogoliubovSplitAlgebra
