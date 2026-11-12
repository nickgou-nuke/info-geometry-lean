/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Ring.Commute
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Faithful matrix amplification and finite trace obstructions

`Matrix.scalar n` is the native ring homomorphism `A →+* Matrix n n A`.
Its coefficients remain in the arbitrary associative ring `A`: the image
need not be commutative or central. Injectivity for a nonempty index type
comes directly from `Matrix.scalar_inj`.

The off-diagonal matrix units below witness both noncommutativity of the
full matrix ring and properness of the scalar image when two indices differ.
The trace section separately assumes commutative coefficients, exactly where
cyclicity of the ordinary matrix trace is used. No topological completion or
operator-algebra classification is asserted.
-/

namespace InfoGeometry.Algebra.MatrixAmplification

universe u v

/-- The associative commutator acts as a derivation without assuming that
the coefficient ring is commutative. -/
theorem commutator_leibniz {A : Type u} [Ring A] (x y z : A) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
  exact (sub_add_sub_cancel (x * (y * z)) (y * (x * z)) (y * (z * x))).symm

section Amplification

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {A : Type u} [Ring A]

/-- Scalar matrix amplification preserves the ordered ring commutator. -/
theorem scalar_commutator (x y : A) :
    ⁅Matrix.scalar n x, Matrix.scalar n y⁆ = Matrix.scalar n ⁅x, y⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul]

/-- A nonempty amplification preserves and reflects vanishing of a commutator. -/
theorem scalar_commutator_eq_zero_iff [Nonempty n] (x y : A) :
    ⁅Matrix.scalar n x, Matrix.scalar n y⁆ = 0 ↔ ⁅x, y⁆ = 0 := by
  rw [scalar_commutator, ← map_zero (Matrix.scalar n), Matrix.scalar_inj]

/-- The same preservation and reflection stated with native `Commute`. -/
theorem scalar_commute_iff [Nonempty n] (x y : A) :
    Commute (Matrix.scalar n x) (Matrix.scalar n y) ↔ Commute x y := by
  exact commute_map_iff (fun _ _ h => Matrix.scalar_inj.mp h)

/-- The opposite matrix units have a diagonal commutator in every ring. -/
theorem single_commutator (i j : n) :
    ⁅Matrix.single i j (1 : A), Matrix.single j i 1⁆ =
      Matrix.single i i 1 - Matrix.single j j 1 := by
  simp only [Ring.lie_def, Matrix.single_mul_single_same, one_mul]

/-- Two distinct indices exhibit a nonzero commutator over any nontrivial ring. -/
theorem single_commutator_ne_zero [Nontrivial A] {i j : n} (hij : i ≠ j) :
    ⁅Matrix.single i j (1 : A), Matrix.single j i 1⁆ ≠ 0 := by
  intro h
  have hii := congrArg (fun M : Matrix n n A => M i i) h
  exact one_ne_zero (by
    simpa [single_commutator, Matrix.single_apply, hij, hij.symm] using hii)

/-- An off-diagonal unit is not in the scalar amplification image. -/
theorem single_not_mem_range_scalar [Nontrivial A] {i j : n} (hij : i ≠ j) :
    Matrix.single i j (1 : A) ∉ Set.range (Matrix.scalar n : A → Matrix n n A) := by
  rintro ⟨a, ha⟩
  have hij' := congrArg (fun M : Matrix n n A => M i j) ha
  exact zero_ne_one (by simpa [Matrix.scalar_apply, hij] using hij')

/-- The amplification is a proper embedding whenever the index type has two
distinct elements and the coefficient ring is nontrivial. -/
theorem scalar_not_surjective [Nontrivial A] {i j : n} (hij : i ≠ j) :
    ¬ Function.Surjective (Matrix.scalar n : A → Matrix n n A) := by
  intro h
  exact single_not_mem_range_scalar hij (h (Matrix.single i j 1))

end Amplification

section Trace

variable {n : Type v} [Fintype n] [DecidableEq n]
variable {A : Type u} [CommRing A]

/-- Ordinary matrix trace annihilates commutators over commutative coefficients. -/
theorem trace_commutator_zero (x y : Matrix n n A) : Matrix.trace ⁅x, y⁆ = 0 := by
  rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm x y, sub_self]

/-- The exact cardinality condition forced by a scalar commutator.
This remains meaningful in positive characteristic and in rings with zero divisors. -/
theorem card_mul_eq_zero_of_commutator_eq_scalar
    (x y : Matrix n n A) (c : A)
    (h : ⁅x, y⁆ = Matrix.scalar n c) : (Fintype.card n : A) * c = 0 := by
  have htrace := congrArg Matrix.trace h
  rw [trace_commutator_zero] at htrace
  simpa [Matrix.scalar_apply, nsmul_eq_mul] using htrace.symm

/-- A scalar matrix with nonzero trace cannot be a commutator. -/
theorem commutator_ne_scalar_of_card_mul_ne_zero
    (x y : Matrix n n A) (c : A) (hc : (Fintype.card n : A) * c ≠ 0) :
    ⁅x, y⁆ ≠ Matrix.scalar n c := by
  intro h
  exact hc (card_mul_eq_zero_of_commutator_eq_scalar x y c h)

/-- The identity is excluded whenever its trace is nonzero in the coefficient ring. -/
theorem commutator_ne_one_of_card_ne_zero
    (x y : Matrix n n A) (hn : (Fintype.card n : A) ≠ 0) : ⁅x, y⁆ ≠ 1 := by
  intro h
  have htrace := congrArg Matrix.trace h
  rw [trace_commutator_zero, Matrix.trace_one] at htrace
  exact hn htrace.symm

/-- In characteristic zero, every nonempty finite matrix ring has the identity
commutator obstruction. The matrices are arbitrary; no commutation assumption
is imposed. -/
theorem commutator_ne_one [CharZero A] [Nonempty n] (x y : Matrix n n A) :
    ⁅x, y⁆ ≠ 1 := by
  exact commutator_ne_one_of_card_ne_zero x y
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end Trace

end InfoGeometry.Algebra.MatrixAmplification
