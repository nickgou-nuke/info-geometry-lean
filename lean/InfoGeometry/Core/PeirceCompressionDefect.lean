/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

/-!
# Multiplication defects of an idempotent compression

These are associative-ring identities. Star-square factorization supplies
self-adjointness, but no ordered positivity or diffraction interpretation is
asserted. The input operators need not be idempotent.
-/
namespace InfoGeometry.Core.PeirceCompressionDefect

variable {A : Type*} [Ring A]

/-- The exact failure of compression to preserve multiplication. -/
theorem compression_mul_defect (p x y : A) (hp : p * p = p) :
    p * (x * y) * p - (p * x * p) * (p * y * p) =
      p * x * (1 - p) * y * p := by
  have hmiddle : (p * x * p) * (p * y * p) = p * x * p * y * p := by
    calc
      _ = p * x * (p * p) * y * p := by simp only [mul_assoc]
      _ = _ := by rw [hp]
  rw [hmiddle]
  noncomm_ring

/-- The complementary transfer product is the square-compression defect. -/
theorem compression_square_defect (p x : A) (hp : p * p = p) :
    p * (x * x) * p - (p * x * p) * (p * x * p) =
      (p * x * (1 - p)) * ((1 - p) * x * p) := by
  rw [compression_mul_defect p x x hp]
  have hc : (1 - p) * (1 - p) = 1 - p := by noncomm_ring [hp]
  calc
    _ = p * x * ((1 - p) * (1 - p)) * x * p := by rw [hc]
    _ = _ := by simp only [mul_assoc]

/-- Resolving the complement into idempotents resolves the defect into products.
Pairwise orthogonality is not needed for this identity once the sum is given. -/
theorem compression_defect_sum {I : Type*} [Fintype I]
    (p x y : A) (s : I → A) (hp : p * p = p)
    (hs : ∑ i, s i = 1 - p) (hi : ∀ i, s i * s i = s i) :
    p * (x * y) * p - (p * x * p) * (p * y * p) =
      ∑ i, (p * x * s i) * (s i * y * p) := by
  rw [compression_mul_defect p x y hp, ← hs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = p * x * (s i * s i) * y * p := by rw [hi i]
    _ = _ := by simp only [mul_assoc]

section Star
variable [StarRing A]

/-- Self-adjoint compression and input give a literal star-square factorization. -/
theorem compression_square_defect_star (p x : A) (hp : p * p = p)
    (hps : star p = p) (hxs : star x = x) :
    p * (x * x) * p - (p * x * p) * (p * x * p) =
      (p * x * (1 - p)) * star (p * x * (1 - p)) := by
  rw [compression_square_defect p x hp]
  simp only [star_mul, star_sub, star_one, hps, hxs, mul_assoc]

/-- Self-adjointness is available without an order on the ring. -/
theorem compression_square_defect_selfAdjoint (p x : A) (hp : p * p = p)
    (hps : star p = p) (hxs : star x = x) :
    star (p * (x * x) * p - (p * x * p) * (p * x * p)) =
      p * (x * x) * p - (p * x * p) * (p * x * p) := by
  rw [compression_square_defect_star p x hp hps hxs, star_mul, star_star]

end Star
end InfoGeometry.Core.PeirceCompressionDefect
