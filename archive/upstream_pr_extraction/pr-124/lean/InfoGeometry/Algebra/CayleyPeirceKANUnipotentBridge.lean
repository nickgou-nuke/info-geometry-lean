/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.Algebra.CyclotomicOperatorProjectors
import InfoGeometry.Algebra.IwasawaOperatorTwinLoxodromic

/-!
# Cayley-Peirce KAN Unipotent Lifting & Non-Associative Defect Mechanics

This module formalizes the algebraic foundation of:
1. **Peirce Decomposition & Nilpotency of Off-Diagonal Sectors**:
   For any idempotent $E^2 = E$, the off-diagonal elements $N_{10} = E X (1-E)$ and
   $N_{01} = (1-E) X E$ are strictly 2-nilpotent: $N_{10}^2 = 0$ and $N_{01}^2 = 0$.
2. **Unipotent Group Lifting (KAN Radicals)**:
   For any 2-nilpotent element $N^2 = 0$, the exponential truncates to $1 + N$,
   and its exact group inverse is $1 - N$, satisfying $(1 + N)(1 - N) = 1$.
3. **The Cayley Transform on Nilpotents**:
   For $N^2 = 0$, the Cayley transform $\mathcal{C}(N) = (1 - N)(1 + N)^{-1}$ simplifies
   identically to $1 - 2N$.
4. **The Associator Defect**:
   Definition of the associator $[A, B, C] = (A B) C - A (B C)$ in non-associative rings.

All proofs are complete in native Lean 4 + Mathlib with **0 sorrys, 0 admits, and 0 custom axioms**.
-/

namespace InfoGeometry.Algebra.CayleyPeirceKAN

open InfoGeometry.Algebra
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CyclotomicOperatorProjectors

variable {R : Type*} [Ring R]

/-! ### 1. Peirce Decomposition and Strict 2-Nilpotency of Off-Diagonal Sectors -/

/-- An element $E$ is an idempotent if $E^2 = E$. -/
def IsIdempotent (E : R) : Prop := E * E = E

/-- The (1,0)-Peirce projection of $X$ with respect to idempotent $E$. -/
def peirce10 (E X : R) : R := E * X * (1 - E)

/-- The (0,1)-Peirce projection of $X$ with respect to idempotent $E$. -/
def peirce01 (E X : R) : R := (1 - E) * X * E

/-- 🏆 THEOREM 1: The (1,0)-Peirce sector is strictly 2-nilpotent: $(E X (1-E))^2 = 0$. -/
theorem peirce10_sq_zero (E X : R) (hE : IsIdempotent E) :
    peirce10 E X * peirce10 E X = 0 := by
  dsimp [peirce10, IsIdempotent]
  calc
    (E * X * (1 - E)) * (E * X * (1 - E)) =
      E * X * ((1 - E) * E) * X * (1 - E) := by noncomm_ring
    _ = E * X * (E - E * E) * X * (1 - E) := by
      have h1 : (1 - E) * E = E - E * E := by noncomm_ring
      rw [h1]
    _ = E * X * (E - E) * X * (1 - E) := by rw [hE]
    _ = E * X * 0 * X * (1 - E) := by rw [sub_self]
    _ = 0 := by noncomm_ring

/-- 🏆 THEOREM 2: The (0,1)-Peirce sector is strictly 2-nilpotent: $((1-E) X E)^2 = 0$. -/
theorem peirce01_sq_zero (E X : R) (hE : IsIdempotent E) :
    peirce01 E X * peirce01 E X = 0 := by
  dsimp [peirce01, IsIdempotent]
  calc
    ((1 - E) * X * E) * ((1 - E) * X * E) =
      (1 - E) * X * (E * (1 - E)) * X * E := by noncomm_ring
    _ = (1 - E) * X * (E - E * E) * X * E := by
      have h1 : E * (1 - E) = E - E * E := by noncomm_ring
      rw [h1]
    _ = (1 - E) * X * (E - E) * X * E := by rw [hE]
    _ = (1 - E) * X * 0 * X * E := by rw [sub_self]
    _ = 0 := by noncomm_ring

/-! ### 2. Unipotent Group Lifting (KAN Radicals) -/

/-- 🏆 THEOREM 3: The unipotent lift $1 + N$ of a 2-nilpotent element $N$ has exact inverse $1 - N$. -/
theorem unipotent_two_nilpotent_inv (N : R) (hN : N * N = 0) :
    (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  constructor
  · calc
      (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
      _ = 1 - 0 := by rw [hN]
      _ = 1 := sub_zero 1
  · calc
      (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
      _ = 1 - 0 := by rw [hN]
      _ = 1 := sub_zero 1

/-- 🏆 THEOREM 4: Multiplication of unipotents with mutually annihilating products is abelian. -/
theorem unipotent_commuting_nilpotents (N1 N2 : R)
    (h12 : N1 * N2 = 0) (h21 : N2 * N1 = 0) :
    (1 + N1) * (1 + N2) = 1 + N1 + N2 ∧
    (1 + N2) * (1 + N1) = 1 + N1 + N2 := by
  constructor
  · calc
      (1 + N1) * (1 + N2) = 1 + N1 + N2 + N1 * N2 := by noncomm_ring
      _ = 1 + N1 + N2 + 0 := by rw [h12]
      _ = 1 + N1 + N2 := add_zero _
  · calc
      (1 + N2) * (1 + N1) = 1 + N2 + N1 + N2 * N1 := by noncomm_ring
      _ = 1 + N2 + N1 + 0 := by rw [h21]
      _ = 1 + N1 + N2 := by abel

/-! ### 3. Cayley Transform on 2-Nilpotents -/

/-- The polynomial Cayley transform of a 2-nilpotent element $N$. -/
def cayleyNilpotent (N : R) : R := 1 - 2 * N

/-- 🏆 THEOREM 5: The Cayley transform $(1 - N)(1 + N)^{-1}$ for $N^2 = 0$ matches $1 - 2N$. -/
theorem cayley_nilpotent_eq_one_sub_two_mul (N : R) (hN : N * N = 0) :
    (1 - N) * (1 - N) = 1 - 2 * N := by
  calc
    (1 - N) * (1 - N) = 1 - 2 * N + N * N := by noncomm_ring
    _ = 1 - 2 * N + 0 := by rw [hN]
    _ = 1 - 2 * N := add_zero _

/-- 🏆 THEOREM 6: Composition of Cayley transform: $(\mathcal{C}(N))^2 = 1 - 4N$ for $N^2 = 0$. -/
theorem cayley_nilpotent_sq (N : R) (hN : N * N = 0) :
    cayleyNilpotent N * cayleyNilpotent N = 1 - 4 * N := by
  dsimp [cayleyNilpotent]
  calc
    (1 - 2 * N) * (1 - 2 * N) = 1 - 4 * N + 4 * (N * N) := by noncomm_ring
    _ = 1 - 4 * N + 4 * 0 := by rw [hN]
    _ = 1 - 4 * N + 0 := by rw [mul_zero]
    _ = 1 - 4 * N := add_zero _

/-! ### 4. The Associator Defect in Non-Associative Rings -/

section AssociatorDefect

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- The associator of three elements: $[x, y, z] = (x * y) * z - x * (y * z)$. -/
def associatorDefect (x y z : A) : A := (x * y) * z - x * (y * z)

/-- 🏆 THEOREM 7: The associator is additive in the first argument. -/
theorem associatorDefect_add_left (x1 x2 y z : A) :
    associatorDefect (x1 + x2) y z = associatorDefect x1 y z + associatorDefect x2 y z := by
  dsimp [associatorDefect]
  rw [add_mul, add_mul, add_mul]
  abel

/-- 🏆 THEOREM 8: The associator is additive in the middle argument. -/
theorem associatorDefect_add_mid (x y1 y2 z : A) :
    associatorDefect x (y1 + y2) z = associatorDefect x y1 z + associatorDefect x y2 z := by
  dsimp [associatorDefect]
  rw [mul_add, add_mul, add_mul, mul_add]
  abel

/-- 🏆 THEOREM 9: The associator is additive in the right argument. -/
theorem associatorDefect_add_right (x y z1 z2 : A) :
    associatorDefect x y (z1 + z2) = associatorDefect x y z1 + associatorDefect x y z2 := by
  dsimp [associatorDefect]
  rw [mul_add, mul_add, mul_add]
  abel

end AssociatorDefect

end InfoGeometry.Algebra.CayleyPeirceKAN
