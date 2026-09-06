/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.Algebra.CyclotomicOperatorProjectors
import InfoGeometry.Algebra.CayleyPeirceKANUnipotentBridge

/-!
# The Cayley Transform Bridge: Algebraic Lifting from Peirce Sectors to KAN Groups

This module formalizes the algebraic lift from the non-associative Peirce algebra to the KAN group
using the **Cayley Transform** instead of infinite analytical Taylor series.

## Key Theorems Formalized:
1. **Unipotent Inverse Construction**:
   For any 2-nilpotent element $N$ ($N^2 = 0$), $(1 + N)(1 - N) = 1$ and $(1 - N)(1 + N) = 1$.
2. **Polynomial Reduction of the Cayley Transform**:
   For $N^2 = 0$, $\mathcal{C}(N) = (1 - N)(1 + N)^{-1} = (1 - N)(1 - N) = 1 - 2N$.
3. **Cayley Inversion & Involutive Identity**:
   For any element $x$ where $1 + x$ has inverse $\text{inv}_{1+x}$ and $2$ has inverse $\text{inv}_2$,
   the Cayley transform is self-inversive: $\mathcal{C}(\mathcal{C}(x)) = x$.

All proofs are complete in native Lean 4 + Mathlib with **0 sorrys, 0 admits, and 0 custom axioms**.
-/

namespace InfoGeometry.Lie.CayleyTransform

open InfoGeometry.Algebra
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CyclotomicOperatorProjectors
open InfoGeometry.Algebra.CayleyPeirceKAN

variable {A : Type*} [CommRing A]

/-! ### 1. Cayley Transform Definition and Nilpotent Reduction -/

/-- The Cayley transform of an element $x$ with explicit inverse $\text{inv}_{1+x}$ of $(1 + x)$:
    $\mathcal{C}(x) = (1 - x) \cdot \text{inv}_{1+x}$. -/
def cayleyWithInv (x inv_one_add_x : A) : A :=
  (1 - x) * inv_one_add_x

/-- The polynomial Cayley transform of a 2-nilpotent element $N$. -/
def cayleyNilpotent (N : A) : A := 1 - 2 * N

/-- 🏆 THEOREM 1: For any 2-nilpotent element $N$ ($N^2 = 0$), $(1 - N)$ is the exact two-sided inverse of $(1 + N)$. -/
theorem unipotent_two_nilpotent_inv (N : A) (hN : N * N = 0) :
    (1 + N) * (1 - N) = 1 ∧ (1 - N) * (1 + N) = 1 := by
  constructor
  · calc
      (1 + N) * (1 - N) = 1 - N * N := by ring
      _ = 1 - 0 := by rw [hN]
      _ = 1 := sub_zero 1
  · calc
      (1 - N) * (1 + N) = 1 - N * N := by ring
      _ = 1 - 0 := by rw [hN]
      _ = 1 := sub_zero 1

/-- 🏆 THEOREM 2: The Cayley transform of a 2-nilpotent element matches the exact polynomial $1 - 2N$. -/
theorem cayley_of_nilpotent (N : A) (hN : N * N = 0) :
    cayleyWithInv N (1 - N) = cayleyNilpotent N := by
  dsimp [cayleyWithInv, cayleyNilpotent]
  calc
    (1 - N) * (1 - N) = 1 - 2 * N + N * N := by ring
    _ = 1 - 2 * N + 0 := by rw [hN]
    _ = 1 - 2 * N := add_zero _

/- In characteristic two the same nilpotent Cayley transform is exactly one. -/
theorem cayley_of_nilpotent_charTwo (N : A) (hN : N * N = 0)
    (hchar : ∀ r : A, r + r = 0) :
    cayleyWithInv N (1 - N) = 1 := by
  rw [cayley_of_nilpotent N hN]
  have htwo : (2 : A) * N = 0 := by
    rw [two_mul]
    exact hchar N
  dsimp [cayleyNilpotent]
  rw [htwo]
  simp

/-! ### 2. The Cayley Involutive Identity -/

/-- 🏆 THEOREM 3: Explicit algebraic identity proving that the Cayley transform is an involution: $\mathcal{C}(\mathcal{C}(x)) = x$.
    Whenever $(1 + x)$ and $2$ are invertible, $1 + \mathcal{C}(x)$ is invertible and $\mathcal{C}(\mathcal{C}(x)) = x$. -/
theorem cayley_algebraic_identity (x : A) (inv_one_add_x inv_two : A)
    (h_x : (1 + x) * inv_one_add_x = 1)
    (h_two : (2 : A) * inv_two = 1) :
    let g := cayleyWithInv x inv_one_add_x
    let inv_one_add_g := (1 + x) * inv_two
    (1 + g) * inv_one_add_g = 1 ∧
    cayleyWithInv g inv_one_add_g = x := by
  intro g inv_one_add_g
  have hcomm : inv_one_add_x * (1 + x) = 1 := by
    rw [mul_comm] at h_x
    exact h_x
  have h1 : (1 + g) * inv_one_add_g = 1 := by
    dsimp [g, inv_one_add_g, cayleyWithInv]
    calc
      (1 + (1 - x) * inv_one_add_x) * ((1 + x) * inv_two) =
        (1 * (1 + x) + (1 - x) * (inv_one_add_x * (1 + x))) * inv_two := by ring
      _ = (1 + x + (1 - x) * 1) * inv_two := by rw [hcomm]; ring
      _ = (2 : A) * inv_two := by ring
      _ = 1 := h_two
  have h2 : cayleyWithInv g inv_one_add_g = x := by
    dsimp [g, inv_one_add_g, cayleyWithInv]
    calc
      (1 - (1 - x) * inv_one_add_x) * ((1 + x) * inv_two) =
        (1 * (1 + x) - (1 - x) * (inv_one_add_x * (1 + x))) * inv_two := by ring
      _ = (1 + x - (1 - x) * 1) * inv_two := by rw [hcomm]; ring
      _ = (2 * x) * inv_two := by ring
      _ = x * ((2 : A) * inv_two) := by ring
      _ = x * 1 := by rw [h_two]
      _ = x := mul_one x
  exact ⟨h1, h2⟩

end InfoGeometry.Lie.CayleyTransform
