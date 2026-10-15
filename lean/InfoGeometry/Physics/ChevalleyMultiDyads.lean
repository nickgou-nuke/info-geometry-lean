/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import InfoGeometry.Physics.ChevalleyDyads

/-!
# Multi-Site Chevalley Dyadic Systems in Cl(N,N)

This module formalizes inductive $N$-site tensor systems of Chevalley dyads in an
arbitrary preadditive category `C`.

## Mathematical Structure

1. **Multi-Index**:
   A binary string of length $N$ representing occupation configurations
   $I \in \{0, 1\}^N$, defined inductively:
   - `.nil : MultiIndex 0`
   - `.cons : Bool → MultiIndex n → MultiIndex (n + 1)`

2. **Inductive Dyad Extension**:
   Given a single-site dyad family $e : \text{Bool} \to \text{Bool} \to (X \longrightarrow X)$
   and an $n$-site dyad family $E$, the $(n+1)$-site dyad family is:
   $$\text{extendDyads}(e, E)(b_1 \cdot I, b_2 \cdot J) = e(b_1, b_2) \circ E(I, J)$$

3. **Diagonal Sum (Trace / Resolution of Unity)**:
   The diagonal sum over all $2^N$ multi-indices:
   $$\text{diagonalSum}(N, E) = \sum_{I \in \{0,1\}^N} E(I, I)$$
   satisfies $\text{diagonalSum}(N+1, \text{extendDyads}(e, E)) = \mathbb{1}_X$ whenever
   $e(0,0) + e(1,1) = \mathbb{1}_X$ and $\text{diagonalSum}(N, E) = \mathbb{1}_X$.

4. **Linearity / Distributivity**:
   Composition distributes linearly through `diagonalSum` from both left and right.
-/

namespace InfoGeometry.Physics.ChevalleyMultiDyads

open CategoryTheory
open InfoGeometry.Physics.ChevalleyDyads

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. Inductive Multi-Index -/

/-- A multi-index of length $n$, representing an occupation configuration
$I \in \{\text{false}, \text{true}\}^n$. -/
inductive MultiIndex : ℕ → Type
  | nil : MultiIndex 0
  | cons {n : ℕ} (b : Bool) (I : MultiIndex n) : MultiIndex (n + 1)
  deriving DecidableEq

/-! ### 2. Diagonal Sum of Multi-Dyads -/

/-- The diagonal sum $\sum_{I} E(I, I)$ across all multi-indices of length $n$. -/
def diagonalSum {X : C} :
    (n : ℕ) → (MultiIndex n → MultiIndex n → (X ⟶ X)) → (X ⟶ X)
  | 0, E => E .nil .nil
  | n + 1, E =>
    diagonalSum n (fun I J => E (.cons false I) (.cons false J)) +
    diagonalSum n (fun I J => E (.cons true I) (.cons true J))

/-- Left-composition distributes across the diagonal sum. -/
theorem comp_diagonal_sum {X : C} (c : X ⟶ X) :
    ∀ (n : ℕ) (E : MultiIndex n → MultiIndex n → (X ⟶ X)),
      c ≫ diagonalSum n E = diagonalSum n (fun I J => c ≫ E I J)
  | 0, E => rfl
  | n + 1, E => by
    dsimp [diagonalSum]
    rw [Preadditive.comp_add]
    rw [comp_diagonal_sum c n (fun I J => E (.cons false I) (.cons false J))]
    rw [comp_diagonal_sum c n (fun I J => E (.cons true I) (.cons true J))]

/-- Right-composition distributes across the diagonal sum. -/
theorem diagonal_sum_comp {X : C} (c : X ⟶ X) :
    ∀ (n : ℕ) (E : MultiIndex n → MultiIndex n → (X ⟶ X)),
      diagonalSum n E ≫ c = diagonalSum n (fun I J => E I J ≫ c)
  | 0, E => rfl
  | n + 1, E => by
    dsimp [diagonalSum]
    rw [Preadditive.add_comp]
    rw [diagonal_sum_comp c n (fun I J => E (.cons false I) (.cons false J))]
    rw [diagonal_sum_comp c n (fun I J => E (.cons true I) (.cons true J))]

set_option linter.unusedSectionVars false

/-- Extends an $n$-site dyad family $E$ by a single-site dyad family $e$ to form
an $(n+1)$-site dyad family. -/
def extendDyads {X : C} {n : ℕ}
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X)) :
    MultiIndex (n + 1) → MultiIndex (n + 1) → (X ⟶ X)
  | .cons b1 I, .cons b2 J => e b1 b2 ≫ E I J

@[simp] theorem extendDyads_cons {X : C} {n : ℕ}
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (b1 b2 : Bool) (I J : MultiIndex n) :
    extendDyads e E (.cons b1 I) (.cons b2 J) = e b1 b2 ≫ E I J :=
  rfl

/-- Extending a resolution of unity by a single-site resolution of unity preserves the
resolution of unity on $(n+1)$ sites. -/
theorem extend_dyads_resolution_of_unity {X : C} {n : ℕ}
    (e : Bool → Bool → (X ⟶ X))
    (E : MultiIndex n → MultiIndex n → (X ⟶ X))
    (he : e false false + e true true = 𝟙 X)
    (hE : diagonalSum n E = 𝟙 X) :
    diagonalSum (n + 1) (extendDyads e E) = 𝟙 X := by
  dsimp [diagonalSum, extendDyads]
  rw [← comp_diagonal_sum (e false false) n E]
  rw [← comp_diagonal_sum (e true true) n E]
  rw [← Preadditive.add_comp]
  rw [he, Category.id_comp, hE]

end InfoGeometry.Physics.ChevalleyMultiDyads
