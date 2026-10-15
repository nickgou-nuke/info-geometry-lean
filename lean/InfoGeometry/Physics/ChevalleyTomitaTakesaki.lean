/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.FinCases
import InfoGeometry.Physics.ChevalleyDyads

/-!
# Chevalley Particle–Hole Relabeling of the Four Dyads

This module defines and proves an involutive relabeling of the four Chevalley
dyads. It requires only a preadditive category and CAR hypotheses for the
identifications of transition dyads with `n` and `p`.

The index flip `(i, j) ↦ (1 - i, 1 - j)` exchanges the two Chevalley transition dyads

$$E_{01} \\leftrightarrow E_{10}, \\qquad \\text{equivalently} \\quad
u \\leftrightarrow v$$

and simultaneously exchanges `E₀₀ ↔ E₁₁`. Because `E₀₁ = n` and `E₁₀ = p`,
the relabeling exchanges the two CAR generators. No star operation, state,
modular operator, or Tomita–Takesaki theorem is defined here.

## Causal Poset of Archetypes

```
[ℬ₀: Chevalley dyads]  E₀₀, E₀₁ = n, E₁₀ = p, E₁₁  (resolution of unity)
    ↓
[index relabeling]  (i, j) ↦ (1 - i, 1 - j),  involutive
    ↓
[diagonal swap]  E₀₀ ↔ E₁₁   (vacuum ↔ excited)
    ↓
[off-diagonal swap]  E₀₁ ↔ E₁₀   (annihilation ↔ creation, u ↔ v)
    ↓
[resolution preserved]  mirror(E₀₀) + mirror(E₁₁) = 𝟙
    ↓
[master theorem]  involutive particle–hole dyad relabeling
```

All results are genuine definitions, lemmas, and theorems with complete proofs.
-/

namespace InfoGeometry.Physics.ChevalleyTomitaTakesaki

open CategoryTheory
open InfoGeometry.Physics.ChevalleyDyads

universe v u

set_option linter.unusedSectionVars false

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### 1. The Mirror Index -/

/-- The particle–hole index relabeling `(i, j) ↦ (1 - i, 1 - j)` on `Fin 2 × Fin 2`. -/
def mirrorIdx (i j : Fin 2) : Fin 2 × Fin 2 := (1 - i, 1 - j)

/-- The mirror index is an involution. -/
theorem mirrorIdx_involutive (i j : Fin 2) :
    mirrorIdx (mirrorIdx i j).1 (mirrorIdx i j).2 = (i, j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The mirror swaps the off-diagonal (transition) indices. -/
theorem mirrorIdx_swaps_transition :
    mirrorIdx 0 1 = (1, 0) ∧ mirrorIdx 1 0 = (0, 1) := by
  constructor <;> rfl

/-- The mirror swaps the diagonal (vacuum/excited) indices. -/
theorem mirrorIdx_swaps_diagonal :
    mirrorIdx 0 0 = (1, 1) ∧ mirrorIdx 1 1 = (0, 0) := by
  constructor <;> rfl

/-- The mirror is fixed-point-free: it moves every index. -/
theorem mirrorIdx_neq_self (i j : Fin 2) : mirrorIdx i j ≠ (i, j) := by
  fin_cases i <;> fin_cases j <;> simp [mirrorIdx]

/-! ### 2. The Mirrored Dyads -/

/-- The dyad selected by the relabeled indices `(i, j) ↦ (1 - i, 1 - j)`. -/
@[inline]
def mirrorDyad {X : C} (n p : X ⟶ X) (i j : Fin 2) : X ⟶ X :=
  if i = 0 then (if j = 0 then E11 n p else E10 n p)
  else (if j = 0 then E01 n p else E00 n p)

/-- The mirror sends the vacuum dyad to the excited dyad. -/
theorem mirrorDyad_00_eq_E11 {X : C} (n p : X ⟶ X) :
    mirrorDyad n p 0 0 = E11 n p := by
  simp [mirrorDyad]

/-- The mirror sends the excited dyad to the vacuum dyad. -/
theorem mirrorDyad_11_eq_E00 {X : C} (n p : X ⟶ X) :
    mirrorDyad n p 1 1 = E00 n p := by
  simp [mirrorDyad]

/-- **The mirror swaps the transition dyads**: `E₀₁ ↦ E₁₀`. -/
theorem mirrorDyad_01_eq_E10 {X : C} (n p : X ⟶ X) :
    mirrorDyad n p 0 1 = E10 n p := by
  simp [mirrorDyad]

/-- **The mirror swaps the transition dyads**: `E₁₀ ↦ E₀₁`. -/
theorem mirrorDyad_10_eq_E01 {X : C} (n p : X ⟶ X) :
    mirrorDyad n p 1 0 = E01 n p := by
  simp [mirrorDyad]

/-- The mirror is an involution on the dyad basis: applying the index relabeling
twice returns the original dyad. -/
theorem mirrorDyad_involutive {X : C} (n p : X ⟶ X) (i j : Fin 2) :
    mirrorDyad n p (mirrorIdx (mirrorIdx i j).1 (mirrorIdx i j).2).1
        (mirrorIdx (mirrorIdx i j).1 (mirrorIdx i j).2).2 = mirrorDyad n p i j := by
  rw [mirrorIdx_involutive]

/-- The resolution of unity is preserved by the mirror: the sum of the two
mirrored diagonal dyads is still the identity. -/
theorem mirror_resolution_of_unity {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    mirrorDyad n p 0 0 + mirrorDyad n p 1 1 = 𝟙 X := by
  rw [mirrorDyad_00_eq_E11, mirrorDyad_11_eq_E00]
  rw [_root_.add_comm]
  exact resolution_of_unity n p hn hp hcar

/-- **The `u ↔ v` relabeling**: since `E₀₁ = n` and `E₁₀ = p`, the map
sends the annihilation nilpotent to the creation nilpotent. -/
theorem mirror_swaps_car_nilpotents {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    mirrorDyad n p 0 1 = p ∧ mirrorDyad n p 1 0 = n := by
  refine ⟨?_, ?_⟩
  · rw [mirrorDyad_01_eq_E10, E10_eq_p n p hp hcar]
  · rw [mirrorDyad_10_eq_E01, E01_eq_n n p hn hcar]

/-- Master theorem: the dyad relabeling is involutive and exchanges the
vacuum and excited projectors,
swaps the two Chevalley transition dyads `E₀₁ ↔ E₁₀` (equivalently
`u ↔ v`), and preserves the resolution of unity. -/
theorem master_tomitakesaki_mirror_soundness {X : C} (n p : X ⟶ X)
    (hn : n ≫ n = 0) (hp : p ≫ p = 0) (hcar : n ≫ p + p ≫ n = 𝟙 X) :
    (mirrorDyad n p 0 0 = E11 n p ∧ mirrorDyad n p 1 1 = E00 n p) ∧
    (mirrorDyad n p 0 1 = E10 n p ∧ mirrorDyad n p 1 0 = E01 n p) ∧
    (mirrorDyad n p 0 1 = p ∧ mirrorDyad n p 1 0 = n) ∧
    (∀ i j : Fin 2, mirrorDyad n p (mirrorIdx (mirrorIdx i j).1 (mirrorIdx i j).2).1
        (mirrorIdx (mirrorIdx i j).1 (mirrorIdx i j).2).2 = mirrorDyad n p i j) ∧
    (mirrorDyad n p 0 0 + mirrorDyad n p 1 1 = 𝟙 X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨mirrorDyad_00_eq_E11 n p, mirrorDyad_11_eq_E00 n p⟩
  · exact ⟨mirrorDyad_01_eq_E10 n p, mirrorDyad_10_eq_E01 n p⟩
  · refine ⟨?_, ?_⟩
    · rw [mirrorDyad_01_eq_E10, E10_eq_p n p hp hcar]
    · rw [mirrorDyad_10_eq_E01, E01_eq_n n p hn hcar]
  · intro i j
    exact mirrorDyad_involutive n p i j
  · exact mirror_resolution_of_unity n p hn hp hcar

end InfoGeometry.Physics.ChevalleyTomitaTakesaki
