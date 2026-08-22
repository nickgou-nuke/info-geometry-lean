import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# G₂ Positive Root System and Simple Reflection Invariance

Formalizes the 6 positive roots of the exceptional Lie algebra `𝔤₂`, the simple
reflections `s₁` and `s₂`, and proves the structural root complement invariance:
  `s₁(Φ⁺ \ {α₁}) = Φ⁺ \ {α₁}`
  `s₂(Φ⁺ \ {α₂}) = Φ⁺ \ {α₂}`
with zero sorrys, zero custom axioms, and zero brute-force double-coset searches.
-/

set_option linter.unnecessarySeqFocus false

namespace InfoGeometry.Algebra.Zorn.G2Roots

/-! =========================================================================
    1. Simple Roots, Root System, and Simple Reflections
    ========================================================================= -/

/-- Simple short root `α₁ = (1, 0)`. -/
def alpha1 : ℤ × ℤ := (1, 0)

/-- Simple long root `α₂ = (0, 1)`. -/
def alpha2 : ℤ × ℤ := (0, 1)

/--
The 6 positive roots of `𝔤₂`:
  `Φ⁺ = { α₁, α₂, α₁ + α₂, 2α₁ + α₂, 3α₁ + α₂, 3α₁ + 2α₂ }`
-/
def phiPlus : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2)}

/--
Simple reflection `s₁` (associated with the short root `α₁`):
  `s₁(c₁, c₂) = (c₁, c₂) - ⟨(c₁, c₂), α₁∨⟩ α₁ = (-c₁ + 3c₂, c₂)`
-/
def s1 (v : ℤ × ℤ) : ℤ × ℤ :=
  (-v.1 + 3 * v.2, v.2)

/--
Simple reflection `s₂` (associated with the long root `α₂`):
  `s₂(c₁, c₂) = (c₁, c₂) - ⟨(c₁, c₂), α₂∨⟩ α₂ = (c₁, c₁ - c₂)`
-/
def s2 (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.1, v.1 - v.2)

/-! =========================================================================
    2. Reflection Involutions and Simple Root Annihilation
    ========================================================================= -/

/-- THEOREM: `s₁` is an involution: `s₁ ∘ s₁ = id`. -/
theorem s1_involutive (v : ℤ × ℤ) : s1 (s1 v) = v := by
  ext <;> dsimp [s1] <;> ring

/-- THEOREM: `s₂` is an involution: `s₂ ∘ s₂ = id`. -/
theorem s2_involutive (v : ℤ × ℤ) : s2 (s2 v) = v := by
  ext <;> dsimp [s2] <;> ring

/-- THEOREM: `s₁` maps `α₁` to its negative `-α₁`. -/
theorem s1_alpha1_neg : s1 alpha1 = (-1, 0) := by
  dsimp [s1, alpha1]

/-- THEOREM: `s₂` maps `α₂` to its negative `-α₂`. -/
theorem s2_alpha2_neg : s2 alpha2 = (0, -1) := by
  dsimp [s2, alpha2]

/-! =========================================================================
    3. Root Complement Invariance under s₁
    ========================================================================= -/

/-- The 5-element complement `Φ⁺ \ {α₁}`. -/
def phiPlusWithoutAlpha1 : Finset (ℤ × ℤ) :=
  {(0, 1), (1, 1), (2, 1), (3, 1), (3, 2)}

/-- Pointwise orbit transitions under `s₁`. -/
theorem s1_eval_01 : s1 (0, 1) = (3, 1) := by dsimp [s1]
theorem s1_eval_31 : s1 (3, 1) = (0, 1) := by dsimp [s1]
theorem s1_eval_11 : s1 (1, 1) = (2, 1) := by dsimp [s1]
theorem s1_eval_21 : s1 (2, 1) = (1, 1) := by dsimp [s1]
theorem s1_eval_32 : s1 (3, 2) = (3, 2) := by dsimp [s1]

/--
MAIN THEOREM (s₁ Invariance of Φ⁺ \ {α₁}):
The reflection `s₁` induces a bijective permutation of `Φ⁺ \ {α₁}`.
-/
theorem s1_image_complement :
    Finset.image s1 phiPlusWithoutAlpha1 = phiPlusWithoutAlpha1 := by
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    dsimp [phiPlusWithoutAlpha1] at hu ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [s1_eval_01]; simp
    · rw [s1_eval_11]; simp
    · rw [s1_eval_21]; simp
    · rw [s1_eval_31]; simp
    · rw [s1_eval_32]; simp
  · intro hv
    dsimp [phiPlusWithoutAlpha1] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    refine ⟨s1 v, ?_, s1_involutive v⟩
    dsimp [phiPlusWithoutAlpha1]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [s1_eval_01]; simp
    · rw [s1_eval_11]; simp
    · rw [s1_eval_21]; simp
    · rw [s1_eval_31]; simp
    · rw [s1_eval_32]; simp

/-! =========================================================================
    4. Root Complement Invariance under s₂
    ========================================================================= -/

/-- The 5-element complement `Φ⁺ \ {α₂}`. -/
def phiPlusWithoutAlpha2 : Finset (ℤ × ℤ) :=
  {(1, 0), (1, 1), (2, 1), (3, 1), (3, 2)}

/-- Pointwise orbit transitions under `s₂`. -/
theorem s2_eval_10 : s2 (1, 0) = (1, 1) := by dsimp [s2]
theorem s2_eval_11 : s2 (1, 1) = (1, 0) := by dsimp [s2]
theorem s2_eval_21 : s2 (2, 1) = (2, 1) := by dsimp [s2]
theorem s2_eval_31 : s2 (3, 1) = (3, 2) := by dsimp [s2]
theorem s2_eval_32 : s2 (3, 2) = (3, 1) := by dsimp [s2]

/--
MAIN THEOREM (s₂ Invariance of Φ⁺ \ {α₂}):
The reflection `s₂` induces a bijective permutation of `Φ⁺ \ {α₂}`.
-/
theorem s2_image_complement :
    Finset.image s2 phiPlusWithoutAlpha2 = phiPlusWithoutAlpha2 := by
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    dsimp [phiPlusWithoutAlpha2] at hu ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rw [s2_eval_10]; simp
    · rw [s2_eval_11]; simp
    · rw [s2_eval_21]; simp
    · rw [s2_eval_31]; simp
    · rw [s2_eval_32]; simp
  · intro hv
    dsimp [phiPlusWithoutAlpha2] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    refine ⟨s2 v, ?_, s2_involutive v⟩
    dsimp [phiPlusWithoutAlpha2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · rw [s2_eval_10]; simp
    · rw [s2_eval_11]; simp
    · rw [s2_eval_21]; simp
    · rw [s2_eval_31]; simp
    · rw [s2_eval_32]; simp

end InfoGeometry.Algebra.Zorn.G2Roots
