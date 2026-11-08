/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel

/-!
# Four-sector directed path and cycle identities

For pairwise orthogonal idempotents, a three-edge directed path has zero
fourth power. Adding a return edge gives a four-cycle whose fourth power,
compressed to the first corner, is the ordered loop product. The theorem is
an algebraic path identity; it does not assert that the loop product is
nonzero or that the ring models a spacetime causal structure.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def directedEdge (P Q A : B) : B := P * A * Q

def openPath4 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ : B) : B :=
  directedEdge P₁ P₂ A₁₂ + directedEdge P₂ P₃ A₂₃ + directedEdge P₃ P₄ A₃₄

def closedCycle4 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁ : B) : B :=
  openPath4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ + directedEdge P₄ P₁ A₄₁

def cycleHolonomy1 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁ : B) : B :=
  directedEdge P₁ P₂ A₁₂ * directedEdge P₂ P₃ A₂₃ *
    directedEdge P₃ P₄ A₃₄ * directedEdge P₄ P₁ A₄₁

def cycleHolonomy2 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁ : B) : B :=
  directedEdge P₂ P₃ A₂₃ * directedEdge P₃ P₄ A₃₄ *
    directedEdge P₄ P₁ A₄₁ * directedEdge P₁ P₂ A₁₂

def cycleHolonomy3 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁ : B) : B :=
  directedEdge P₃ P₄ A₃₄ * directedEdge P₄ P₁ A₄₁ *
    directedEdge P₁ P₂ A₁₂ * directedEdge P₂ P₃ A₂₃

def cycleHolonomy4 (P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁ : B) : B :=
  directedEdge P₄ P₁ A₄₁ * directedEdge P₁ P₂ A₁₂ *
    directedEdge P₂ P₃ A₂₃ * directedEdge P₃ P₄ A₃₄

lemma idempotent_left_assoc {P : B} (hP : P * P = P) (X : B) :
    P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

lemma orthogonal_left_assoc {P Q : B} (hPQ : P * Q = 0) (X : B) :
    P * (Q * X) = 0 := by
  rw [← mul_assoc, hPQ, zero_mul]

/-- The open path reaches its terminal corner in three steps and then
annihilates. Closing it with the edge `P₄ → P₁` makes the first-corner
compression of the fourth power exactly the ordered four-edge loop. -/
theorem open_path4_and_closed_cycle4_holonomy
    {P₁ P₂ P₃ P₄ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h3 : P₃ * P₃ = P₃) (h4 : P₄ * P₄ = P₄)
    (h12 : P₁ * P₂ = 0) (h13 : P₁ * P₃ = 0) (h14 : P₁ * P₄ = 0)
    (h21 : P₂ * P₁ = 0) (h23 : P₂ * P₃ = 0) (h24 : P₂ * P₄ = 0)
    (h31 : P₃ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h34 : P₃ * P₄ = 0)
    (h41 : P₄ * P₁ = 0) (h42 : P₄ * P₂ = 0) (h43 : P₄ * P₃ = 0)
    (A₁₂ A₂₃ A₃₄ A₄₁ : B) :
    let T := openPath4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄
    let C := closedCycle4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    T * T * T = P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₄ * P₄ ∧
    T * T * T * T = 0 ∧
    P₁ * (C * C * C * C) * P₁ =
      P₁ * A₁₂ * P₂ * A₂₃ * P₃ * A₃₄ * P₄ * A₄₁ * P₁ := by
  intro T C
  refine ⟨?_, ?_, ?_⟩ <;>
    dsimp [T, C, closedCycle4, openPath4, directedEdge] <;>
    simp only [add_mul, mul_add, mul_assoc,
      h1, idempotent_left_assoc h1, h2, idempotent_left_assoc h2,
      h3, idempotent_left_assoc h3, h4, idempotent_left_assoc h4,
      h12, orthogonal_left_assoc h12, h13, orthogonal_left_assoc h13,
      h14, orthogonal_left_assoc h14, h21, orthogonal_left_assoc h21,
      h23, orthogonal_left_assoc h23, h24, orthogonal_left_assoc h24,
      h31, orthogonal_left_assoc h31, h32, orthogonal_left_assoc h32,
      h34, orthogonal_left_assoc h34, h41, orthogonal_left_assoc h41,
      h42, orthogonal_left_assoc h42, h43, orthogonal_left_assoc h43,
      mul_zero, zero_mul] <;>
    abel

/-- The fourth power of the four-edge cycle splits into its four corner
holonomies. Consecutive edge transport intertwines the corresponding corner
holonomies; the displayed orthogonality is one representative of their
pairwise corner support. -/
theorem closed_cycle4_sector_decomposition_and_transport
    {P₁ P₂ P₃ P₄ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h3 : P₃ * P₃ = P₃) (h4 : P₄ * P₄ = P₄)
    (h12 : P₁ * P₂ = 0) (h13 : P₁ * P₃ = 0) (h14 : P₁ * P₄ = 0)
    (h21 : P₂ * P₁ = 0) (h23 : P₂ * P₃ = 0) (h24 : P₂ * P₄ = 0)
    (h31 : P₃ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h34 : P₃ * P₄ = 0)
    (h41 : P₄ * P₁ = 0) (h42 : P₄ * P₂ = 0) (h43 : P₄ * P₃ = 0)
    (A₁₂ A₂₃ A₃₄ A₄₁ : B) :
    let T := closedCycle4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let E₁₂ := directedEdge P₁ P₂ A₁₂
    let E₂₃ := directedEdge P₂ P₃ A₂₃
    let E₃₄ := directedEdge P₃ P₄ A₃₄
    let E₄₁ := directedEdge P₄ P₁ A₄₁
    let H₁ := cycleHolonomy1 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₂ := cycleHolonomy2 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₃ := cycleHolonomy3 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₄ := cycleHolonomy4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    T * T * T * T = H₁ + H₂ + H₃ + H₄ ∧
    H₁ * H₂ = 0 ∧
    H₁ * E₁₂ = E₁₂ * H₂ ∧
    H₂ * E₂₃ = E₂₃ * H₃ ∧
    H₃ * E₃₄ = E₃₄ * H₄ ∧
    H₄ * E₄₁ = E₄₁ * H₁ := by
  intro T E₁₂ E₂₃ E₃₄ E₄₁ H₁ H₂ H₃ H₄
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [T, E₁₂, E₂₃, E₃₄, E₄₁, H₁, H₂, H₃, H₄,
      closedCycle4, openPath4, directedEdge, cycleHolonomy1, cycleHolonomy2,
      cycleHolonomy3, cycleHolonomy4] <;>
    simp only [add_mul, mul_add, mul_assoc,
      h1, idempotent_left_assoc h1, h2, idempotent_left_assoc h2,
      h3, idempotent_left_assoc h3, h4, idempotent_left_assoc h4,
      h12, orthogonal_left_assoc h12, h13, orthogonal_left_assoc h13,
      h14, orthogonal_left_assoc h14, h21, orthogonal_left_assoc h21,
      h23, orthogonal_left_assoc h23, h24, orthogonal_left_assoc h24,
      h31, orthogonal_left_assoc h31, h32, orthogonal_left_assoc h32,
      h34, orthogonal_left_assoc h34, h41, orthogonal_left_assoc h41,
      h42, orthogonal_left_assoc h42, h43, orthogonal_left_assoc h43,
      mul_zero, zero_mul] <;>
    abel

/-- Distinct corner holonomies have zero products in both orders.  This
strengthens the representative orthogonality included in
`closed_cycle4_sector_decomposition_and_transport` to all six pairs. -/
theorem closed_cycle4_holonomies_pairwise_orthogonal
    {P₁ P₂ P₃ P₄ : B}
    (h12 : P₁ * P₂ = 0) (h13 : P₁ * P₃ = 0) (h14 : P₁ * P₄ = 0)
    (h21 : P₂ * P₁ = 0) (h23 : P₂ * P₃ = 0) (h24 : P₂ * P₄ = 0)
    (h31 : P₃ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h34 : P₃ * P₄ = 0)
    (h41 : P₄ * P₁ = 0) (h42 : P₄ * P₂ = 0) (h43 : P₄ * P₃ = 0)
    (A₁₂ A₂₃ A₃₄ A₄₁ : B) :
    let H₁ := cycleHolonomy1 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₂ := cycleHolonomy2 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₃ := cycleHolonomy3 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₄ := cycleHolonomy4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    H₁ * H₂ = 0 ∧ H₂ * H₁ = 0 ∧
    H₁ * H₃ = 0 ∧ H₃ * H₁ = 0 ∧
    H₁ * H₄ = 0 ∧ H₄ * H₁ = 0 ∧
    H₂ * H₃ = 0 ∧ H₃ * H₂ = 0 ∧
    H₂ * H₄ = 0 ∧ H₄ * H₂ = 0 ∧
    H₃ * H₄ = 0 ∧ H₄ * H₃ = 0 := by
  intro H₁ H₂ H₃ H₄
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [H₁, H₂, H₃, H₄, cycleHolonomy1, cycleHolonomy2,
      cycleHolonomy3, cycleHolonomy4, directedEdge] <;>
    simp only [mul_assoc,
      h12, orthogonal_left_assoc h12, h13, orthogonal_left_assoc h13,
      h14, orthogonal_left_assoc h14, h21, orthogonal_left_assoc h21,
      h23, orthogonal_left_assoc h23, h24, orthogonal_left_assoc h24,
      h31, orthogonal_left_assoc h31, h32, orthogonal_left_assoc h32,
      h34, orthogonal_left_assoc h34, h41, orthogonal_left_assoc h41,
      h42, orthogonal_left_assoc h42, h43, orthogonal_left_assoc h43,
      mul_zero, zero_mul]

/-- Every positive number of laps of the fourth-power cycle operator is the
sum of the corresponding powers of its four supported corner holonomies.
The positive exponent matters: at exponent zero the right side has four unit
terms. -/
theorem closed_cycle4_positive_laps_decompose
    {P₁ P₂ P₃ P₄ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h3 : P₃ * P₃ = P₃) (h4 : P₄ * P₄ = P₄)
    (h12 : P₁ * P₂ = 0) (h13 : P₁ * P₃ = 0) (h14 : P₁ * P₄ = 0)
    (h21 : P₂ * P₁ = 0) (h23 : P₂ * P₃ = 0) (h24 : P₂ * P₄ = 0)
    (h31 : P₃ * P₁ = 0) (h32 : P₃ * P₂ = 0) (h34 : P₃ * P₄ = 0)
    (h41 : P₄ * P₁ = 0) (h42 : P₄ * P₂ = 0) (h43 : P₄ * P₃ = 0)
    (A₁₂ A₂₃ A₃₄ A₄₁ : B) (n : ℕ) :
    let T := closedCycle4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₁ := cycleHolonomy1 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₂ := cycleHolonomy2 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₃ := cycleHolonomy3 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    let H₄ := cycleHolonomy4 P₁ P₂ P₃ P₄ A₁₂ A₂₃ A₃₄ A₄₁
    (T * T * T * T) ^ (n + 1) = H₁ ^ (n + 1) + H₂ ^ (n + 1) +
      H₃ ^ (n + 1) + H₄ ^ (n + 1) := by
  intro T H₁ H₂ H₃ H₄
  have hdecomp := closed_cycle4_sector_decomposition_and_transport
    h1 h2 h3 h4 h12 h13 h14 h21 h23 h24 h31 h32 h34 h41 h42 h43
    A₁₂ A₂₃ A₃₄ A₄₁
  have horth := closed_cycle4_holonomies_pairwise_orthogonal
    h12 h13 h14 h21 h23 h24 h31 h32 h34 h41 h42 h43
    A₁₂ A₂₃ A₃₄ A₄₁
  rcases hdecomp with ⟨hT, _, _, _, _, _⟩
  rcases horth with ⟨h12', h21', h13', h31', h14', h41',
    h23', h32', h24', h42', h34', h43'⟩
  dsimp [T, H₁, H₂, H₃, H₄] at *
  have hpow : ∀ {X Y : B}, X * Y = 0 → ∀ n : ℕ, X ^ (n + 1) * Y = 0 := by
    intro X Y hXY n
    induction n with
    | zero => simpa using hXY
    | succ n ih =>
        rw [pow_succ, mul_assoc, hXY, mul_zero]
  induction n with
  | zero =>
      simpa using hT
  | succ n ih =>
      have h12pow := hpow h12' n
      have h13pow := hpow h13' n
      have h14pow := hpow h14' n
      have h21pow := hpow h21' n
      have h23pow := hpow h23' n
      have h24pow := hpow h24' n
      have h31pow := hpow h31' n
      have h32pow := hpow h32' n
      have h34pow := hpow h34' n
      have h41pow := hpow h41' n
      have h42pow := hpow h42' n
      have h43pow := hpow h43' n
      rw [pow_succ, ih, hT]
      simp only [add_mul, mul_add, h12pow, h13pow, h14pow, h21pow,
        h23pow, h24pow, h31pow, h32pow, h34pow, h41pow, h42pow,
        h43pow, mul_zero, zero_mul]
      rw [← pow_succ, ← pow_succ, ← pow_succ, ← pow_succ]
      simp only [zero_add, add_zero]

end InfoGeometry.OperatorAlgebra.PeirceSpine
