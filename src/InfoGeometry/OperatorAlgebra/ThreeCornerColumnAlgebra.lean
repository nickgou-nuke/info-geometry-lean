/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Three corners with one unrestricted column

Contract: an arbitrary associative ring, two idempotents `p,l` orthogonal in
both orders, and the complementary third idempotent `r = 1-p-l`.
The operators `p F p + L l + r Q r` form a native subring. Their four missing
off-diagonal corners remain zero under arbitrary finite multiplication.

Dependency order: complementary idempotents → column/corner identities →
product formula → subring → powers and absence of cross-corner transport.
Compression by `1-p` has the stated algebraic formula. No within-corner
triangularity, softmax, nonlinear decoder, empirical ablation, or factual
retrieval assertion is encoded by these ring identities.
-/

namespace InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra

open PeirceSpine (peirce11 P_mul_P')
variable {B : Type*} [Ring B]

def third (p l : B) : B := 1 - p - l

def columnOp (p l F L Q : B) : B :=
  peirce11 p F + L * l + peirce11 (third p l) Q

/-- Add an explicitly permitted first-to-third corner. -/
def retrievalOp (p l F L Q R : B) : B :=
  columnOp p l F L Q + third p l * R * p

private theorem zero_pair {a b : B} (h : a * b = 0) (x : B) :
    a * (b * x) = 0 := by rw [← mul_assoc, h, zero_mul]

macro "three_corner_nf" hp:ident hl:ident hpl:ident hlp:ident : tactic =>
  `(tactic| (
    simp only [retrievalOp, columnOp, third, peirce11, sub_mul, mul_sub, add_mul, mul_add,
      one_mul, mul_one, zero_mul, mul_zero, mul_assoc,
      $hp:ident, $hl:ident, $hpl:ident, $hlp:ident,
      P_mul_P' $hp:ident, P_mul_P' $hl:ident,
      zero_pair $hpl:ident, zero_pair $hlp:ident]
    <;> abel))

variable {p l : B} (hp : p * p = p) (hl : l * l = l)
  (hpl : p * l = 0) (hlp : l * p = 0)

theorem partition : p + l + third p l = 1 := by unfold third; abel

theorem column_decomposition (L : B) :
    L * l = p * L * l + l * L * l + third p l * L * l := by
  simp only [third, sub_mul, one_mul]
  abel

include hp hl hpl hlp

theorem third_idempotent : third p l * third p l = third p l := by
  three_corner_nf hp hl hpl hlp

theorem third_orthogonal :
    p * third p l = 0 ∧ third p l * p = 0 ∧
    l * third p l = 0 ∧ third p l * l = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> three_corner_nf hp hl hpl hlp

theorem column_eq (F L Q : B) : columnOp p l F L Q * l = L * l := by
  three_corner_nf hp hl hpl hlp

theorem forbidden_corners (F L Q : B) :
    l * columnOp p l F L Q * p = 0 ∧
    l * columnOp p l F L Q * third p l = 0 ∧
    p * columnOp p l F L Q * third p l = 0 ∧
    third p l * columnOp p l F L Q * p = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> three_corner_nf hp hl hpl hlp

theorem columnOp_mul (F₁ L₁ Q₁ F₂ L₂ Q₂ : B) :
    columnOp p l F₁ L₁ Q₁ * columnOp p l F₂ L₂ Q₂ =
      columnOp p l (F₁ * p * F₂)
        (p * F₁ * p * L₂ + L₁ * l * L₂ + third p l * Q₁ * third p l * L₂)
        (Q₁ * third p l * Q₂) := by
  three_corner_nf hp hl hpl hlp

theorem compression (F L Q : B) :
    (1 - p) * columnOp p l F L Q * (1 - p) =
      columnOp p l 0 ((1 - p) * L) Q := by
  three_corner_nf hp hl hpl hlp

/-- Algebraic support closure, with no commutativity assumption on coefficients. -/
def supportedSubring : Subring B where
  carrier := {x | ∃ F L Q, x = columnOp p l F L Q}
  zero_mem' := ⟨0, 0, 0, by simp [columnOp, peirce11]⟩
  one_mem' := ⟨1, 1, 1, by three_corner_nf hp hl hpl hlp⟩
  add_mem' := by
    rintro x y ⟨F₁, L₁, Q₁, rfl⟩ ⟨F₂, L₂, Q₂, rfl⟩
    refine ⟨F₁ + F₂, L₁ + L₂, Q₁ + Q₂, ?_⟩
    simp only [columnOp, peirce11, mul_add, add_mul]
    abel
  neg_mem' := by
    rintro x ⟨F, L, Q, rfl⟩
    refine ⟨-F, -L, -Q, ?_⟩
    simp only [columnOp, peirce11, mul_neg, neg_mul]
    abel
  mul_mem' := by
    rintro x y ⟨F₁, L₁, Q₁, rfl⟩ ⟨F₂, L₂, Q₂, rfl⟩
    exact ⟨_, _, _, columnOp_mul hp hl hpl hlp F₁ L₁ Q₁ F₂ L₂ Q₂⟩

/-- Arbitrary heterogeneous stacks preserve all four forbidden corners. -/
theorem list_prod_forbidden_corners (xs : List B)
    (hxs : ∀ x ∈ xs, x ∈ supportedSubring hp hl hpl hlp) :
    l * xs.prod * p = 0 ∧ l * xs.prod * third p l = 0 ∧
    p * xs.prod * third p l = 0 ∧ third p l * xs.prod * p = 0 := by
  obtain ⟨F, L, Q, h⟩ := (supportedSubring hp hl hpl hlp).list_prod_mem hxs
  rw [h]
  exact forbidden_corners hp hl hpl hlp F L Q

/-- No finite repetition creates a path from the first corner to the third. -/
theorem pow_no_cross_transport (F L Q : B) (n : ℕ) :
    third p l * columnOp p l F L Q ^ n * p = 0 := by
  have hx : columnOp p l F L Q ∈ supportedSubring hp hl hpl hlp := ⟨F, L, Q, rfl⟩
  obtain ⟨F', L', Q', h⟩ := (supportedSubring hp hl hpl hlp).pow_mem hx n
  rw [h]
  exact (forbidden_corners hp hl hpl hlp F' L' Q').2.2.2

/-- The additional corner is precisely the first-to-third transport block. -/
theorem retrieval_corner (F L Q R : B) :
    third p l * retrievalOp p l F L Q R * p = third p l * R * p := by
  three_corner_nf hp hl hpl hlp

/-- The extension with directed first-to-third transport is also product-closed. -/
theorem retrievalOp_mul (F₁ L₁ Q₁ R₁ F₂ L₂ Q₂ R₂ : B) :
    retrievalOp p l F₁ L₁ Q₁ R₁ * retrievalOp p l F₂ L₂ Q₂ R₂ =
      retrievalOp p l (F₁ * p * F₂)
        (p * F₁ * p * L₂ + L₁ * l * L₂ + third p l * Q₁ * third p l * L₂ +
          third p l * R₁ * p * L₂)
        (Q₁ * third p l * Q₂) (R₁ * p * F₂ + Q₁ * third p l * R₂) := by
  three_corner_nf hp hl hpl hlp

/-- Compression removes the added transport corner as well as the first corner. -/
theorem retrieval_compression (F L Q R : B) :
    (1 - p) * retrievalOp p l F L Q R * (1 - p) =
      columnOp p l 0 ((1 - p) * L) Q := by
  three_corner_nf hp hl hpl hlp

end InfoGeometry.OperatorAlgebra.ThreeCornerColumnAlgebra
