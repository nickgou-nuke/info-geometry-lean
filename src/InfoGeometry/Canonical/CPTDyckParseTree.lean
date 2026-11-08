/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Recursive cancellation for matched unipotent parse trees

This module formalizes a monoid-valued, well-bracketed parse tree. Each node
uses an opening gate and its specified two-sided inverse as the matching
closing gate. The resulting cancellation is an algebraic theorem; this file
does not define a Yangian, an RTT algebra, or syntactic distance.
-/

namespace InfoGeometry.Canonical.CPTDyckParseTree

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- A grammar of balanced, recursively nested gate clauses. -/
inductive DyckTree (Label : Type*) where
  | empty : DyckTree Label
  | join : DyckTree Label → DyckTree Label → DyckTree Label
  | enclose : Label → DyckTree Label → DyckTree Label
  deriving Repr

namespace DyckTree

/-- Evaluate a balanced tree using `openGate` at the start of a clause and
`closeGate` at its matching end. The product order follows the displayed
opening-to-closing traversal. -/
def eval {Label : Type*} {B : Type*} [Monoid B]
    (openGate closeGate : Label → B) : DyckTree Label → B
  | .empty => 1
  | .join left right => eval openGate closeGate left * eval openGate closeGate right
  | .enclose label inside =>
      openGate label * eval openGate closeGate inside * closeGate label

/-- Every well-bracketed tree evaluates to the identity when each closing
gate is a two-sided inverse of its corresponding opening gate. -/
theorem eval_eq_one {Label : Type*} {B : Type*} [Monoid B]
    (openGate closeGate : Label → B)
    (hinv : ∀ label,
      openGate label * closeGate label = 1 ∧ closeGate label * openGate label = 1)
    (tree : DyckTree Label) : eval openGate closeGate tree = 1 := by
  induction tree with
  | empty => rfl
  | join left right ihLeft ihRight => simp [eval, ihLeft, ihRight]
  | enclose label inside ih =>
      simp [eval, ih, (hinv label).1]

/-- An arbitrary left and right context around a balanced tree reduces to the
same context with the tree removed. -/
theorem context_cancel {Label : Type*} {B : Type*} [Monoid B]
    (openGate closeGate : Label → B)
    (hinv : ∀ label,
      openGate label * closeGate label = 1 ∧ closeGate label * openGate label = 1)
    (left right : B) (tree : DyckTree Label) :
    left * eval openGate closeGate tree * right = left * right := by
  rw [eval_eq_one openGate closeGate hinv tree]
  simp only [mul_one]

end DyckTree

section Peirce

variable {B : Type*} [Ring B]

/-- The opening and closing gates for an upper Peirce shear. -/
def peirceOpen (P A : B) : B := 1 + conePlus P A

def peirceClose (P A : B) : B := 1 - conePlus P A

/-- A Peirce shear and its subtraction gate are two-sided inverses because
the upper corner is square-zero. -/
theorem peirceOpen_close_inverse {P A : B} (hP : P * P = P) :
    peirceOpen P A * peirceClose P A = 1 ∧
      peirceClose P A * peirceOpen P A = 1 := by
  dsimp [peirceOpen, peirceClose]
  have hN := conePlus_mul_conePlus hP A A
  constructor
  · calc
      (1 + conePlus P A) * (1 - conePlus P A) =
          1 - conePlus P A * conePlus P A := by noncomm_ring
      _ = 1 := by rw [hN]; simp
  · calc
      (1 - conePlus P A) * (1 + conePlus P A) =
          1 - conePlus P A * conePlus P A := by noncomm_ring
      _ = 1 := by rw [hN]; simp

/-- A recursively nested tree of upper Peirce shears cancels exactly. This
specialization proves the finite-ring identity only; it carries no RTT or
Yangian structure. -/
theorem peirce_tree_eval_eq_one {Label : Type*}
    {P : B} (hP : P * P = P) (parameter : Label → B)
    (tree : DyckTree Label) :
    DyckTree.eval (fun label => peirceOpen P (parameter label))
      (fun label => peirceClose P (parameter label)) tree = 1 := by
  apply DyckTree.eval_eq_one
  · intro label
    exact peirceOpen_close_inverse hP

/-- Lower Peirce opening gate `1 + coneMinus P C`. -/
def peirceOpenMinus (P C : B) : B := 1 + coneMinus P C

/-- Lower Peirce closing gate `1 - coneMinus P C`. -/
def peirceCloseMinus (P C : B) : B := 1 - coneMinus P C

/-- **Frontier III (`peirce_crossed_dependency_holonomy_defect`)**:
1. **Well-Nested Dyck Clause Order (`g₁ g₂ g₂⁻¹ g₁⁻¹`)**:
   `(1 + N_+)(1 + N_-)(1 - N_-)(1 - N_+) = 1`,
2. **Crossed-Serial Dependency Order (`g₁ g₂ g₁⁻¹ g₂⁻¹`)**:
   `(1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-) - 1 =
      (N_+ N_- - N_- N_+) - N_+ N_- N_+ + N_- N_+ N_- + N_+ N_- N_+ N_-`,
3. **Reverse Crossed-Serial Order Cancellation**:
   `((1 + N_+)(1 + N_-)(1 - N_+)(1 - N_-)) *
      ((1 + N_-)(1 + N_+)(1 - N_-)(1 - N_+)) = 1`. -/
theorem peirce_crossed_dependency_holonomy_defect
    {P A C : B} (hP : P * P = P) :
    peirceOpen P A * peirceOpenMinus P C *
        peirceCloseMinus P C * peirceClose P A = 1 ∧
    peirceOpen P A * peirceOpenMinus P C *
        peirceClose P A * peirceCloseMinus P C - 1 =
      (conePlus P A * coneMinus P C - coneMinus P C * conePlus P A) -
        conePlus P A * coneMinus P C * conePlus P A +
        coneMinus P C * conePlus P A * coneMinus P C +
        (conePlus P A * coneMinus P C) * (conePlus P A * coneMinus P C) ∧
    (peirceOpen P A * peirceOpenMinus P C *
        peirceClose P A * peirceCloseMinus P C) *
      (peirceOpenMinus P C * peirceOpen P A *
        peirceCloseMinus P C * peirceClose P A) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [peirceOpen, peirceClose, peirceOpenMinus, peirceCloseMinus]
    peirce_nf hP
  · dsimp [peirceOpen, peirceClose, peirceOpenMinus, peirceCloseMinus]
    peirce_nf hP
  · have hPlusLeft :
        (1 - conePlus P A) * (1 + conePlus P A) = 1 := by
      peirce_nf hP
    have hPlusRight :
        (1 + conePlus P A) * (1 - conePlus P A) = 1 := by
      peirce_nf hP
    have hMinusLeft :
        (1 - coneMinus P C) * (1 + coneMinus P C) = 1 := by
      peirce_nf hP
    have hMinusRight :
        (1 + coneMinus P C) * (1 - coneMinus P C) = 1 := by
      peirce_nf hP
    dsimp [peirceOpen, peirceClose, peirceOpenMinus, peirceCloseMinus]
    calc
      (1 + conePlus P A) * (1 + coneMinus P C) *
          (1 - conePlus P A) * (1 - coneMinus P C) *
          ((1 + coneMinus P C) * (1 + conePlus P A) *
            (1 - coneMinus P C) * (1 - conePlus P A)) =
        (1 + conePlus P A) * (1 + coneMinus P C) *
          (1 - conePlus P A) * ((1 - coneMinus P C) * (1 + coneMinus P C)) *
          (1 + conePlus P A) * (1 - coneMinus P C) * (1 - conePlus P A) := by
            noncomm_ring
      _ = (1 + conePlus P A) * (1 + coneMinus P C) *
          (1 - conePlus P A) * (1 + conePlus P A) *
          (1 - coneMinus P C) * (1 - conePlus P A) := by
            rw [hMinusLeft]
            noncomm_ring
      _ = (1 + conePlus P A) * (1 + coneMinus P C) *
          ((1 - conePlus P A) * (1 + conePlus P A)) *
          (1 - coneMinus P C) * (1 - conePlus P A) := by
            noncomm_ring
      _ = (1 + conePlus P A) * (1 + coneMinus P C) *
          (1 - coneMinus P C) * (1 - conePlus P A) := by
            rw [hPlusLeft]
            noncomm_ring
      _ = (1 + conePlus P A) *
          ((1 + coneMinus P C) * (1 - coneMinus P C)) *
          (1 - conePlus P A) := by
            noncomm_ring
      _ = (1 + conePlus P A) * (1 - conePlus P A) := by
            rw [hMinusRight]
            simp
      _ = 1 := hPlusRight

/-- **Frontier III (`peirce_garden_path_mismatch_and_reanalysis`)**:
When an opening gate `1 + N_+(A₁)` is provisionally closed by a mismatched
closing gate `1 - N_+(A₂)`, the garden-path residual is the exact first-order
nilpotent shear `1 + (N_+(A₁) - N_+(A₂))` with square-zero defect
`(N_+(A₁) - N_+(A₂))² = 0`, which is strictly cancelled to `1` by the
reanalysis gate `1 - (N_+(A₁) - N_+(A₂))`. -/
theorem peirce_garden_path_mismatch_and_reanalysis
    {P A₁ A₂ : B} (hP : P * P = P) :
    peirceOpen P A₁ * peirceClose P A₂ =
      1 + (conePlus P A₁ - conePlus P A₂) ∧
    (conePlus P A₁ - conePlus P A₂) * (conePlus P A₁ - conePlus P A₂) = 0 ∧
    peirceOpen P A₁ * peirceClose P A₂ *
      (1 - (conePlus P A₁ - conePlus P A₂)) = 1 := by
  dsimp [peirceOpen, peirceClose]
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

end Peirce

end InfoGeometry.Canonical.CPTDyckParseTree
