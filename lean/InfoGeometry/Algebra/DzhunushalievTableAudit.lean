/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Audit of the printed multiplication table in arXiv:0805.3221v6

`table1BasisMul` transcribes Table I on PDF page 3, with index `0` denoting
the unit and indices `1` through `7` denoting the paper's basis elements.
The product is extended bilinearly to `Fin 8 → ℤ`. The counterexamples below
concern this complete printed table, not an abstract choice of commutator
orientation. In particular, the table is not an alternative algebra.

Source: Vladimir Dzhunushaliev, *Hidden structures in quantum mechanics*,
arXiv:0805.3221v6 (29 November 2008), Table I and equations (17)–(26).
-/

namespace InfoGeometry.Algebra.DzhunushalievTableAudit

/-- The signed basis product in the printed Table I. -/
def table1BasisMul (i j : Fin 8) : ℤ × Fin 8 :=
  match i.val, j.val with
  | 0, _ => (1, j)
  | _, 0 => (1, i)
  | 1, 1 => (-1, 0) | 1, 2 => (1, 3)  | 1, 3 => (-1, 2)
  | 1, 4 => (-1, 7) | 1, 5 => (1, 6)  | 1, 6 => (-1, 5) | 1, 7 => (1, 4)
  | 2, 1 => (-1, 3) | 2, 2 => (-1, 0) | 2, 3 => (1, 1)
  | 2, 4 => (-1, 6) | 2, 5 => (-1, 7) | 2, 6 => (1, 4)  | 2, 7 => (1, 5)
  | 3, 1 => (1, 2)  | 3, 2 => (-1, 1) | 3, 3 => (-1, 0)
  | 3, 4 => (1, 5)  | 3, 5 => (-1, 4) | 3, 6 => (-1, 7) | 3, 7 => (1, 6)
  | 4, 1 => (1, 7)  | 4, 2 => (1, 6)  | 4, 3 => (-1, 5)
  | 4, 4 => (1, 0)  | 4, 5 => (-1, 3) | 4, 6 => (1, 2)  | 4, 7 => (1, 1)
  | 5, 1 => (-1, 6) | 5, 2 => (1, 7)  | 5, 3 => (1, 4)
  | 5, 4 => (1, 3)  | 5, 5 => (1, 0)  | 5, 6 => (-1, 1) | 5, 7 => (1, 2)
  | 6, 1 => (1, 5)  | 6, 2 => (-1, 4) | 6, 3 => (1, 7)
  | 6, 4 => (-1, 2) | 6, 5 => (1, 1)  | 6, 6 => (1, 0)  | 6, 7 => (1, 3)
  | 7, 1 => (-1, 4) | 7, 2 => (-1, 5) | 7, 3 => (-1, 6)
  | 7, 4 => (-1, 1) | 7, 5 => (-1, 2) | 7, 6 => (-1, 3) | 7, 7 => (1, 0)
  | _, _ => (0, 0)

/-- Basis vectors in the free integer module carrying the printed table. -/
def tableBasis (i : Fin 8) : Fin 8 → ℤ := fun k => if k = i then 1 else 0

/-- Bilinear extension of the printed signed basis products. -/
def tableMul (x y : Fin 8 → ℤ) : Fin 8 → ℤ := fun k =>
  ∑ i : Fin 8, ∑ j : Fin 8,
    if (table1BasisMul i j).2 = k then x i * y j * (table1BasisMul i j).1 else 0

/-- Associator for the printed product, with the parentheses kept explicit. -/
def tableAssociator (x y z : Fin 8 → ℤ) : Fin 8 → ℤ :=
  tableMul (tableMul x y) z - tableMul x (tableMul y z)

set_option maxRecDepth 4096 in
theorem table_associator_125 :
    tableAssociator (tableBasis 1) (tableBasis 2) (tableBasis 5) = 0 := by
  decide

set_option maxRecDepth 4096 in
theorem table_associator_152 :
    tableAssociator (tableBasis 1) (tableBasis 5) (tableBasis 2) =
      (-2 : ℤ) • tableBasis 4 := by
  decide

/-- The displayed alternativity defect is a nonzero vector, not just a
comparison of signed product encodings. -/
theorem table_linearized_right_alternativity_fails :
    tableAssociator (tableBasis 1) (tableBasis 2) (tableBasis 5) +
      tableAssociator (tableBasis 1) (tableBasis 5) (tableBasis 2) ≠ 0 := by
  rw [table_associator_125, table_associator_152, zero_add]
  decide

set_option maxRecDepth 4096 in
theorem table_repeated_argument_defect :
    tableAssociator (tableBasis 1) (tableBasis 2 + tableBasis 5)
      (tableBasis 2 + tableBasis 5) = (-2 : ℤ) • tableBasis 4 := by
  decide

/-- The original right-alternative law itself fails on an explicit sum. -/
theorem table_not_right_alternative :
    ¬ ∀ x y : Fin 8 → ℤ, tableMul (tableMul x y) y = tableMul x (tableMul y y) := by
  intro h
  have hz : tableAssociator (tableBasis 1) (tableBasis 2 + tableBasis 5)
      (tableBasis 2 + tableBasis 5) = 0 := by
    unfold tableAssociator
    rw [h, sub_self]
  rw [table_repeated_argument_defect] at hz
  exact (by decide : (-2 : ℤ) • tableBasis 4 ≠ 0) hz

set_option maxRecDepth 4096 in
theorem table_associator_456 :
    tableAssociator (tableBasis 4) (tableBasis 5) (tableBasis 6) =
      (2 : ℤ) • tableBasis 7 := by
  decide

set_option maxRecDepth 4096 in
/-- Both commutator signs quoted in equations (17) and (18) are indeed
present in the table being audited. -/
theorem table_commutator_signs :
    (tableMul (tableBasis 1) (tableBasis 2) - tableMul (tableBasis 2) (tableBasis 1) =
        (2 : ℤ) • tableBasis 3) ∧
    (tableMul (tableBasis 4) (tableBasis 5) - tableMul (tableBasis 5) (tableBasis 4) =
        (-2 : ℤ) • tableBasis 3) := by
  decide

end InfoGeometry.Algebra.DzhunushalievTableAudit
