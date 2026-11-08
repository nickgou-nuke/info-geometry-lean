/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Archetypes.SouriauKaluzaJanusBimetric
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Souriau–Kaluza–Janus carriers and native Mathlib matrices

The archetype file defines explicit noncommutative 2×2 and 3×3 coordinate
carriers.  This module proves that their coordinate operations (`0`, `1`, `+`,
`-`, `*`, and trace) agree entrywise with the corresponding operations on
`Matrix (Fin n) (Fin n) B`.  The results preserve factor order and hold over
the original arbitrary `[Ring B]` carrier.

## i. Overview

This module represents the existing noncommutative coordinate carriers by
native finite Mathlib matrices.

## ii. Key results

- `toMatrix2_zero`, `toMatrix2_one`, `toMatrix2_add`, `toMatrix2_sub`,
  `toMatrix2_mul`, and `toMatrix2_trace` preserve zero, one, addition,
  subtraction, multiplication, and trace in dimension 2 over arbitrary rings.
- `toMatrix3_zero`, `toMatrix3_one`, `toMatrix3_mul`, and `toMatrix3_trace`
  preserve zero, one, multiplication, and trace in dimension 3 over arbitrary rings.
- `toMatrix2_injective` and `toMatrix3_injective` show both coordinate maps
  distinguish carrier elements.

## iii. Table of contents

1. The 2×2 representation (`toMatrix2`).
2. The 3×3 representation (`toMatrix3`).

## iv. References

- `InfoGeometry.Archetypes.SouriauKaluzaJanusBimetric`.
- Mathlib `Matrix.mul_apply` and `Matrix.trace`.

### Three-Bucket Audit Map (`audit-proof` Policy)

#### BUCKET 1 — Proved Kernel Content
- `toMatrix2_zero`, `toMatrix2_one`, `toMatrix2_add`, `toMatrix2_sub`, `toMatrix2_mul`, `toMatrix2_trace`, `toMatrix2_injective`.
- `toMatrix3_zero`, `toMatrix3_one`, `toMatrix3_mul`, `toMatrix3_trace`, `toMatrix3_injective`.

#### BUCKET 2 — Conditional / Interface Boundaries
- Holds over any associative ring `[Ring B]` (`0` `Classical.choice`).

#### BUCKET 3 — Open / Unformalized
- Infinite-dimensional operator matrix representations.
-/

namespace InfoGeometry.Archetypes.SouriauKaluzaNativeMatrixBridge

open InfoGeometry.Archetypes.SouriauKaluzaJanusBimetric

section CarrierEquivalences

variable {B : Type*} [Ring B]

/-- The 2×2 coordinate map is a genuine equivalence of carriers, with inverse
given by reading the four matrix entries. The operation-preservation lemmas
below establish that this equivalence respects the declared operator
operations; no commutativity of `B` is used. -/
def toMatrix2Equiv : SKJBMat2 B ≃ Matrix (Fin 2) (Fin 2) B where
  toFun := toMatrix2
  invFun M := ⟨M 0 0, M 0 1, M 1 0, M 1 1⟩
  left_inv X := by cases X; rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- The 3×3 coordinate map is an equivalence of carriers; its inverse reads
the nine entries in row-major order. Multiplication and trace are preserved
by `toMatrix3_mul` and `toMatrix3_trace`. -/
def toMatrix3Equiv : SKJBMat3 B ≃ Matrix (Fin 3) (Fin 3) B where
  toFun := toMatrix3
  invFun M := ⟨M 0 0, M 0 1, M 0 2,
    M 1 0, M 1 1, M 1 2,
    M 2 0, M 2 1, M 2 2⟩
  left_inv X := by cases X; rfl
  right_inv M := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl

end CarrierEquivalences

section TwoByTwo

variable {B : Type*} [Ring B]

/-- The 2×2 coordinate embedding sends `0` to the zero matrix. -/
lemma toMatrix2_zero :
    toMatrix2 (0 : SKJBMat2 B) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The 2×2 coordinate embedding sends `1` to the identity matrix. -/
lemma toMatrix2_one :
    toMatrix2 (1 : SKJBMat2 B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The 2×2 coordinate embedding preserves addition entrywise. -/
lemma toMatrix2_add (X Y : SKJBMat2 B) :
    toMatrix2 (X + Y) = toMatrix2 X + toMatrix2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The 2×2 coordinate embedding preserves subtraction entrywise. -/
lemma toMatrix2_sub (X Y : SKJBMat2 B) :
    toMatrix2 (X - Y) = toMatrix2 X - toMatrix2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The custom 2×2 carrier's multiplication agrees entrywise with Mathlib
matrix multiplication over an arbitrary, possibly noncommutative ring. -/
lemma toMatrix2_mul (X Y : SKJBMat2 B) :
    toMatrix2 (X * Y) = toMatrix2 X * toMatrix2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix2, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The Souriau carrier's Hermitian adjoint becomes Mathlib's matrix
conjugate-transpose. This uses the actual `StarRing` coefficient involution. -/
lemma toMatrix2_star [StarRing B] (X : SKJBMat2 B) :
    toMatrix2 (star X) = Matrix.conjTranspose (toMatrix2 X) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix2, Matrix.conjTranspose_apply]

/-- The Mathlib matrix trace of `toMatrix2 X` equals `SKJBTr2 X`. -/
lemma toMatrix2_trace (X : SKJBMat2 B) :
    Matrix.trace (toMatrix2 X) = SKJBTr2 X := by
  simp [toMatrix2, SKJBTr2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

omit [Ring B] in
/-- The coordinate embedding of the 2×2 carrier is injective. -/
lemma toMatrix2_injective :
    Function.Injective (toMatrix2 : SKJBMat2 B → Matrix (Fin 2) (Fin 2) B) := by
  intro X Y h
  cases X
  cases Y
  simp_all [toMatrix2]

end TwoByTwo

section ThreeByThree

variable {B : Type*} [Ring B]

/-- The 3×3 coordinate embedding sends `0` to the zero matrix. -/
lemma toMatrix3_zero :
    toMatrix3 (0 : SKJBMat3 B) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The 3×3 coordinate embedding sends `1` to the identity matrix. -/
lemma toMatrix3_one :
    toMatrix3 (1 : SKJBMat3 B) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The custom 3×3 carrier's multiplication agrees entrywise with Mathlib
matrix multiplication over an arbitrary, possibly noncommutative ring. -/
lemma toMatrix3_mul (X Y : SKJBMat3 B) :
    toMatrix3 (X * Y) = toMatrix3 X * toMatrix3 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix3, Matrix.mul_apply, Fin.sum_univ_succ, add_assoc]

/-- The Mathlib matrix trace of `toMatrix3 X` equals `SKJBTr3 X`. -/
lemma toMatrix3_trace (X : SKJBMat3 B) :
    Matrix.trace (toMatrix3 X) = SKJBTr3 X := by
  simp [toMatrix3, SKJBTr3, Matrix.trace, Matrix.diag, Fin.sum_univ_three, add_assoc]

omit [Ring B] in
/-- The coordinate embedding of the 3×3 carrier is injective. -/
lemma toMatrix3_injective :
    Function.Injective (toMatrix3 : SKJBMat3 B → Matrix (Fin 3) (Fin 3) B) := by
  intro X Y h
  cases X
  cases Y
  simp_all [toMatrix3]

end ThreeByThree

end InfoGeometry.Archetypes.SouriauKaluzaNativeMatrixBridge
