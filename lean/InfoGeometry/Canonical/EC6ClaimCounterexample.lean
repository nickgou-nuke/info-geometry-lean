/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Counterexample to the unrestricted EC6 curvature contractions

The proposed identities contracting the skew upper-corner anomaly with a
lower-corner operator fail in a genuine noncommutative block matrix ring.  The
example below uses `2 × 2` block matrices with `2 × 2` integer-matrix entries
(equivalently, operators on a four-dimensional free module).  The off-diagonal
blocks are noncommuting, and the lower diagonal block has the opposite sign.
-/

namespace InfoGeometry.Canonical.EC6ClaimCounterexample

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ
abbrev BlockOp := Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)

def e11 : M2 := !![1, 0; 0, 0]
def e12 : M2 := !![0, 1; 0, 0]

def cut : BlockOp := !![1, 0; 0, 0]
def n₁ : BlockOp := !![0, e11; 0, 0]
def n₂ : BlockOp := !![0, e12; 0, 0]
def m : BlockOp := !![0, 0; 1, 0]

def plus (A : BlockOp) : BlockOp := cut * A * (1 - cut)
def minus (C : BlockOp) : BlockOp := (1 - cut) * C * cut
def sig (N : BlockOp) : BlockOp := N * m - m * N
def metric (N : BlockOp) : BlockOp := N * m + m * N
def anomaly : BlockOp := plus n₁ * minus m * plus n₂ - plus n₂ * minus m * plus n₁
def bracket (X Y : BlockOp) : BlockOp := X * Y - Y * X
def jordan (X Y : BlockOp) : BlockOp := X * Y + Y * X

theorem cut_idempotent : cut * cut = cut := by decide

theorem plus_support : plus n₁ = n₁ ∧ plus n₂ = n₂ := by decide

theorem minus_support : minus m = m := by decide

theorem first_EC6_contraction_fails :
    bracket anomaly (minus m) ≠ bracket (sig (plus n₁)) (sig (plus n₂)) := by decide

theorem second_EC6_contraction_fails :
    jordan anomaly (minus m) ≠ bracket (sig (plus n₁)) (metric (plus n₂)) := by decide

/-- Explicit non-commutativity witness on the nested `2 × 2` block-matrix ring `BlockOp`. -/
theorem ec6_blockOp_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ), A * B ≠ B * A :=
  ⟨n₁, m, by decide⟩

end InfoGeometry.Canonical.EC6ClaimCounterexample
