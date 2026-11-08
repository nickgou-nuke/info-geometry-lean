/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.NCG.AnomalyGradeGeneration
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Exact residual for a block-swapped particle/hole associator sum

The carrier and multiplication are the repository-owned `OpZornMatrix A`
from `AlbertCayleyDickson`. In particular its vector cross operation is the
ordered skew difference `naiveCross u v - naiveCross v u`. The block swap
below is only a linear coordinate involution; no multiplicativity or
automorphism property is assumed. The main theorem computes the reflected
associator sum exactly, and a noncommutative matrix witness shows that it need
not vanish.
-/

namespace InfoGeometry.NCG.ReflectedAssociatorResidual

variable {A : Type*} [Ring A]

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix
open InfoGeometry.NCG.AnomalyGradeGeneration

/-- Swap the two scalar corners and the two vector blocks. -/
def blockSwap (X : OpZornMatrix A) : OpZornMatrix A :=
  ⟨X.b, X.w, X.v, X.a⟩

@[simp] theorem blockSwap_involutive (X : OpZornMatrix A) :
    blockSwap (blockSwap X) = X := by
  cases X
  rfl

/-- Exact failure of the block swap to preserve Zorn multiplication. The
scalar corners cancel; the two vector corners retain opposite skew-cross
defects. In particular, the involution is not silently treated as an
algebra automorphism. -/
theorem blockSwap_product_defect (X Y : OpZornMatrix A) :
    blockSwap (X * Y) - blockSwap X * blockSwap Y =
      ⟨0,
        OpVec3.skewCross X.v Y.v + OpVec3.skewCross X.v Y.v,
        -(OpVec3.skewCross X.w Y.w + OpVec3.skewCross X.w Y.w),
        0⟩ := by
  ext <;>
    simp [blockSwap, mul_a, mul_b, mul_v, mul_w,
      OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
      OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- The three-term reflected associator sum is the exact ordered residual
of contraction and the repository's skew-cross associator. -/
theorem block_swap_associator_sum_eq_residual
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (blockSwap (fockLower w))
        (blockSwap (fockRaise v)) +
      opAssociator (blockSwap (fockRaise u)) (blockSwap (fockLower w))
        (fockRaise v) =
      fockRaise
        (-OpVec3.leftScale (OpVec3.dot u w) v +
          OpVec3.rightScale u (OpVec3.dot w v) -
          OpVec3.skewCross (OpVec3.skewCross u w) v +
          OpVec3.skewCross u (OpVec3.skewCross w v)) := by
  ext <;>
    simp [opAssociator, blockSwap, fockRaise, fockLower,
      mul_a, mul_b, mul_v, mul_w, OpVec3.dot, OpVec3.skewCross,
      OpVec3.naiveCross, OpVec3.leftScale, OpVec3.rightScale] <;>
    noncomm_ring

/-- Exact cancellation criterion for the reflected associator sum. The
three-term sum vanishes precisely when its ordered vector residual vanishes;
this leaves the noncommutative coefficient equations visible instead of
asserting an unconditional cancellation law. -/
theorem block_swap_associator_sum_eq_zero_iff_residual_eq_zero
    (u w v : OpVec3 A) :
    opAssociator (fockRaise u) (fockLower w) (fockRaise v) +
      opAssociator (fockRaise u) (blockSwap (fockLower w))
        (blockSwap (fockRaise v)) +
      opAssociator (blockSwap (fockRaise u)) (blockSwap (fockLower w))
        (fockRaise v) = 0 ↔
      -OpVec3.leftScale (OpVec3.dot u w) v +
        OpVec3.rightScale u (OpVec3.dot w v) -
        OpVec3.skewCross (OpVec3.skewCross u w) v +
        OpVec3.skewCross u (OpVec3.skewCross w v) = 0 := by
  rw [block_swap_associator_sum_eq_residual]
  exact fockRaise_eq_zero_iff _

/-! ## A noncommutative matrix witness -/

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℤ

def witnessA : Mat₂ := !![0, 1; 0, 0]
def witnessB : Mat₂ := !![0, 0; 1, 0]
def witnessC : Mat₂ := !![1, 0; 0, 0]

def witnessU : OpVec3 Mat₂ := ⟨witnessA, 0, 0⟩
def witnessW : OpVec3 Mat₂ := ⟨0, witnessB, 0⟩
def witnessV : OpVec3 Mat₂ := ⟨0, witnessC, 0⟩

/-- The block-swap involution fails to preserve multiplication on the same
noncommuting matrix coefficients used in the associator witness. -/
theorem blockSwap_not_multiplicative_on_witness :
    blockSwap (fockRaise witnessU * fockRaise witnessW) ≠
      blockSwap (fockRaise witnessU) * blockSwap (fockRaise witnessW) := by
  intro h
  have hzero := sub_eq_zero.mpr h
  have hdef := blockSwap_product_defect
    (fockRaise witnessU) (fockRaise witnessW)
  rw [hzero] at hdef
  have hz := congrArg (fun X : OpZornMatrix Mat₂ => X.v.z 0 0) hdef
  norm_num [fockRaise, witnessU, witnessW, witnessA, witnessB,
    OpVec3.skewCross, OpVec3.naiveCross, OpVec3.leftScale,
    OpVec3.rightScale, Matrix.mul_apply, Fin.sum_univ_succ] at hz

/-- The chosen coefficient matrices do not commute. -/
theorem witness_coefficients_noncommute : witnessA * witnessB ≠ witnessB * witnessA := by
  intro h
  have h₀₀ := congrArg (fun M : Mat₂ => M 0 0) h
  norm_num [witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_succ] at h₀₀

/-- The reflected associator sum is nonzero on the noncommuting `2 × 2`
matrix witness. This refutes a universal cancellation claim for this block
swap and the repository's actual `OpZornMatrix` product. -/
theorem witness_block_swap_associator_sum_ne_zero :
    opAssociator (fockRaise witnessU) (fockLower witnessW) (fockRaise witnessV) +
      opAssociator (fockRaise witnessU) (blockSwap (fockLower witnessW))
        (blockSwap (fockRaise witnessV)) +
      opAssociator (blockSwap (fockRaise witnessU)) (blockSwap (fockLower witnessW))
        (fockRaise witnessV) ≠ 0 := by
  rw [block_swap_associator_sum_eq_residual]
  intro h
  have h₀₀ := congrArg
    (fun X : OpZornMatrix Mat₂ => X.v.x 0 0) h
  norm_num [witnessU, witnessW, witnessV, witnessA, witnessB, witnessC,
    fockRaise, OpVec3.dot, OpVec3.skewCross, OpVec3.naiveCross,
    OpVec3.leftScale, OpVec3.rightScale, Matrix.mul_apply,
    Fin.sum_univ_succ] at h₀₀

end InfoGeometry.NCG.ReflectedAssociatorResidual
