/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Clifford.BrauerWeylMatrixStep

/-!
# Universal nilpotent block holonomy over a noncommutative coefficient ring

This owner proves the nested block identities over an arbitrary unital ring.
The coefficient matrices remain operator-valued; only the separate infinite
order corollary uses the characteristic-zero hypothesis.
-/

namespace InfoGeometry.OperatorAlgebra.UniversalParabolicBlockMonodromy

open Matrix

variable {B : Type*} [Ring B]

abbrev Op₂ (B : Type*) := Matrix (Fin 2) (Fin 2) B
abbrev Block₂ (B : Type*) := Matrix (Fin 2) (Fin 2) (Op₂ B)

def fPlus : Op₂ B := InfoGeometry.Clifford.BrauerWeylMatrixStep.create
def fMinus : Op₂ B := InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate
def sigma : Op₂ B := InfoGeometry.Clifford.BrauerWeylMatrixStep.shift
def gamma : Op₂ B := InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality
def nPlus : Op₂ B := !![-1, -1; 1, 1]
def link : Op₂ B := (1 : Op₂ B) + fPlus
def linkInv : Op₂ B := (1 : Op₂ B) - fPlus

def xBlock : Block₂ B := !![0, linkInv; link, 0]
def zBlock : Block₂ B := !![sigma, 0; 0, gamma]
def nBlock : Block₂ B := !![nPlus, 0; 0, -fMinus]
def qBlock : Block₂ B := (zBlock * xBlock) * (zBlock * xBlock)

theorem blockMul00 (M N : Block₂ B) :
    (M * N) 0 0 = M 0 0 * N 0 0 + M 0 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem blockMul01 (M N : Block₂ B) :
    (M * N) 0 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem blockMul10 (M N : Block₂ B) :
    (M * N) 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem blockMul11 (M N : Block₂ B) :
    (M * N) 1 1 = M 1 0 * N 0 1 + M 1 1 * N 1 1 := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem blockExt {M N : Block₂ B}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  funext i
  fin_cases i
  · funext j
    fin_cases j
    · exact h00
    · exact h01
  · funext j
    fin_cases j
    · exact h10
    · exact h11

theorem opExt {M N : Op₂ B}
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) : M = N := by
  funext i
  fin_cases i
  · funext j
    fin_cases j
    · exact h00
    · exact h01
  · funext j
    fin_cases j
    · exact h10
    · exact h11

theorem link_mul_linkInv : (link : Op₂ B) * linkInv = 1 := by
  have h : (fPlus : Op₂ B) * fPlus = 0 := by
    simpa [fPlus] using
      (InfoGeometry.Clifford.BrauerWeylMatrixStep.witt_ladder_car (A := B)).1
  dsimp [link, linkInv]
  calc ((1 : Op₂ B) + fPlus) * ((1 : Op₂ B) - fPlus) =
      (1 : Op₂ B) - fPlus * fPlus := by noncomm_ring
    _ = 1 := by rw [h]; simp

theorem linkInv_mul_link : (linkInv : Op₂ B) * link = 1 := by
  have h : (fPlus : Op₂ B) * fPlus = 0 := by
    simpa [fPlus] using
      (InfoGeometry.Clifford.BrauerWeylMatrixStep.witt_ladder_car (A := B)).1
  dsimp [link, linkInv]
  calc ((1 : Op₂ B) - fPlus) * ((1 : Op₂ B) + fPlus) =
      (1 : Op₂ B) - fPlus * fPlus := by noncomm_ring
    _ = 1 := by rw [h]; simp

theorem xBlock_sq : (xBlock : Block₂ B) * xBlock = 1 := by
  apply blockExt
  · rw [blockMul00]
    simpa [xBlock] using linkInv_mul_link
  · rw [blockMul01]
    simp [xBlock]
  · rw [blockMul10]
    simp [xBlock]
  · rw [blockMul11]
    simpa [xBlock] using link_mul_linkInv

theorem zBlock_sq : (zBlock : Block₂ B) * zBlock = 1 := by
  apply blockExt
  · rw [blockMul00]
    simpa [zBlock, sigma] using
      (InfoGeometry.Clifford.BrauerWeylMatrixStep.shift_sq (A := B))
  · rw [blockMul01]
    simp [zBlock]
  · rw [blockMul10]
    simp [zBlock]
  · rw [blockMul11]
    simpa [zBlock, gamma] using
      (InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality_sq (A := B))

/-- The displayed plaquette decomposition is an identity in `M₂(M₂(B))`. -/
theorem qBlock_eq_one_add_nBlock : (qBlock : Block₂ B) = 1 + nBlock := by
  apply blockExt <;> apply opExt <;>
    simp [qBlock, zBlock, xBlock, link, linkInv, fPlus, fMinus, sigma,
      gamma, nBlock, nPlus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Matrix.one_apply, Fin.sum_univ_two,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.create,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.shift,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality] <;>
      try noncomm_ring

theorem nBlock_sq_zero : (nBlock : Block₂ B) * nBlock = 0 := by
  apply blockExt <;> apply opExt <;>
    simp [nBlock, nPlus, fMinus, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Fin.sum_univ_two,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate] <;>
      try noncomm_ring

theorem xBlock_conj_nBlock : (xBlock : Block₂ B) * nBlock * xBlock = -nBlock := by
  apply blockExt <;> apply opExt <;>
    simp [xBlock, link, linkInv, fPlus, nBlock, nPlus, fMinus,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Matrix.one_apply,
      Fin.sum_univ_two,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.create,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate] <;>
      try noncomm_ring

theorem zBlock_conj_nBlock : (zBlock : Block₂ B) * nBlock * zBlock = -nBlock := by
  apply blockExt <;> apply opExt <;>
    simp [zBlock, sigma, gamma, nBlock, nPlus, fMinus,
      Matrix.mul_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.shift,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.chirality,
      InfoGeometry.Clifford.BrauerWeylMatrixStep.annihilate] <;>
      try noncomm_ring

/-- Nilpotence gives a linear power law without commutativity of `B`. -/
theorem qBlock_pow (n : ℕ) : (qBlock : Block₂ B) ^ n = 1 + (n • nBlock) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, qBlock_eq_one_add_nBlock, add_nsmul, one_nsmul]
      have hn : ((n • nBlock) : Block₂ B) * nBlock = 0 := by
        rw [nsmul_eq_mul, mul_assoc, nBlock_sq_zero, mul_zero]
      calc
        ((1 : Block₂ B) + (n • nBlock)) * ((1 : Block₂ B) + nBlock)
            = 1 + ((n • nBlock) + nBlock) + (n • nBlock) * nBlock := by noncomm_ring
        _ = 1 + ((n • nBlock) + nBlock) := by rw [hn, add_zero]

/-- The involutions and holonomy satisfy the exact noncentral braiding law. -/
theorem block_braiding : (zBlock : Block₂ B) * xBlock = qBlock * xBlock * zBlock := by
  have hz : (zBlock : Block₂ B) * zBlock = 1 := zBlock_sq
  have hx : (xBlock : Block₂ B) * xBlock = 1 := xBlock_sq
  have hq : (qBlock : Block₂ B) = (zBlock * xBlock) * (zBlock * xBlock) := rfl
  rw [hq]
  symm
  calc
    ((zBlock * xBlock) * (zBlock * xBlock)) * xBlock * zBlock
        = ((zBlock * xBlock) * ((zBlock * xBlock) * xBlock)) * zBlock := by
            rw [mul_assoc (zBlock * xBlock) (zBlock * xBlock) xBlock]
    _ = ((zBlock * xBlock) * (zBlock * (xBlock * xBlock))) * zBlock := by
            rw [mul_assoc zBlock xBlock xBlock]
    _ = ((zBlock * xBlock) * zBlock) * zBlock := by
            rw [hx, mul_one]
    _ = (zBlock * xBlock) * (zBlock * zBlock) := by
            rw [mul_assoc (zBlock * xBlock) zBlock zBlock]
    _ = zBlock * xBlock := by
            rw [hz, mul_one]

theorem xBlock_cocycle_closure : (qBlock : Block₂ B) * (xBlock * qBlock * xBlock) = 1 := by
  rw [qBlock_eq_one_add_nBlock]
  calc
    ((1 : Block₂ B) + nBlock) * (xBlock * ((1 : Block₂ B) + nBlock) * xBlock)
        = (1 + nBlock) * (xBlock * xBlock + xBlock * nBlock * xBlock) := by
          noncomm_ring
    _ = (1 + nBlock) * (1 + -nBlock) := by
          rw [xBlock_sq, xBlock_conj_nBlock]
    _ = 1 := by
      calc ((1 : Block₂ B) + nBlock) * ((1 : Block₂ B) + -nBlock)
          = (1 : Block₂ B) - nBlock * nBlock := by noncomm_ring
        _ = 1 := by rw [nBlock_sq_zero, sub_zero]

theorem zBlock_cocycle_closure : ((zBlock : Block₂ B) * qBlock * zBlock) * qBlock = 1 := by
  rw [qBlock_eq_one_add_nBlock]
  calc
    (zBlock * ((1 : Block₂ B) + nBlock) * zBlock) * ((1 : Block₂ B) + nBlock)
        = (zBlock * zBlock + zBlock * nBlock * zBlock) * (1 + nBlock) := by
          noncomm_ring
    _ = (1 + -nBlock) * (1 + nBlock) := by
          rw [zBlock_sq, zBlock_conj_nBlock]
    _ = 1 := by
      calc ((1 : Block₂ B) + -nBlock) * ((1 : Block₂ B) + nBlock)
          = (1 : Block₂ B) - nBlock * nBlock := by noncomm_ring
        _ = 1 := by rw [nBlock_sq_zero, sub_zero]

/-- In characteristic zero the universal unipotent holonomy has infinite
multiplicative order. The witness is an entry of its nontrivial operator
block, not a scalar diagonal reduction. -/
theorem qBlock_infinite_order [CharZero B] (n : ℕ) (hn : 0 < n) :
    (qBlock : Block₂ B) ^ n ≠ 1 := by
  intro h
  have hentry := congrArg (fun M : Block₂ B => (M 0 0) 1 0) h
  rw [qBlock_pow] at hentry
  have hnB : (n : B) = (0 : B) := by
    simpa [nBlock, nPlus] using hentry
  have hn0 : n = 0 := by
    have hnB' : ((n : ℕ) : B) = ((0 : ℕ) : B) := by simpa only [Nat.cast_zero] using hnB
    exact Nat.cast_injective hnB'
  exact Nat.ne_of_gt hn hn0

/-- Matrix multiplication in `Op₂ B` is genuinely noncommutative over any
nontrivial coefficient ring. -/
theorem op2_noncommute [Nontrivial B] :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) B,
      matI * matJ ≠ matJ * matI := by
  refine ⟨!![(0 : B), 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Nested `2 × 2` block matrix multiplication in `Block₂ B` is genuinely
noncommutative over any nontrivial coefficient ring. -/
theorem block2_noncommute [Nontrivial B] :
    ∃ matI matJ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B),
      matI * matJ ≠ matJ * matI := by
  refine ⟨!![(0 : Matrix (Fin 2) (Fin 2) B), 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) B) => M 0 0) h
  have h00_00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) B => M 0 0) h00
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00_00

end InfoGeometry.OperatorAlgebra.UniversalParabolicBlockMonodromy
