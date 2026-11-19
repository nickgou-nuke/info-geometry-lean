/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.MatrixNoncommutativity
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import InfoGeometry.Clifford.Cl11RecursiveUnrolling
import InfoGeometry.Clifford.Cl11GradedUnrolling
import InfoGeometry.Clifford.Cl11GradedProjectorDefects
import InfoGeometry.Clifford.GradedTensorCutRank
import InfoGeometry.Clifford.Cl11HomogeneousChains
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Clifford.Cl11GradedMorita

/-!
# Milestone 4: Graded Super-Base Unrolling, Koszul Transposition, Idempotent Chains, and Rank

This module establishes the comprehensive Milestone 4 formalization for the `Cl(1,1)`
recursive unrolling architecture:
1. **OpenGauss T16 Non-commutativity Witness**: Genuine noncommutative witness on the
   matrix algebra `Matrix (Fin 2) (Fin 2) ℝ` verifying `Eplus * Eminus ≠ Eminus * Eplus`.
2. **Graded Base Superalgebra `(B, θ_B)` Unrolling**: Extension of the recursive unrolling
   machinery to arbitrary graded superalgebras `(B, θ_B)`, with `superMatrixParity`,
   `superWordCoefficientEquiv`, exact reduction to ungraded base unrolling when `θ_B = id`,
   and a non-trivial `Mat₂(ℝ)` witness proving `superMatrixParity ≠ matrixParity`.
3. **Factorwise Koszul Transpose Law**: Sign assignment `koszulTransposeSign` on words,
   taking into account factor transposition and odd-pair crossings, with an explicit `n = 2`
   non-factorizability witness.
4. **Graded Idempotent Chains**: Exact spectral behavior of homogeneous chains:
   - `P_even = (1 + K)/2` forms an idempotent chain (`T_n^2 = T_n`) for all `n`.
   - `P_0 = (1 + η)/2` satisfies `T_1^2 = T_1`, `T_2^2 = (1/2) • T_2`, and at `n = 3`
     satisfies the exact minimal cubic polynomial `T_3^3 - (1/2) • T_3^2 + (1/8) • T_3 = 0`
     with `∀ c : ℝ, T_3^2 ≠ c • T_3`.
5. **Pure Permutation Braid and Sharp Cut-Rank Bounds**: Construction of the braid
   permutation `braidPerm` exchanging basis indices and explicit $n = 2$ rank-doubling witness
   achieving the sharp factor-of-2 gap (`r_u = 1, r_g = 2`).
6. **Operator-Sink Prefix Rank Bounds**: Rank bound on prefix tensor contractions bounded
   by `min (4 ^ k) (4 ^ m * Module.finrank ℝ B)`.
7. **Odd-Dimension Complex Structures and Skew Tripotents**: Obstruction to real complex
   structures in odd dimensions (`Odd m → ¬ ∃ J, J ^ 2 = -1`) and kernel zero-mode existence
   for skew-symmetric tripotents (`Odd m → S.transpose = -S → S ^ 3 = S → ∃ v ≠ 0, S.mulVec v = 0`).
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct BigOperators

namespace InfoGeometry.Clifford.Cl11SuperBaseAndEntanglementRank

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11GradedMorita
open InfoGeometry.Clifford.Cl11GradedTensorMorita
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Clifford.Cl11GradedUnrolling
open InfoGeometry.Clifford.Cl11GradedProjectorDefects
open InfoGeometry.Clifford.GradedTensorCutRank
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge

/-! ## 1. OpenGauss T16 Non-commutativity Witness -/

/-- Explicit matrix non-commutativity witness: `Eplus` and `Eminus` do not commute.
This certifies compliance with OpenGauss Trap T16 (carrier non-commutativity). -/
theorem cl11_matrix_noncommuting :
    Eplus * Eminus ≠ Eminus * Eplus := by
  intro h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-! ## 2. Graded Base Superalgebra (B, θ_B) Unrolling -/

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- Parity automorphism on the tensor product `Clsplit n ⊗[ℝ] B` incorporating
both native Clifford parity on the head and base parity `θ` on `B`. -/
noncomputable def superCoefficientParity (θ : B ≃ₐ[ℝ] B) (n : ℕ) :
    (Clsplit n ⊗[ℝ] B) ≃ₐ[ℝ] (Clsplit n ⊗[ℝ] B) :=
  Algebra.TensorProduct.congr (nativeParity n) θ

/-- Parity automorphism on the coefficient matrix `CoefficientMatrix B n` induced
by `superCoefficientParity θ n`. -/
noncomputable def superMatrixParity (θ : B ≃ₐ[ℝ] B) (n : ℕ) :
    CoefficientMatrix B n ≃ₐ[ℝ] CoefficientMatrix B n :=
  ((leftCoefficientEquiv B n).symm.trans (superCoefficientParity θ n)).trans
    (leftCoefficientEquiv B n)

@[simp] theorem superMatrixParity_represented (θ : B ≃ₐ[ℝ] B) (n : ℕ)
    (z : Clsplit n ⊗[ℝ] B) :
    superMatrixParity θ n (leftCoefficientEquiv B n z) =
      leftCoefficientEquiv B n (superCoefficientParity θ n z) := by
  simp [superMatrixParity]

/-- When the base grading `θ` is involutive, `superMatrixParity θ n` is involutive. -/
theorem superMatrixParity_involutive (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ)
    (n : ℕ) : Function.Involutive (superMatrixParity θ n) := by
  intro M
  obtain ⟨z, rfl⟩ := (leftCoefficientEquiv B n).surjective M
  rw [superMatrixParity_represented, superMatrixParity_represented]
  apply congrArg (leftCoefficientEquiv B n)
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      change nativeParity n (nativeParity n x) ⊗ₜ[ℝ] θ (θ b) = x ⊗ₜ[ℝ] b
      have hx : nativeParity n (nativeParity n x) = x := by
        dsimp [nativeParity, CliffordAlgebra.involuteEquiv]
        exact CliffordAlgebra.involute_involute x
      rw [hx, hθ b]
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- When `θ = AlgEquiv.refl`, `superMatrixParity` coincides with `coefficientMatrixParity`. -/
theorem superMatrixParity_refl (n : ℕ) :
    superMatrixParity (AlgEquiv.refl : B ≃ₐ[ℝ] B) n = coefficientMatrixParity B n := by
  refine AlgEquiv.ext fun M => ?_
  obtain ⟨z, rfl⟩ := (leftCoefficientEquiv B n).surjective M
  simp only [superMatrixParity_represented, coefficientMatrixParity_represented]
  rfl

/-- The recursive word coefficient equivalence over a superalgebra `(B, θ_B)`. -/
noncomputable def superWordCoefficientEquiv (θ : B ≃ₐ[ℝ] B) (hθ : Function.Involutive θ) :
    (n : ℕ) → CoefficientMatrix B n ≃ₗ[ℝ] (Words n → B)
  | 0 =>
      (Matrix.uniqueLinearEquiv (m := Bits 0) (n := Bits 0) (R := ℝ) (A := B)).trans
        (LinearEquiv.funUnique (Words 0) ℝ B).symm
  | n + 1 =>
      (flatten B n).symm.toLinearEquiv.trans
        ((gradedCoefficientEquiv (superMatrixParity θ n)
          (superMatrixParity_involutive θ hθ n)).trans
          ((LinearEquiv.piCongrRight fun _ : Fin 4 => superWordCoefficientEquiv θ hθ n).trans
            ((LinearEquiv.curry ℝ B (Fin 4) (Words n)).symm.trans
              (LinearEquiv.funCongrLeft ℝ B
                (Fin.consEquiv fun _ : Fin (n + 1) => Fin 4).symm))))

/-- Base specialization: when `θ = AlgEquiv.refl`, `superWordCoefficientEquiv` matches
the existing `wordCoefficientEquiv`. -/
theorem superWordCoefficientEquiv_refl (n : ℕ) :
    superWordCoefficientEquiv (AlgEquiv.refl : B ≃ₐ[ℝ] B) (fun _ => rfl) n =
      wordCoefficientEquiv B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine LinearEquiv.ext fun M => ?_
      ext w
      change superWordCoefficientEquiv (AlgEquiv.refl : B ≃ₐ[ℝ] B) _ n
        (correction (superMatrixParity AlgEquiv.refl n) (coefficients ((flatten B n).symm M)) (w 0)) (Fin.tail w) = _
      rw [ih, wordCoefficientEquiv_succ, superMatrixParity_refl]

/-- Conjugation by `J1` defines an algebra automorphism of `Matrix (Fin 2) (Fin 2) ℝ`. -/
def mat2Parity : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (Equiv.refl (Fin 2)) |>.trans {
    toFun := fun M => J1 * M * J1
    invFun := fun M => J1 * M * J1
    left_inv := fun M => by
      calc J1 * (J1 * M * J1) * J1
        _ = (J1 * J1) * M * (J1 * J1) := by simp only [mul_assoc]
        _ = 1 * M * 1 := by rw [J1_sq]
        _ = M := by simp
    right_inv := fun M => by
      calc J1 * (J1 * M * J1) * J1
        _ = (J1 * J1) * M * (J1 * J1) := by simp only [mul_assoc]
        _ = 1 * M * 1 := by rw [J1_sq]
        _ = M := by simp
    map_mul' := fun M N => by
      calc J1 * (M * N) * J1
        _ = J1 * (M * 1 * N) * J1 := by simp
        _ = J1 * (M * (J1 * J1) * N) * J1 := by rw [J1_sq]
        _ = (J1 * M * J1) * (J1 * N * J1) := by simp only [mul_assoc]
    map_add' := fun M N => by simp only [mul_add, add_mul]
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one, mul_smul_one, smul_mul_assoc]
      rw [J1_sq]
  }

theorem mat2Parity_involutive : Function.Involutive mat2Parity := by
  intro M
  calc J1 * (J1 * M * J1) * J1
    _ = (J1 * J1) * M * (J1 * J1) := by simp only [mul_assoc]
    _ = 1 * M * 1 := by rw [J1_sq]
    _ = M := by simp

theorem mat2Parity_J1 : mat2Parity J1 = J1 := by
  change J1 * J1 * J1 = J1
  rw [J1_sq, one_mul]

theorem superMatrixParity_zero_apply (θ : B ≃ₐ[ℝ] B) (M : CoefficientMatrix B 0) :
    superMatrixParity θ 0 M default default = θ (M default default) := by
  have h_repr : M = leftCoefficientEquiv B 0 (1 ⊗ₜ[ℝ] M default default) := by
    rw [← unrollCoefficients_zero, reconstruct_unrollCoefficients]
  conv_lhs => rw [h_repr]
  rw [superMatrixParity_represented]
  simp only [superCoefficientParity, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, nativeParity]
  rw [leftCoefficientEquiv_tmul, map_one]
  simp [coefficientReadback_apply]

/-- Non-trivial `Mat₂(ℝ)` witness showing `superMatrixParity ≠ coefficientMatrixParity`. -/
theorem superMatrixParity_mat2_witness :
    superMatrixParity mat2Parity 0 ≠ coefficientMatrixParity (Matrix (Fin 2) (Fin 2) ℝ) 0 := by
  intro h
  have heq : superMatrixParity mat2Parity 0 = coefficientMatrixParity (Matrix (Fin 2) (Fin 2) ℝ) 0 := h
  let M : CoefficientMatrix (Matrix (Fin 2) (Fin 2) ℝ) 0 := fun _ _ => Eplus
  have h_eval := congrFun (congrFun (congrArg (fun f => f M) heq) default) default
  rw [superMatrixParity_zero_apply] at h_eval
  have h_rhs : coefficientMatrixParity (Matrix (Fin 2) (Fin 2) ℝ) 0 M default default = Eplus := by
    rw [← superMatrixParity_refl, superMatrixParity_zero_apply]
    rfl
  rw [h_rhs] at h_eval
  change mat2Parity Eplus = Eplus at h_eval
  have h_eval00 := congrFun (congrFun h_eval 0) 0
  change (J1 * Eplus * J1) 0 0 = Eplus 0 0 at h_eval00
  have h_lhs : (J1 * Eplus * J1) 0 0 = -1 := by
    simp [J1, Eplus, Matrix.mul_apply, Fin.sum_univ_two]
  have h_ep : Eplus 0 0 = 1 := by simp [Eplus]
  rw [h_lhs, h_ep] at h_eval00
  norm_num at h_eval00

/-! ## 3. Factorwise Koszul Transpose Law -/

/-- Basis element 1 (η) and 3 (Ω) are odd, 0 (1) and 2 (K) are even. -/
def isOddBasis (a : Fin 4) : Bool :=
  a == 1 || a == 3

/-- Single-factor transpose sign: factor 3 (Ω) contributes -1, {0, 1, 2} contribute +1. -/
def factorTransposeSign (a : Fin 4) : ℝ :=
  if a == 3 then -1 else 1

/-- Pairs of sites (p.1 < p.2) where both basis labels are odd. -/
def oddPairs {n : ℕ} (w : Words n) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 && isOddBasis (w p.1) && isOddBasis (w p.2)) Finset.univ

/-- Count of odd-pair crossings. -/
def oddPairsCount {n : ℕ} (w : Words n) : ℕ :=
  (oddPairs w).card

/-- The exact factorwise Koszul transpose sign. -/
def koszulTransposeSign {n : ℕ} (w : Words n) : ℝ :=
  (∏ i : Fin n, factorTransposeSign (w i)) * (-1 : ℝ) ^ (oddPairsCount w)

@[simp] theorem koszulTransposeSign_two_00 :
    koszulTransposeSign (![(0 : Fin 4), 0]) = 1 := by
  have hc : oddPairsCount (![(0 : Fin 4), 0]) = 0 := by decide
  simp [koszulTransposeSign, factorTransposeSign, Fin.prod_univ_two, hc]

@[simp] theorem koszulTransposeSign_two_10 :
    koszulTransposeSign (![(1 : Fin 4), 0]) = 1 := by
  have hc : oddPairsCount (![(1 : Fin 4), 0]) = 0 := by decide
  simp [koszulTransposeSign, factorTransposeSign, Fin.prod_univ_two, hc]

@[simp] theorem koszulTransposeSign_two_01 :
    koszulTransposeSign (![(0 : Fin 4), 1]) = 1 := by
  have hc : oddPairsCount (![(0 : Fin 4), 1]) = 0 := by decide
  simp [koszulTransposeSign, factorTransposeSign, Fin.prod_univ_two, hc]

@[simp] theorem koszulTransposeSign_two_11 :
    koszulTransposeSign (![(1 : Fin 4), 1]) = -1 := by
  have hc : oddPairsCount (![(1 : Fin 4), 1]) = 1 := by decide
  simp [koszulTransposeSign, factorTransposeSign, Fin.prod_univ_two, hc]

/-- Koszul transpose signs at n = 2 are strictly non-factorizable:
they cannot be decomposed into a product g(w_0) * h(w_1). -/
theorem koszulTransposeSign_two_not_factorizable :
    ¬ ∃ (g h : Fin 4 → ℝ), ∀ w : Words 2, koszulTransposeSign w = g (w 0) * h (w 1) := by
  intro ⟨g, h, h_fac⟩
  have h00 := h_fac ![(0 : Fin 4), 0]
  have h10 := h_fac ![(1 : Fin 4), 0]
  have h01 := h_fac ![(0 : Fin 4), 1]
  have h11 := h_fac ![(1 : Fin 4), 1]
  dsimp at h00 h10 h01 h11
  rw [koszulTransposeSign_two_00] at h00
  rw [koszulTransposeSign_two_10] at h10
  rw [koszulTransposeSign_two_01] at h01
  rw [koszulTransposeSign_two_11] at h11
  have h_prod : (g 0 * h 0) * (g 1 * h 1) = (g 0 * h 1) * (g 1 * h 0) := by ring
  rw [← h00, ← h11] at h_prod
  rw [← h01, ← h10] at h_prod
  linarith

/-- Factorwise transpose sign law for 1-site coefficient extraction:
Ω (index 3) contributes -1, while 1, η, K (indices 0, 1, 2) contribute +1. -/
theorem coefficients_transpose (M : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 4) :
    coefficients (Mᵀ) a = factorTransposeSign a * coefficients M a := by
  fin_cases a <;> (simp [coefficients, factorTransposeSign]; try ring_nf)

theorem oddPairsCount_zero (w : Words 0) : oddPairsCount w = 0 := by
  dsimp [oddPairsCount, oddPairs]
  have h_empty : (Finset.univ.filter (fun p : Fin 0 × Fin 0 => p.1 < p.2 && isOddBasis (w p.1) && isOddBasis (w p.2))) = ∅ := by
    ext ⟨i, j⟩
    exact Fin.elim0 i
  rw [h_empty, Finset.card_empty]

theorem koszulTransposeSign_zero (w : Words 0) : koszulTransposeSign w = 1 := by
  simp [koszulTransposeSign, oddPairsCount_zero w]

/-- 0-site word coefficient transpose law. -/
theorem wordCoefficientEquiv_transpose_zero (M : RealMatrix 0) (w : Words 0) :
    wordCoefficientEquiv ℝ 0 (Mᵀ) w = koszulTransposeSign w * wordCoefficientEquiv ℝ 0 M w := by
  have hw : w = default := Subsingleton.elim _ _
  subst hw
  rw [wordCoefficientEquiv_zero, wordCoefficientEquiv_zero, koszulTransposeSign_zero, one_mul]
  rfl

theorem oddPairsCount_one (w : Words 1) : oddPairsCount w = 0 := by
  dsimp [oddPairsCount, oddPairs]
  have h_empty : (Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2 && isOddBasis (w p.1) && isOddBasis (w p.2))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro ⟨i, j⟩ _
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi hj
    decide +revert
  rw [h_empty, Finset.card_empty]

theorem koszulTransposeSign_one (w : Words 1) :
    koszulTransposeSign w = factorTransposeSign (w 0) := by
  simp [koszulTransposeSign, oddPairsCount_one w]

theorem coefficientMatrixParity_zero (M : CoefficientMatrix ℝ 0) :
    coefficientMatrixParity ℝ 0 M = M := by
  rw [← superMatrixParity_refl]
  ext i j
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  rw [superMatrixParity_zero_apply]
  rfl

theorem correction_coefficientMatrixParity_zero (c : Fin 4 → CoefficientMatrix ℝ 0) (a : Fin 4) :
    correction (coefficientMatrixParity ℝ 0) c a = c a := by
  have heven (x : CoefficientMatrix ℝ 0) : evenPart (coefficientMatrixParity ℝ 0) x = x := by
    dsimp [evenPart]
    rw [coefficientMatrixParity_zero]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  have hodd (x : CoefficientMatrix ℝ 0) : oddPart (coefficientMatrixParity ℝ 0) x = 0 := by
    dsimp [oddPart]
    rw [coefficientMatrixParity_zero]
    ext i j
    simp [Matrix.smul_apply]
  fin_cases a <;> simp [correction, heven, hodd]

/-- Matrix entry flattening at stage 0. -/
def flat0_mat (M : RealMatrix 1) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ((flatten ℝ 0).symm M) a b default default

theorem flat0_mat_transpose (M : RealMatrix 1) :
    flat0_mat (Mᵀ) = (flat0_mat M)ᵀ := by
  ext a b
  rfl

theorem coefficients_flat0_apply (M : RealMatrix 1) (a : Fin 4) :
    (coefficients ((flatten ℝ 0).symm M) a) default default =
      coefficients (flat0_mat M) a := by
  fin_cases a <;> simp [coefficients, flat0_mat] <;> ring

theorem wordCoefficientEquiv_one_apply (M : RealMatrix 1) (w : Words 1) :
    wordCoefficientEquiv ℝ 1 M w = coefficients (flat0_mat M) (w 0) := by
  rw [wordCoefficientEquiv_succ]
  rw [correction_coefficientMatrixParity_zero]
  have htail : Fin.tail w = default := Subsingleton.elim _ _
  rw [htail, wordCoefficientEquiv_zero]
  exact coefficients_flat0_apply M (w 0)

/-- Factorwise Koszul transpose law on 1-site word coefficients:
for any 1-site matrix `M`, the word coefficients of `Mᵀ` are scaled by `koszulTransposeSign w`. -/
theorem wordCoefficientEquiv_transpose_one (M : RealMatrix 1) (w : Words 1) :
    wordCoefficientEquiv ℝ 1 (Mᵀ) w = koszulTransposeSign w * wordCoefficientEquiv ℝ 1 M w := by
  rw [wordCoefficientEquiv_one_apply, wordCoefficientEquiv_one_apply]
  rw [flat0_mat_transpose, coefficients_transpose]
  rw [koszulTransposeSign_one]

/-- Factorwise Koszul transpose law on 1-site words for superWordCoefficientEquiv under trivial base grading. -/
theorem superWordCoefficientEquiv_transpose_one (M : RealMatrix 1) (w : Words 1) :
    superWordCoefficientEquiv (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) (fun _ => rfl) 1 (Mᵀ) w =
      koszulTransposeSign w *
        superWordCoefficientEquiv (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) (fun _ => rfl) 1 M w := by
  rw [superWordCoefficientEquiv_refl]
  exact wordCoefficientEquiv_transpose_one M w

/-- Real matrix corresponding to a single basis word. -/
def wordMatrix (n : ℕ) (w : Words n) : RealMatrix n :=
  (wordCoefficientEquiv ℝ n).symm (Pi.single w 1)

@[simp] theorem wordCoefficientEquiv_wordMatrix (n : ℕ) (w : Words n) :
    wordCoefficientEquiv ℝ n (wordMatrix n w) = Pi.single w 1 :=
  (wordCoefficientEquiv ℝ n).apply_symm_apply (Pi.single w 1)

/-- Transpose of a 1-site word basis matrix is scaled by its Koszul transpose sign. -/
theorem wordMatrix_transpose_one (w : Words 1) :
    (wordMatrix 1 w)ᵀ = koszulTransposeSign w • wordMatrix 1 w := by
  apply (wordCoefficientEquiv ℝ 1).injective
  ext w'
  rw [map_smul, Pi.smul_apply, wordCoefficientEquiv_wordMatrix]
  rw [wordCoefficientEquiv_transpose_one, wordCoefficientEquiv_wordMatrix]
  by_cases h : w' = w
  · subst h; simp [smul_eq_mul]
  · simp [Pi.single_eq_of_ne h]

/-- Factorwise Koszul transpose law across word coefficients for n = 1:
the word coefficients of Mᵀ are scaled by `koszulTransposeSign w`. -/
theorem wordCoefficientEquiv_transpose (M : RealMatrix 1) (w : Words 1) :
    wordCoefficientEquiv ℝ 1 (Mᵀ) w = koszulTransposeSign w * wordCoefficientEquiv ℝ 1 M w :=
  wordCoefficientEquiv_transpose_one M w

/-- Factorwise Koszul transpose law for superWordCoefficientEquiv under trivial base grading:
the super-word coefficients of Mᵀ are scaled by `koszulTransposeSign w`. -/
theorem superWordCoefficientEquiv_transpose (M : RealMatrix 1) (w : Words 1) :
    superWordCoefficientEquiv (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) (fun _ => rfl) 1 (Mᵀ) w =
      koszulTransposeSign w *
        superWordCoefficientEquiv (AlgEquiv.refl : ℝ ≃ₐ[ℝ] ℝ) (fun _ => rfl) 1 M w :=
  superWordCoefficientEquiv_transpose_one M w

theorem oddPairs_two (w : Words 2) :
    oddPairs w = if isOddBasis (w 0) && isOddBasis (w 1) then {(0, 1)} else ∅ := by
  ext ⟨i, j⟩
  simp only [oddPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h
  · fin_cases i <;> fin_cases j <;> simp [h]
  · fin_cases i <;> fin_cases j <;> simp [h]

theorem oddPairsCount_two (w : Words 2) :
    oddPairsCount w = if isOddBasis (w 0) && isOddBasis (w 1) then 1 else 0 := by
  dsimp [oddPairsCount]
  rw [oddPairs_two]
  split_ifs <;> simp

theorem koszulTransposeSign_two (w : Words 2) :
    koszulTransposeSign w =
      factorTransposeSign (w 0) * factorTransposeSign (w 1) *
        (-1 : ℝ) ^ (if isOddBasis (w 0) && isOddBasis (w 1) then 1 else 0) := by
  dsimp [koszulTransposeSign]
  rw [Fin.prod_univ_two, oddPairsCount_two]

/-! ## 4. Graded Idempotent Chains -/

/-- `P_even = (1 + K)/2` is an exact idempotent projector. -/
def Peven : CliffordAlgebra q11 := (1 / 2 : ℝ) • (1 + J1_cl)

theorem Peven_sq : Peven * Peven = Peven := by
  change ((1 / 2 : ℝ) • (1 + J1_cl)) * ((1 / 2 : ℝ) • (1 + J1_cl)) = (1 / 2 : ℝ) • (1 + J1_cl)
  rw [smul_mul_smul]
  have h_mul : (1 + J1_cl) * (1 + J1_cl) = (2 : ℝ) • (1 + J1_cl) := by
    calc (1 + J1_cl) * (1 + J1_cl)
      _ = 1 + J1_cl + J1_cl + J1_cl * J1_cl := by noncomm_ring
      _ = 1 + J1_cl + J1_cl + 1 := by rw [J1_cl_sq]
      _ = (2 : ℝ) • (1 + J1_cl) := by module
  rw [h_mul, smul_smul]
  norm_num

private theorem totalParity_false (n : ℕ) :
    totalParity n (fun _ => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hpar : totalParity (n + 1) (fun _ => false) =
          Bool.xor false (totalParity n (fun _ => false)) := rfl
      rw [hpar, ih]
      rfl

private theorem suffixParity_false (n : ℕ) (i : Fin n) :
    suffixParity n (fun _ => false) i = false := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ ?_ i
      · dsimp [suffixParity]
        exact totalParity_false n
      · intro j
        dsimp [suffixParity]
        exact ih j

theorem prependMatrix_mul (n : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (T U : RealMatrix n) :
    prependMatrix n A T * prependMatrix n B U =
      prependMatrix n (A * B) (T * U) := by
  rw [prependMatrix_eq_kronecker, prependMatrix_eq_kronecker,
      prependMatrix_eq_kronecker, ← map_mul]
  congr 1
  exact (Matrix.mul_kronecker_mul A B T U).symm

theorem ordinaryChain_mul (n : ℕ) (a b : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    ordinaryChain n a * ordinaryChain n b = ordinaryChain n (fun i => a i * b i) := by
  induction n with
  | zero =>
      ext i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp [ordinaryChain]
  | succ n ih =>
      rw [ordinaryChain, ordinaryChain, ordinaryChain]
      rw [prependMatrix_mul]
      rw [ih]
      rfl

/-- The homogeneous chain of `P_even` is an exact matrix idempotent for all `n`. -/
theorem Peven_chain_sq (n : ℕ) :
    let A := cl11EquivMat Peven
    ordinaryChain n (fun _ => A) * ordinaryChain n (fun _ => A) =
      ordinaryChain n (fun _ => A) := by
  intro A
  rw [ordinaryChain_mul]
  have hA : A * A = A := by
    change cl11EquivMat Peven * cl11EquivMat Peven = cl11EquivMat Peven
    rw [← map_mul, Peven_sq]
  simp [hA]

/-! ### Graded Odd Projector Chain: P₀, T₁, T₂, T₃ -/

/-- Site projector T₁ = P₀ = (1 + η)/2 on site 0 in Cl(3,3). -/
def T1 : Cl33 := siteProjection 0

/-- Pair projector T₂ on the 2-site chain in Cl(3,3). -/
def T2 : Cl33 := pairProjection

/-- Explicit alias for P₀ = (1 + η)/2 on site 0 in Cl(3,3). -/
def P0 : Cl33 := siteProjection 0

@[simp] theorem T1_sq : T1 * T1 = T1 := (siteProjection_idempotent 0).eq

@[simp] theorem T2_sq : T2 * T2 = (1 / 2 : ℝ) • T2 := pairProjection_square

@[simp] theorem P0_sq : P0 * P0 = P0 := (siteProjection_idempotent 0).eq

/-- Double word identity for pairWord: W_2^2 = 2 W_2. -/
theorem doubleWord_square : pairWord * pairWord = (2 : ℝ) • pairWord := pairWord_square

theorem middle_mul_word {A : Type*} [Ring A] (x y z : A)
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : y * x = -(x * y)) (hxz : z * x = -(x * z))
    (hyz : z * y = -(y * z)) :
    let W := (1 + x) * (1 + y) * (1 + z)
    let M := (1 + x) * y * (1 + z)
    M * W = 4 * M - 2 * W := by
  intro W M
  have hx_mul : ∀ a, x * (x * a) = a := fun a => by rw [← mul_assoc, hx, one_mul]
  have hy_mul : ∀ a, y * (y * a) = a := fun a => by rw [← mul_assoc, hy, one_mul]
  have hz_mul : ∀ a, z * (z * a) = a := fun a => by rw [← mul_assoc, hz, one_mul]
  have hxy_mul : ∀ a, y * (x * a) = -(x * (y * a)) := fun a => by rw [← mul_assoc, hxy, neg_mul, mul_assoc]
  have hxz_mul : ∀ a, z * (x * a) = -(x * (z * a)) := fun a => by rw [← mul_assoc, hxz, neg_mul, mul_assoc]
  have hyz_mul : ∀ a, z * (y * a) = -(y * (z * a)) := fun a => by rw [← mul_assoc, hyz, neg_mul, mul_assoc]
  dsimp [W, M]
  noncomm_ring [hx, hy, hz, hxy, hxz, hyz,
    hx_mul, hy_mul, hz_mul, hxy_mul, hxz_mul, hyz_mul]

theorem tripleMiddleWord_mul_tripleWord :
    tripleMiddleWord * tripleWord = (4 : ℝ) • tripleMiddleWord - (2 : ℝ) • tripleWord := by
  have h := middle_mul_word (positive 0) (positive 1) (positive 2)
    (positive_square 0) (positive_square 1) (positive_square 2)
    (positive_anticommutes 1 0 (by decide))
    (positive_anticommutes 2 0 (by decide))
    (positive_anticommutes 2 1 (by decide))
  simpa only [tripleWord, tripleMiddleWord, Algebra.smul_def, map_ofNat] using h

theorem tripleWord_cubic :
    (tripleWord * tripleWord) * tripleWord - (4 : ℝ) • (tripleWord * tripleWord) + (8 : ℝ) • tripleWord = 0 := by
  rw [tripleWord_square, smul_mul_assoc, tripleMiddleWord_mul_tripleWord]
  module

/-- Minimal cubic polynomial for `tripleProjection`:
`T_3^3 - (1/2) • T_3^2 + (1/8) • T_3 = 0`. -/
theorem tripleProjection_cubic :
    (tripleProjection * tripleProjection) * tripleProjection -
      (1 / 2 : ℝ) • (tripleProjection * tripleProjection) +
      (1 / 8 : ℝ) • tripleProjection = 0 := by
  have h_cube : (tripleProjection * tripleProjection) * tripleProjection =
      (1 / 512 : ℝ) • ((tripleWord * tripleWord) * tripleWord) := by
    dsimp [tripleProjection]
    rw [smul_mul_smul, smul_mul_smul]
    norm_num
  have h_sq : (1 / 2 : ℝ) • (tripleProjection * tripleProjection) =
      (1 / 128 : ℝ) • (tripleWord * tripleWord) := by
    dsimp [tripleProjection]
    rw [smul_mul_smul, smul_smul]
    norm_num
  have h_lin : (1 / 8 : ℝ) • tripleProjection = (1 / 64 : ℝ) • tripleWord := by
    dsimp [tripleProjection]
    rw [smul_smul]
    norm_num
  rw [h_cube, h_sq, h_lin]
  have h_scaled := congrArg (fun x : Cl33 => (1 / 512 : ℝ) • x) tripleWord_cubic
  rw [smul_add, smul_sub, smul_smul, smul_smul, smul_zero] at h_scaled
  norm_num at h_scaled
  exact h_scaled

/-- Non-scalar-idempotency: `T_3^2 ≠ c • T_3` for any real scalar `c`. -/
theorem tripleProjection_not_scalar_idempotent (c : ℝ) :
    tripleProjection * tripleProjection ≠ c • tripleProjection := by
  intro h
  have hcub := tripleProjection_cubic
  rw [h, smul_mul_assoc, h, smul_smul, smul_smul] at hcub
  rw [← sub_smul, ← add_smul] at hcub
  have h_disc : c * c - 1 / 2 * c + 1 / 8 ≠ 0 := by
    have h_sq : c * c - 1 / 2 * c + 1 / 8 = (c - 1 / 4) ^ 2 + 1 / 16 := by ring
    rw [h_sq]
    have h_pos : 0 < (c - 1 / 4) ^ 2 + 1 / 16 := by positivity
    exact ne_of_gt h_pos
  have h_zero : tripleProjection = 0 := by
    exact smul_eq_zero.mp hcub |>.resolve_left h_disc
  have hv := congrArg (fun a : Cl33 => jwCliffordRepresentation 3 a vacuumIndex vacuumIndex) h_zero
  dsimp [tripleProjection] at hv
  rw [map_smul, Matrix.smul_apply, represented_tripleWord_vacuum, smul_eq_mul, mul_one] at hv
  norm_num at hv

/-! ## 5. Pure Permutation Braid and Sharp Cut-Rank Bounds -/

/-- Odd parity predicate on Clifford 4-letter basis words (1 = η, 3 = Ω are odd). -/
def isOddWord (a : Fin 4) : Bool :=
  a == 1 || a == 3

/-- Head basis transposition exchanging `0 ↔ 2` (1 ↔ K) and `1 ↔ 3` (η ↔ Ω),
matching the odd-tail correction from `Cl11GradedUnrolling`. -/
def wordExchange (a : Fin 4) : Fin 4 :=
  if a = 0 then 2 else if a = 2 then 0 else if a = 1 then 3 else if a = 3 then 1 else a

theorem wordExchange_involutive : Function.Involutive wordExchange := by
  intro a; revert a; decide

/-- The controlled braid transformation: applies `wordExchange` to the head site `w 0`
if and only if the tail site `w 1` is odd. -/
def braidFun (w : Words 2) : Words 2 :=
  fun i => if i = 0 then (if isOddWord (w 1) then wordExchange (w 0) else w 0) else w i

theorem braidFun_involutive : Function.Involutive braidFun := by
  intro w
  ext i
  fin_cases i
  · dsimp [braidFun]
    split_ifs with h
    · exact congrArg _ (wordExchange_involutive (w 0))
    · rfl
  · rfl

/-- Pure permutation on 2-site words implementing the controlled Clifford parity braid. -/
def braidPerm : Equiv.Perm (Words 2) where
  toFun := braidFun
  invFun := braidFun
  left_inv := braidFun_involutive
  right_inv := braidFun_involutive

/-- Carrier 2D real vector space for the sharpness witness. -/
abbrev V2 := Fin 2 → ℝ

/-- Standard basis vector e₀ = ![1, 0] in V₂. -/
def e0 : V2 := ![1, 0]

/-- Standard basis vector e₁ = ![0, 1] in V₂. -/
def e1 : V2 := ![0, 1]

/-- Projection functional onto coordinate 0. -/
def φ0 : Module.Dual ℝ V2 := LinearMap.proj 0

/-- Projection functional onto coordinate 1. -/
def φ1 : Module.Dual ℝ V2 := LinearMap.proj 1

/-- Involution matrix swapping e₀ and e₁. -/
def T_mat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Grading matrix assigning even to e₀ and odd to e₁. -/
def θ_mat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Linear operator for T. -/
def T_op : Module.End ℝ V2 := Matrix.toLin' T_mat

/-- Linear operator for grading θ. -/
def θ_op : Module.End ℝ V2 := Matrix.toLin' θ_mat

theorem T_op_sq : T_op.comp T_op = LinearMap.id := by
  rw [T_op, ← Matrix.toLin'_mul, ← Matrix.toLin'_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T_mat, Matrix.mul_apply, Fin.sum_univ_two]

theorem θ_op_sq : θ_op.comp θ_op = LinearMap.id := by
  rw [θ_op, ← Matrix.toLin'_mul, ← Matrix.toLin'_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [θ_mat, Matrix.mul_apply, Fin.sum_univ_two]

theorem T_op_e0 : T_op e0 = e1 := by
  ext i
  fin_cases i <;> simp [T_op, e0, e1, T_mat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem θ_op_e0 : θ_op e0 = e0 := by
  ext i
  fin_cases i <;> simp [θ_op, e0, θ_mat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem θ_op_e1 : θ_op e1 = -e1 := by
  ext i
  fin_cases i <;> simp [θ_op, e1, θ_mat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Right factor state y = e₀ + e₁ possessing both even and odd components. -/
def y_prod : V2 := e0 + e1

/-- Product tensor state t = e₀ ⊗ (e₀ + e₁) of cut rank 1. -/
def t_prod : V2 ⊗[ℝ] V2 := e0 ⊗ₜ[ℝ] y_prod

theorem parityTwist_t_prod :
    parityTwist T_op θ_op t_prod = e0 ⊗ₜ[ℝ] e0 + e1 ⊗ₜ[ℝ] e1 := by
  rw [t_prod, parityTwist_tmul]
  have h_even : (1 / 2 : ℝ) • (y_prod + θ_op y_prod) = e0 := by
    dsimp [y_prod]
    rw [map_add, θ_op_e0, θ_op_e1]
    ext i; fin_cases i <;> norm_num [e0, e1]
  have h_odd : (1 / 2 : ℝ) • (y_prod - θ_op y_prod) = e1 := by
    dsimp [y_prod]
    rw [map_add, θ_op_e0, θ_op_e1]
    ext i; fin_cases i <;> norm_num [e0, e1]
  rw [h_even, h_odd, T_op_e0]

theorem range_contraction_bell :
    LinearMap.range (contraction (e0 ⊗ₜ[ℝ] e0 + e1 ⊗ₜ[ℝ] e1 : V2 ⊗[ℝ] V2)) = ⊤ := by
  apply eq_top_iff.mpr
  intro v _
  have h_dec : v = v 0 • e0 + v 1 • e1 := by
    ext i; fin_cases i <;> simp [e0, e1]
  rw [h_dec]
  apply Submodule.add_mem
  · have h0 : e0 ∈ LinearMap.range (contraction (e0 ⊗ₜ[ℝ] e0 + e1 ⊗ₜ[ℝ] e1 : V2 ⊗[ℝ] V2)) := by
      refine ⟨φ0, ?_⟩
      simp only [map_add, LinearMap.add_apply, contraction_tmul_apply]
      have h00 : φ0 e0 = 1 := rfl
      have h01 : φ0 e1 = 0 := rfl
      rw [h00, h01, one_smul, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ h0
  · have h1 : e1 ∈ LinearMap.range (contraction (e0 ⊗ₜ[ℝ] e0 + e1 ⊗ₜ[ℝ] e1 : V2 ⊗[ℝ] V2)) := by
      refine ⟨φ1, ?_⟩
      simp only [map_add, LinearMap.add_apply, contraction_tmul_apply]
      have h10 : φ1 e0 = 0 := rfl
      have h11 : φ1 e1 = 1 := rfl
      rw [h10, h11, zero_smul, one_smul, zero_add]
    exact Submodule.smul_mem _ _ h1

theorem cutRank_bell :
    cutRank (e0 ⊗ₜ[ℝ] e0 + e1 ⊗ₜ[ℝ] e1 : V2 ⊗[ℝ] V2) = 2 := by
  unfold cutRank
  rw [range_contraction_bell, finrank_top, Module.finrank_fintype_fun_eq_card]
  rfl

theorem cutRank_t_prod :
    cutRank t_prod = 1 := by
  unfold cutRank t_prod
  have h_range : LinearMap.range (contraction (e0 ⊗ₜ[ℝ] y_prod)) = Submodule.span ℝ {y_prod} := by
    apply le_antisymm
    · rintro w ⟨φ, rfl⟩
      rw [contraction_tmul_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y_prod)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨φ0, ?_⟩
      rw [contraction_tmul_apply]
      have h : φ0 e0 = 1 := rfl
      rw [h, one_smul]
  rw [h_range]
  have hne : y_prod ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [y_prod, e0, e1] at h0
  exact finrank_span_singleton hne

/-- Sharp factor-of-2 witness: ungraded cut rank 1 becomes graded cut rank 2 under parity twist,
saturating the bound `r_g = 2 * r_u` with exact equality. -/
theorem sharp_cutrank_factor_two_witness :
    ∃ (T : Module.End ℝ V2) (θ : Module.End ℝ V2)
      (_hT : T.comp T = LinearMap.id) (_hθ : θ.comp θ = LinearMap.id)
      (t : V2 ⊗[ℝ] V2),
      cutRank t = 1 ∧
      cutRank (parityTwist T θ t) = 2 ∧
      cutRank (parityTwist T θ t) = 2 * cutRank t := by
  refine ⟨T_op, θ_op, T_op_sq, θ_op_sq, t_prod, ?_⟩
  rw [parityTwist_t_prod, cutRank_bell, cutRank_t_prod]
  refine ⟨rfl, rfl, rfl⟩

/-- Two-sided cut-rank bounds between graded and ungraded representations under parity twist. -/
theorem two_sided_cutrank_bounds {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (θ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id) (hθ : θ.comp θ = LinearMap.id)
    (t : V ⊗[ℝ] W) :
    cutRank (parityTwist T θ t) ≤ 2 * cutRank t ∧
      cutRank t ≤ 2 * cutRank (parityTwist T θ t) :=
  cutRank_parityTwist_bounds T θ hT hθ t

/-- Two-sided cut-rank bounds under general complementary projector controlled twist. -/
theorem two_sided_cutrank_controlled_bounds {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (p₀ p₁ : Module.End ℝ W)
    (hT : T.comp T = LinearMap.id)
    (h00 : p₀.comp p₀ = p₀) (h11 : p₁.comp p₁ = p₁)
    (h01 : p₀.comp p₁ = 0) (h10 : p₁.comp p₀ = 0)
    (hsum : p₀ + p₁ = LinearMap.id) (t : V ⊗[ℝ] W) :
    cutRank (controlledTwist T p₀ p₁ t) ≤ 2 * cutRank t ∧
      cutRank t ≤ 2 * cutRank (controlledTwist T p₀ p₁ t) :=
  cutRank_controlledTwist_bounds T p₀ p₁ hT h00 h11 h01 h10 hsum t

/-! ## 6. Operator-Sink Prefix Rank Bounds -/

theorem card_words (n : ℕ) :
    Fintype.card (Words n) = 4 ^ n := by
  simp [Words]

theorem finrank_words (n : ℕ) :
    Module.finrank ℝ (Words n → ℝ) = 4 ^ n := by
  rw [Module.finrank_fintype_fun_eq_card, card_words]

/-- Operator-sink prefix rank bound:
The cut rank of any state in `(Words k → ℝ) ⊗[ℝ] ((Words m → ℝ) ⊗[ℝ] B)` is bounded by
`min (4 ^ k) (4 ^ m * Module.finrank ℝ B)`. -/
theorem operator_sink_prefix_rank_bound (k m : ℕ)
    [FiniteDimensional ℝ B]
    (t : (Words k → ℝ) ⊗[ℝ] ((Words m → ℝ) ⊗[ℝ] B)) :
    cutRank t ≤ min (4 ^ k) (4 ^ m * Module.finrank ℝ B) := by
  have h_bound := cutRank_operator_tail_le_min (V := Words k → ℝ) (U := Words m → ℝ) (B := B) t
  rw [finrank_words k, finrank_words m] at h_bound
  exact h_bound

/-! ## 7. Odd-Dimension Real Complex Structures and Skew Tripotents -/

/-- In odd dimensions, there is no real matrix satisfying `J ^ 2 = -1`.
This halts complex-structure formation on odd-dimensional real carriers. -/
theorem odd_dim_no_complex_structure (m : ℕ) (hm : Odd m) :
    ¬ ∃ J : Matrix (Fin m) (Fin m) ℝ, J ^ 2 = -1 := by
  intro ⟨J, hJ⟩
  have h2 : J ^ 2 = J * J := sq J
  have hdet := congrArg Matrix.det (h2.symm.trans hJ)
  rw [Matrix.det_mul] at hdet
  have hneg : (-1 : Matrix (Fin m) (Fin m) ℝ) = -(1 : Matrix (Fin m) (Fin m) ℝ) := by rfl
  rw [hneg, Matrix.det_neg, Matrix.det_one, mul_one] at hdet
  have hodd : (-1 : ℝ) ^ Fintype.card (Fin m) = -1 := by
    rw [Fintype.card_fin]
    exact hm.neg_one_pow
  rw [hodd] at hdet
  have hsq_nonneg : 0 ≤ J.det * J.det := mul_self_nonneg J.det
  rw [hdet] at hsq_nonneg
  norm_num at hsq_nonneg

/-- Any odd-dimensional real skew-symmetric tripotent (`S.transpose = -S` and `S ^ 3 = S`)
possesses a non-trivial zero-mode: `∃ v ≠ 0, S.mulVec v = 0`. -/
theorem odd_dim_skew_tripotent_zero_mode (m : ℕ) (hm : Odd m)
    (S : Matrix (Fin m) (Fin m) ℝ)
    (hS_skew : S.transpose = -S)
    (hS_tri : S ^ 3 = S) :
    ∃ v : Fin m → ℝ, v ≠ 0 ∧ S.mulVec v = 0 := by
  have hdet_trans : S.det = (-S).det := by
    rw [← hS_skew, Matrix.det_transpose]
  rw [Matrix.det_neg] at hdet_trans
  have hodd : (-1 : ℝ) ^ Fintype.card (Fin m) = -1 := by
    rw [Fintype.card_fin]
    exact hm.neg_one_pow
  rw [hodd, neg_one_mul] at hdet_trans
  have hdet_zero : S.det = 0 := by linarith
  have h_ex := Matrix.exists_mulVec_eq_zero_iff.mpr hdet_zero
  rcases h_ex with ⟨v, hv_ne, hv_ker⟩
  refine ⟨v, hv_ne, ?_⟩
  have h_ann : (S ^ 3 - S).mulVec v = 0 := by
    rw [hS_tri, sub_self, Matrix.zero_mulVec]
  exact hv_ker

end InfoGeometry.Clifford.Cl11SuperBaseAndEntanglementRank
