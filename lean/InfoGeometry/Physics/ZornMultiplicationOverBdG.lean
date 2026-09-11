import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NCG.NoncommutativeChiralZornAlgebra
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace InfoGeometry.Physics.PalatialTwistor

open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

/-!
# Zorn multiplication over the BdG coefficient algebra

This module is a bridge to the canonical noncommutative Zorn carrier.  The
coefficient type is `BdGBlock ℚ`, whose multiplication is native Mathlib
matrix multiplication.  No associativity, alternativity, spinor structure,
or physical interpretation is added to the Zorn carrier here.
-/

abbrev BdGZornMatrix := NCZornElement (BdGBlock ℚ)

abbrev BdGBlockQ := BdGBlock ℚ

abbrev zornMul (X Y : BdGZornMatrix) : BdGZornMatrix :=
  NCZornElement.mul X Y

@[ext] theorem ncZorn_ext {X Y : NCZornElement A}
    (hnp : X.n_plus = Y.n_plus)
    (hnm : X.n_minus = Y.n_minus)
    (hsp : X.sigma_plus = Y.sigma_plus)
    (hsm : X.sigma_minus = Y.sigma_minus) :
    X = Y := by
  cases X
  cases Y
  simp_all

@[simp] theorem zornMul_eq_native (X Y : BdGZornMatrix) :
    zornMul X Y = X * Y :=
  rfl

theorem zorn_cross_self_red_eq_commutator
    (v : Fin 3 → BdGBlock ℚ) :
    NCZornElement.zornCross v v 0 =
      v 1 * v 2 - v 2 * v 1 := by
  rfl

theorem zorn_cross_self_green_eq_commutator
    (v : Fin 3 → BdGBlock ℚ) :
    NCZornElement.zornCross v v 1 =
      v 2 * v 0 - v 0 * v 2 := by
  rfl

theorem zorn_cross_self_blue_eq_commutator
    (v : Fin 3 → BdGBlock ℚ) :
    NCZornElement.zornCross v v 2 =
      v 0 * v 1 - v 1 * v 0 := by
  rfl

def matrixE12 : BdGBlockQ := !![0, 1; 0, 0]

def matrixE21 : BdGBlockQ := !![0, 0; 1, 0]

def commutatorColourVector : Fin 3 → BdGBlockQ
  | 0 => 0
  | 1 => matrixE12
  | 2 => matrixE21

theorem colourCross_self_red :
    NCZornElement.zornCross commutatorColourVector
      commutatorColourVector 0 = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [NCZornElement.zornCross, commutatorColourVector,
      matrixE12, matrixE21, Matrix.mul_apply, Fin.sum_univ_two]

theorem colourCross_self_red_ne_zero :
    NCZornElement.zornCross commutatorColourVector
      commutatorColourVector 0 ≠ 0 := by
  rw [colourCross_self_red]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num at h00

def singleColourEmbedding (c : Fin 3) (M : Matrix (Fin 2) (Fin 2) A) :
    NCZornElement A where
  n_plus := M 0 0
  n_minus := M 1 1
  sigma_plus := fun k => if k = c then M 0 1 else 0
  sigma_minus := fun k => if k = c then M 1 0 else 0

section CommutativeCoefficients

variable {C : Type*} [CommRing C]

theorem singleColourEmbedding_map_mul
    (c : Fin 3) (M N : Matrix (Fin 2) (Fin 2) C) :
    singleColourEmbedding c (M * N) =
      (singleColourEmbedding c M) * (singleColourEmbedding c N) := by
  change singleColourEmbedding c (M * N) =
    NCZornElement.mul (singleColourEmbedding c M)
      (singleColourEmbedding c N)
  fin_cases c
  all_goals
    apply ncZorn_ext
    · simp [singleColourEmbedding, NCZornElement.mul,
        NCZornElement.zornDot, NCZornElement.zornCross,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ac_rfl
    · simp [singleColourEmbedding, NCZornElement.mul,
        NCZornElement.zornDot, NCZornElement.zornCross,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ac_rfl
    · funext k; fin_cases k <;>
        simp [singleColourEmbedding, NCZornElement.mul,
          NCZornElement.zornDot, NCZornElement.zornCross,
          Matrix.mul_apply, Fin.sum_univ_two] <;> ac_rfl
    · funext k; fin_cases k <;>
        simp [singleColourEmbedding, NCZornElement.mul,
          NCZornElement.zornDot, NCZornElement.zornCross,
          Matrix.mul_apply, Fin.sum_univ_two] <;> ac_rfl

end CommutativeCoefficients

end InfoGeometry.Physics.PalatialTwistor
