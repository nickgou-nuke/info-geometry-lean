import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite Choi matrices and complete-positivity contracts

This owner fixes the finite matrix conventions for Choi certification.  It
does not silently identify Choi positivity with complete positivity; that
equivalence and its Kraus proof are separate obligations.
-/

noncomputable section

namespace InfoGeometry.Quantum.Choi

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ
local notation "Idx" => n × n

/-- The matrix unit `eᵢⱼ`. -/
def matrixUnit (i j : n) : Matrix n n ℂ :=
  fun k l => if k = i ∧ l = j then 1 else 0

/-- A finite complex-linear map on matrix observables. -/
abbrev MatrixMap := Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ

/-- Choi matrix, indexed by input and output matrix indices. -/
def choiMatrix (E : MatrixMap (n := n)) : Matrix (n × n) (n × n) ℂ :=
  fun (i, k) (j, l) => E (matrixUnit i j) k l

/-- The unnormalised maximally-entangled vector. -/
def maximallyEntangled : (n × n) → ℂ :=
  fun (i, k) => if i = k then 1 else 0

/-- Rank-one projector associated to a vector. -/
def rankOne (v : (n × n) → ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun a b => v a * star (v b)

theorem rankOne_posSemidef (v : (n × n) → ℂ) :
    (rankOne v).PosSemidef := by
  let C : Matrix (n × n) Unit ℂ := fun a _ => v a
  have hC : C * Cᴴ = rankOne v := by
    ext a b
    simp [C, rankOne, Matrix.mul_apply]
  rw [← hC]
  exact Matrix.posSemidef_self_mul_conjTranspose C

/-- The finite Kraus Choi certificate, written as a sum of rank-one terms. -/
def krausChoi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
    ∑ r, rankOne (fun p => V r p.2 p.1)

theorem krausChoi_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) :
    (krausChoi V).PosSemidef := by
  unfold krausChoi
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (n × n) (n × n) ℂ).PosSemidef)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Matrix.PosSemidef.add (rankOne_posSemidef _) ih

/-- Choi positivity of a finite matrix map. -/
def ChoiPositive (E : MatrixMap (n := n)) : Prop :=
  (choiMatrix E).PosSemidef

/-- Finite complete positivity: every matrix amplification preserves the
positive-semidefinite cone.  The amplification construction is intentionally
left as a separate owner because its index/type transport is nontrivial. -/
@[simp] theorem matrixUnit_apply (i j k l : n) :
    matrixUnit i j k l = if k = i ∧ l = j then 1 else 0 := rfl

@[simp] theorem choiMatrix_apply (E : MatrixMap (n := n))
    (i j k l : n) :
    choiMatrix E (i, k) (j, l) = E (matrixUnit i j) k l := rfl

@[simp] theorem maximallyEntangled_diag (i : n) :
    maximallyEntangled (i, i) = 1 := by simp [maximallyEntangled]

end InfoGeometry.Quantum.Choi

end noncomputable section
