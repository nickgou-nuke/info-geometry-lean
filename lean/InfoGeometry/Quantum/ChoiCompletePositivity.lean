import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

def krausMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) : MatrixMap (n := n) where
  toFun X := ∑ a, V a * X * star (V a)
  map_add' X Y := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp [mul_assoc, mul_left_comm, mul_comm]

private theorem kraus_term_matrixUnit_apply
    (V : Mat) (i j k l : n) :
    (V * matrixUnit i j * star V) k l = V k i * star (V l j) := by
  dsimp [matrixUnit, Matrix.mul_apply, Matrix.star_apply]
  have h_inner (r : n) : (∑ c : n, V k c * (if c = i ∧ r = j then (1 : ℂ) else 0)) =
      if r = j then V k i else 0 := by
    rw [Finset.sum_eq_single i]
    · simp only [true_and]
      split_ifs <;> simp
    · intro c _ hneq
      have : (c = i ∧ r = j) = False := by simp [hneq]
      simp [this]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  
  have h_outer : (∑ r : n, (∑ c : n, V k c * (if c = i ∧ r = j then (1 : ℂ) else 0)) * star (V l r)) =
      V k i * star (V l j) := by
    calc
      (∑ r : n, (∑ c : n, V k c * (if c = i ∧ r = j then (1 : ℂ) else 0)) * star (V l r))
        = ∑ r : n, (if r = j then V k i else 0) * star (V l r) := by
          refine Finset.sum_congr rfl (fun r _ => by rw [h_inner r])
      _ = V k i * star (V l j) := by
        rw [Finset.sum_eq_single j]
        · simp only [if_true]
        · intro r _ hneq
          simp only [if_neg hneq, zero_mul]
        · intro hj
          exact False.elim (hj (Finset.mem_univ j))
  
  exact h_outer

/-- The finite Kraus Choi certificate, written as a sum of rank-one terms. -/
def krausChoi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
    ∑ r, rankOne (fun p => V r p.2 p.1)

theorem choiMatrix_krausMap_eq_krausChoi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) :
    choiMatrix (krausMap V) = krausChoi V := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [choiMatrix, krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, krausChoi, rankOne]
  apply Finset.sum_congr rfl
  intro a ha
  exact kraus_term_matrixUnit_apply (V a) i j k l

theorem krausChoi_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) :
    (krausChoi V).PosSemidef := by
  unfold krausChoi
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (n × n) (n × n) ℂ).PosSemidef)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Matrix.PosSemidef.add (rankOne_posSemidef _) ih

/-- The Choi matrix of every finite Kraus map is positive semidefinite. -/
theorem choiMatrix_krausMap_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) :
    (choiMatrix (krausMap V)).PosSemidef := by
  rw [choiMatrix_krausMap_eq_krausChoi V]
  exact krausChoi_posSemidef V

/-- Choi positivity of a finite matrix map. -/
def ChoiPositive (E : MatrixMap (n := n)) : Prop :=
  (choiMatrix E).PosSemidef

/-! The following finite amplification makes the Choi--Jamiołkowski formula
literal at the level of matrix entries. -/

def tensorAmplification (E : MatrixMap (n := n))
    (X : Matrix (n × n) (n × n) ℂ) : Matrix (n × n) (n × n) ℂ :=
  fun (i, k) (j, l) =>
    E (fun a b => X (i, a) (j, b)) k l

theorem choiMatrix_eq_tensorAmplification_rankOne
    (E : MatrixMap (n := n)) :
    choiMatrix E = tensorAmplification E (rankOne maximallyEntangled) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  dsimp [choiMatrix, tensorAmplification]
  have hslice :
      (fun a b => rankOne maximallyEntangled (i, a) (j, b)) =
        matrixUnit i j := by
    funext a b
    dsimp [rankOne, maximallyEntangled, matrixUnit]
    split_ifs with h1 h2 h3 <;> simp_all
  rw [hslice]

theorem krausMap_choiPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) :
  ChoiPositive (krausMap V) :=
  choiMatrix_krausMap_posSemidef V

theorem krausMap_tensorAmplification_rankOne_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) :
    (tensorAmplification (krausMap V) (rankOne maximallyEntangled)).PosSemidef := by
  rw [← choiMatrix_eq_tensorAmplification_rankOne]
  exact choiMatrix_krausMap_posSemidef V

theorem tensorAmplification_rankOne_posSemidef_of_choiPositive
    (E : MatrixMap (n := n)) (hE : ChoiPositive E) :
    (tensorAmplification E (rankOne maximallyEntangled)).PosSemidef := by
  rw [← choiMatrix_eq_tensorAmplification_rankOne]
  exact hE

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
