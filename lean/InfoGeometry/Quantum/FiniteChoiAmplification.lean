import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Quantum.FiniteChoiAmplification

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ
local notation "BipMat" => Matrix (n × n) (n × n) ℂ

abbrev MatrixMap (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ

def matrixUnit (i j : n) : Mat :=
  fun k l => if k = i ∧ l = j then 1 else 0

def choiMatrix (E : MatrixMap n) : BipMat :=
  fun (i, k) (j, l) => E (matrixUnit k l) i j

def amplify (m : Type*) [Fintype m] [DecidableEq m]
    (E : MatrixMap n) :
    Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun X := fun (p, i) (q, j) =>
    E (fun a b => X (p, a) (q, b)) i j
  map_add' X Y := by
    ext ⟨p, i⟩ ⟨q, j⟩
    change E (fun a b => X (p, a) (q, b) + Y (p, a) (q, b)) i j = _
    rw [show (fun a b => X (p, a) (q, b) + Y (p, a) (q, b)) =
        (fun a b => X (p, a) (q, b)) + (fun a b => Y (p, a) (q, b)) by rfl]
    rw [E.map_add]
    rfl
  map_smul' c X := by
    ext ⟨p, i⟩ ⟨q, j⟩
    change E (fun a b => c * X (p, a) (q, b)) i j = _
    rw [show (fun a b => c * X (p, a) (q, b)) =
        c • (fun a b => X (p, a) (q, b)) by rfl]
    rw [E.map_smul]
    rfl

@[simp] theorem amplify_apply (m : Type*) [Fintype m] [DecidableEq m]
    (E : MatrixMap n) (X : Matrix (m × n) (m × n) ℂ)
    (p q : m) (i j : n) :
    amplify m E X (p, i) (q, j) = E (fun a b => X (p, a) (q, b)) i j := rfl

def ChoiPositive (E : MatrixMap n) : Prop :=
  (choiMatrix E).PosSemidef

def CompleteChoiPositive (E : MatrixMap n) : Prop :=
  ∀ (m : Type*) [Fintype m] [DecidableEq m],
    (choiMatrix (amplify m E)).PosSemidef

def krausTerm (V X : Mat) : Mat := V * X * star V

def krausChannel {ι : Type*} [Fintype ι]
    (V : ι → Mat) : MatrixMap n where
  toFun X := ∑ r, krausTerm (V r) X
  map_add' X Y := by
    simp [krausTerm, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp [krausTerm, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]

def blockKraus (m : Type*) [Fintype m] [DecidableEq m]
    {ι : Type*} (V : ι → Mat) (r : ι) :
    Matrix (m × n) (m × n) ℂ :=
  fun (p, i) (q, j) => if p = q then V r i j else 0

def blockKrausChannel (m : Type*) [Fintype m] [DecidableEq m]
    {ι : Type*} [Fintype ι] (V : ι → Mat) :
    Matrix (m × n) (m × n) ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ :=
  { toFun := fun X => ∑ r, (blockKraus m V r) * X * star (blockKraus m V r)
    map_add' := by
      intro X Y
      simp [mul_add, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c X
      simp [smul_mul_assoc, mul_smul_comm, Finset.smul_sum] }

def choiMatrixAmplified (m : Type*) [Fintype m] [DecidableEq m]
    (E : MatrixMap n) :
    Matrix ((m × n) × (m × n)) ((m × n) × (m × n)) ℂ :=
  choiMatrix (amplify m E)

end InfoGeometry.Quantum.FiniteChoiAmplification

end noncomputable section
