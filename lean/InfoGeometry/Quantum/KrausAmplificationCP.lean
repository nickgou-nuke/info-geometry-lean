import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import InfoGeometry.Modular.ChoiCompletePositivity

noncomputable section

namespace InfoGeometry.Quantum.KrausAmplification

open Matrix
open scoped ComplexOrder

variable {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

local notation "Mat" => Matrix n n ℂ
local notation "AmpMat" => Matrix (r × n) (r × n) ℂ

def blockK (V : Mat) : AmpMat :=
  fun a b => if a.1 = b.1 then V a.2 b.2 else 0

def blockKDiag (V : Mat) : Matrix (n × r) (n × r) ℂ :=
  Matrix.blockDiagonal (fun _ : r => V)

theorem blockK_eq_reindex_blockDiagonal (V : Mat) :
    blockK (r := r) V =
      Matrix.reindex (Equiv.prodComm n r) (Equiv.prodComm n r)
        (blockKDiag (r := r) V) := by
  ext ⟨p, i⟩ ⟨q, j⟩
  rfl



@[simp] theorem blockK_apply (V : Mat) (a b : r × n) :
    blockK (r := r) V a b = if a.1 = b.1 then V a.2 b.2 else 0 := rfl

def block (X : AmpMat) (p q : r) : Mat :=
  fun i j => X (p, i) (q, j)

def amplification (E : Mat →ₗ[ℂ] Mat) : AmpMat →ₗ[ℂ] AmpMat where
  toFun X := fun a b => E (block X a.1 b.1) a.2 b.2
  map_add' X Y := by
    ext a b
    rw [show block (X + Y) a.1 b.1 = block X a.1 b.1 + block Y a.1 b.1 by
      ext i j
      rfl, E.map_add]
    rfl
  map_smul' c X := by
    ext a b
    rw [show block (c • X) a.1 b.1 = c • block X a.1 b.1 by
      ext i j
      rfl, E.map_smul]
    rfl

@[simp] theorem amplification_apply (E : Mat →ₗ[ℂ] Mat)
    (X : AmpMat) (a b : r × n) :
    amplification (r := r) E X a b = E (block X a.1 b.1) a.2 b.2 := rfl

def amplifiedKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) : AmpMat :=
  ∑ k, blockK (r := r) (V k) * X * (blockK (r := r) (V k))ᴴ

theorem amplifiedKraus_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Mat) (X : AmpMat) (hX : X.PosSemidef) :
    (amplifiedKraus (r := r) V X).PosSemidef := by
  unfold amplifiedKraus
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using (Matrix.PosSemidef.zero : (0 : AmpMat).PosSemidef)
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact Matrix.PosSemidef.add
        (Matrix.PosSemidef.mul_mul_conjTranspose_same hX _) ih

end InfoGeometry.Quantum.KrausAmplification

end noncomputable section
