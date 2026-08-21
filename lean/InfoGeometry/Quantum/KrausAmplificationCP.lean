import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Quantum.KrausAmplification

open Matrix
open scoped ComplexOrder

variable {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

local notation "Mat" => Matrix n n ℂ
local notation "AmpMat" => Matrix (r × n) (r × n) ℂ

def blockK (V : Mat) : AmpMat :=
  fun (p, i) (q, j) => if p = q then V i j else 0

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
