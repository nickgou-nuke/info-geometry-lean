import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs

/-!
# Local two-by-two block insertion into rational matrices

This definition inserts the entries of a two-by-two block at two selected
indices and uses the identity on all other diagonal coordinates. It does not
define a braid representation or prove multiplicativity of the insertion map.
-/

namespace InfoGeometry.Topology.Delaunay

open Matrix

noncomputable def embedBlock₂ (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) : Matrix (Fin d) (Fin d) ℚ :=
  λ i j =>
    if i = a then
      if j = a then block 0 0
      else if j = b then block 0 1
      else 0
    else if i = b then
      if j = a then block 1 0
      else if j = b then block 1 1
      else 0
    else if i = j then 1 else 0

@[simp]
theorem embedBlock₂_apply_aa (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ) (a b : Fin d) :
    embedBlock₂ d block a b a a = block 0 0 := by
  simp [embedBlock₂]

@[simp]
theorem embedBlock₂_apply_ab (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b a b = block 0 1 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

@[simp]
theorem embedBlock₂_apply_ba (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b b a = block 1 0 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

@[simp]
theorem embedBlock₂_apply_bb (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d block a b b b = block 1 1 := by
  have hba : b ≠ a := Ne.symm hab
  simp [embedBlock₂, hba]

theorem embedBlock₂_apply_other (d : ℕ) (block : Matrix (Fin 2) (Fin 2) ℚ)
    (a b i j : Fin d) (hia : i ≠ a) (hib : i ≠ b) :
    embedBlock₂ d block a b i j = if i = j then 1 else 0 := by
  simp [embedBlock₂, hia, hib]

/-- Inserting the 2×2 identity matrix at distinct indices `a ≠ b` yields the `d × d` identity matrix. -/
theorem embedBlock₂_one (d : ℕ) (a b : Fin d) (hab : a ≠ b) :
    embedBlock₂ d 1 a b = 1 := by
  ext i j
  dsimp [embedBlock₂]
  split_ifs <;> simp_all [Matrix.one_apply] <;> tauto

end InfoGeometry.Topology.Delaunay
