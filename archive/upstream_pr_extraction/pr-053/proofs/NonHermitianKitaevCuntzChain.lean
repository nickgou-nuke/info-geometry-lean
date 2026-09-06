import Mathlib

/-!
# Non-Hermitian Kitaev--Cuntz Chain: Finite Edge-Mode Core

A finite algebraic core for the proposed applied simulation layer.
The numerical script builds long non-Hermitian SSH/Kitaev-like chains; this Lean
module records the exact local mechanism behind protected zero modes:

* a chiral/non-Hermitian two-site block `[[0,q],[r,0]]`;
* one-sided Cuntz/shift limit `r=0`, where the left edge vector is an exact zero
  mode and the block is nilpotent;
* determinant/eigenvalue obstruction `det = -q r`, so zero modes occur when one
  chiral coupling is cut.
-/

noncomputable section

open Matrix Complex

namespace InfoGeometry.GrandUnification.NonHermitianKitaevCuntzChain

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev Col2C := Matrix (Fin 2) (Fin 1) ℂ

/-- Chiral two-site non-Hermitian Majorana/SSH block. -/
def chiralBlock (q r : ℂ) : M2C :=
  !![0, q; r, 0]

/-- Left edge basis column. -/
def leftEdge : Col2C :=
  !![1; 0]

/-- Right edge basis column. -/
def rightEdge : Col2C :=
  !![0; 1]

/-- One-sided Cuntz/skin block: only the right shift coupling remains. -/
def cuntzShiftBlock (q : ℂ) : M2C :=
  chiralBlock q 0

/-- Opposite one-sided block. -/
def oppositeShiftBlock (r : ℂ) : M2C :=
  chiralBlock 0 r

/-- Determinant of the chiral block. -/
theorem chiralBlock_det (q r : ℂ) :
    (chiralBlock q r).det = - q * r := by
  simp [chiralBlock, Matrix.det_fin_two]

/-- Square of the chiral block is `qr` on the diagonal. -/
theorem chiralBlock_sq (q r : ℂ) :
    chiralBlock q r * chiralBlock q r = (q * r) • (1 : M2C) := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [chiralBlock]
    · simp [chiralBlock]
  · fin_cases j
    · simp [chiralBlock]
    · simp [chiralBlock]
      ring

/-- The one-sided Cuntz/skin block is nilpotent. -/
theorem cuntzShiftBlock_sq (q : ℂ) :
    cuntzShiftBlock q * cuntzShiftBlock q = (0 : M2C) := by
  rw [cuntzShiftBlock, chiralBlock_sq]
  simp

/-- In the one-sided block, the left boundary mode is pinned exactly at zero. -/
theorem leftEdge_zero_mode (q : ℂ) :
    cuntzShiftBlock q * leftEdge = (0 : Col2C) := by
  ext i j
  fin_cases i
  · fin_cases j
    simp [cuntzShiftBlock, chiralBlock, leftEdge]
  · fin_cases j
    simp [cuntzShiftBlock, chiralBlock, leftEdge]

/-- In the opposite one-sided block, the right boundary mode is pinned exactly at zero. -/
theorem rightEdge_zero_mode (r : ℂ) :
    oppositeShiftBlock r * rightEdge = (0 : Col2C) := by
  ext i j
  fin_cases i
  · fin_cases j
    simp [oppositeShiftBlock, chiralBlock, rightEdge]
  · fin_cases j
    simp [oppositeShiftBlock, chiralBlock, rightEdge]

/-- The one-sided block has zero determinant, i.e. an exact exceptional/null sector. -/
theorem cuntzShiftBlock_det_zero (q : ℂ) :
    (cuntzShiftBlock q).det = 0 := by
  simp [cuntzShiftBlock, chiralBlock_det]

/-- Consolidated finite edge-mode package. -/
theorem nonhermitian_kitaev_cuntz_chain_synthesis :
    (∀ q r : ℂ, (chiralBlock q r).det = - q * r) ∧
    (∀ q r : ℂ, chiralBlock q r * chiralBlock q r = (q * r) • (1 : M2C)) ∧
    (∀ q : ℂ, cuntzShiftBlock q * cuntzShiftBlock q = (0 : M2C)) ∧
    (∀ q : ℂ, cuntzShiftBlock q * leftEdge = (0 : Col2C)) ∧
    (∀ r : ℂ, oppositeShiftBlock r * rightEdge = (0 : Col2C)) ∧
    (∀ q : ℂ, (cuntzShiftBlock q).det = 0) := by
  constructor
  · intro q r
    exact chiralBlock_det q r
  constructor
  · intro q r
    exact chiralBlock_sq q r
  constructor
  · intro q
    exact cuntzShiftBlock_sq q
  constructor
  · intro q
    exact leftEdge_zero_mode q
  constructor
  · intro r
    exact rightEdge_zero_mode r
  · intro q
    exact cuntzShiftBlock_det_zero q

end InfoGeometry.GrandUnification.NonHermitianKitaevCuntzChain
