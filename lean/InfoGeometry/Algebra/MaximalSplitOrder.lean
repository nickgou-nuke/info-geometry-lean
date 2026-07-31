import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Int.ModEq

/-!
# Maximal Split Order of Zorn Matrices

This module formally defines the van der Blij-Springer maximal split order
`O_split` for Zorn matrices. This order is essential for constructing the 
$E_{8(8)}$ lattice algebraically.

A rational Zorn matrix $X$ belongs to the maximal split order if:
1. Its components $a, b, v_i, w_i$ are half-integers (i.e. of the form $z / 2$ for $z \in \mathbb{Z}$).
2. The integers $2a, 2b$ and $2v_i$ satisfy the congruence condition:
   $(2a - 2b) \equiv (2v_0 + 2v_1 + 2v_2) \pmod 4$.

We define this property and bundle it into a rigorous `Submodule ℤ (ZornVectorMatrix ℚ)`.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

/--
The condition for a rational Zorn matrix to belong to the Maximal Split Order (the $E_8$ lattice).
-/
def isMaximalSplitOrder (X : ZornVectorMatrix ℚ) : Prop :=
  ∃ (za zb : ℤ) (zv zw : Fin 3 → ℤ),
    X.a = (za : ℚ) / 2 ∧
    X.b = (zb : ℚ) / 2 ∧
    (∀ i, X.v i = (zv i : ℚ) / 2) ∧
    (∀ i, X.w i = (zw i : ℚ) / 2) ∧
    (za - zb) ≡ (zv 0 + zv 1 + zv 2) [ZMOD 4]

lemma zero_isMaximalSplitOrder : isMaximalSplitOrder (zero : ZornVectorMatrix ℚ) := by
  use 0, 0, (fun _ => 0), (fun _ => 0)
  dsimp [zero]
  norm_num

lemma add_isMaximalSplitOrder {X Y : ZornVectorMatrix ℚ} 
    (hX : isMaximalSplitOrder X) (hY : isMaximalSplitOrder Y) : 
    isMaximalSplitOrder (add X Y) := by
  rcases hX with ⟨xa, xb, xv, xw, ha, hb, hv, hw, hcongX⟩
  rcases hY with ⟨ya, yb, yv, yw, ga, gb, gv, gw, hcongY⟩
  use (xa + ya), (xb + yb), (fun i => xv i + yv i), (fun i => xw i + yw i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [add]; rw [ha, ga]; push_cast; ring
  · dsimp [add]; rw [hb, gb]; push_cast; ring
  · intro i; dsimp [add]; rw [hv i, gv i]; push_cast; ring
  · intro i; dsimp [add]; rw [hw i, gw i]; push_cast; ring
  · have h1 : (xa + ya - (xb + yb)) = (xa - xb) + (ya - yb) := by ring
    have h2 : ((xv 0 + yv 0) + (xv 1 + yv 1) + (xv 2 + yv 2)) = 
      (xv 0 + xv 1 + xv 2) + (yv 0 + yv 1 + yv 2) := by ring
    rw [h1, h2]
    exact Int.ModEq.add hcongX hcongY

lemma smul_isMaximalSplitOrder (z : ℤ) {X : ZornVectorMatrix ℚ} (hX : isMaximalSplitOrder X) : 
    isMaximalSplitOrder (smul (z : ℚ) X) := by
  rcases hX with ⟨xa, xb, xv, xw, ha, hb, hv, hw, hcongX⟩
  use (z * xa), (z * xb), (fun i => z * xv i), (fun i => z * xw i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [smul]; rw [ha]; push_cast; ring
  · dsimp [smul]; rw [hb]; push_cast; ring
  · intro i; dsimp [smul]; rw [hv i]; push_cast; ring
  · intro i; dsimp [smul]; rw [hw i]; push_cast; ring
  · have h1 : (z * xa - z * xb) = z * (xa - xb) := by ring
    have h2 : (z * xv 0 + z * xv 1 + z * xv 2) = z * (xv 0 + xv 1 + xv 2) := by ring
    rw [h1, h2]
    exact Int.ModEq.mul_left z hcongX

end InfoGeometry.Algebra.ZornVectorMatrix
