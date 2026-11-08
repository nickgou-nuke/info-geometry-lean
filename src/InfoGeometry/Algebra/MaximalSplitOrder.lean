import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Maximal Split Order of Zorn Matrices

This module formally defines the van der Blij-Springer maximal split order
`O_split` for Zorn matrices. This order is essential for constructing the 
$E_{8(8)}$ lattice algebraically.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

/--
The mathematically exact condition for a rational Zorn matrix to belong to the Maximal Split Order (the $E_{8(8)}$ lattice).
Defined as a self-dual integral lattice:
1. Half-integer components.
2. Integer Trace.
3. Integer Norm.
4. Integer Bilinear Form with ANY other such matrix.
-/
def isMaximalSplitOrder (X : ZornVectorMatrix ℚ) : Prop :=
  (∃ (za zb : ℤ) (zv zw : Fin 3 → ℤ),
    X.a = (za : ℚ) / 2 ∧ X.b = (zb : ℚ) / 2 ∧
    (∀ i, X.v i = (zv i : ℚ) / 2) ∧ (∀ i, X.w i = (zw i : ℚ) / 2)) ∧
  (∃ (t : ℤ), X.a + X.b = (t : ℚ)) ∧
  (∃ (n : ℤ), X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) = (n : ℚ)) ∧
  (∀ Y : ZornVectorMatrix ℚ, 
    (∃ (ya yb : ℤ) (yv yw : Fin 3 → ℤ),
      Y.a = (ya : ℚ) / 2 ∧ Y.b = (yb : ℚ) / 2 ∧
      (∀ i, Y.v i = (yv i : ℚ) / 2) ∧ (∀ i, Y.w i = (yw i : ℚ) / 2)) →
    (∃ (ty : ℤ), Y.a + Y.b = (ty : ℚ)) →
    (∃ (ny : ℤ), Y.a * Y.b - (Y.v 0 * Y.w 0 + Y.v 1 * Y.w 1 + Y.v 2 * Y.w 2) = (ny : ℚ)) →
    (∃ (m : ℤ), X.a * Y.b + X.b * Y.a - (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2 + Y.v 0 * X.w 0 + Y.v 1 * X.w 1 + Y.v 2 * X.w 2) = (m : ℚ)))

lemma zero_isMaximalSplitOrder : isMaximalSplitOrder (zero : ZornVectorMatrix ℚ) := by
  refine ⟨⟨0, 0, (fun _ => 0), (fun _ => 0), ?_, ?_, ?_, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ?_⟩
  · dsimp [zero]; norm_num
  · dsimp [zero]; norm_num
  · intro i; dsimp [zero]; norm_num
  · intro i; dsimp [zero]; norm_num
  · dsimp [zero]; norm_num
  · dsimp [zero]; norm_num
  · intro Y hY1 hY2 hY3
    use 0
    dsimp [zero]
    ring

lemma norm_is_integer {X : ZornVectorMatrix ℚ} (h : isMaximalSplitOrder X) : 
    ∃ (n : ℤ), X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2) = (n : ℚ) := by
  rcases h with ⟨_, _, hnorm, _⟩
  exact hnorm

lemma add_isMaximalSplitOrder {X Y : ZornVectorMatrix ℚ} 
    (hX : isMaximalSplitOrder X) (hY : isMaximalSplitOrder Y) : 
    isMaximalSplitOrder (add X Y) := by
  rcases hX with ⟨hX_half, ⟨tx, htx⟩, ⟨nx, hnx⟩, hX_bilin⟩
  rcases hY with ⟨hY_half, ⟨ty, hty⟩, ⟨ny, hny⟩, hY_bilin⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hX_half with ⟨xa, xb, xv, xw, ha, hb, hv, hw⟩
    rcases hY_half with ⟨ya, yb, yv, yw, ga, gb, gv, gw⟩
    use (xa + ya), (xb + yb), (fun i => xv i + yv i), (fun i => xw i + yw i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [add]; rw [ha, ga]; push_cast; ring
    · dsimp [add]; rw [hb, gb]; push_cast; ring
    · intro i; dsimp [add]; rw [hv i, gv i]; push_cast; ring
    · intro i; dsimp [add]; rw [hw i, gw i]; push_cast; ring
  · use tx + ty
    dsimp [add]
    have h1 : X.a + Y.a + (X.b + Y.b) = (X.a + X.b) + (Y.a + Y.b) := by ring
    rw [h1, htx, hty]
    push_cast
    ring
  · rcases hX_bilin Y hY_half ⟨ty, hty⟩ ⟨ny, hny⟩ with ⟨m, hm⟩
    use nx + ny + m
    dsimp [add]
    have h2 : (X.a + Y.a) * (X.b + Y.b) - ((X.v 0 + Y.v 0) * (X.w 0 + Y.w 0) + (X.v 1 + Y.v 1) * (X.w 1 + Y.w 1) + (X.v 2 + Y.v 2) * (X.w 2 + Y.w 2)) = 
      (X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2)) +
      (Y.a * Y.b - (Y.v 0 * Y.w 0 + Y.v 1 * Y.w 1 + Y.v 2 * Y.w 2)) +
      (X.a * Y.b + X.b * Y.a - (X.v 0 * Y.w 0 + X.v 1 * Y.w 1 + X.v 2 * Y.w 2 + Y.v 0 * X.w 0 + Y.v 1 * X.w 1 + Y.v 2 * X.w 2)) := by ring
    rw [h2, hnx, hny, hm]
    push_cast
    ring
  · intro Z hZ_half hZ_int1 hZ_int2
    rcases hX_bilin Z hZ_half hZ_int1 hZ_int2 with ⟨mx, hmx⟩
    rcases hY_bilin Z hZ_half hZ_int1 hZ_int2 with ⟨my, hmy⟩
    use mx + my
    dsimp [add]
    have h3 : (X.a + Y.a) * Z.b + (X.b + Y.b) * Z.a - ((X.v 0 + Y.v 0) * Z.w 0 + (X.v 1 + Y.v 1) * Z.w 1 + (X.v 2 + Y.v 2) * Z.w 2 + Z.v 0 * (X.w 0 + Y.w 0) + Z.v 1 * (X.w 1 + Y.w 1) + Z.v 2 * (X.w 2 + Y.w 2)) =
      (X.a * Z.b + X.b * Z.a - (X.v 0 * Z.w 0 + X.v 1 * Z.w 1 + X.v 2 * Z.w 2 + Z.v 0 * X.w 0 + Z.v 1 * X.w 1 + Z.v 2 * X.w 2)) +
      (Y.a * Z.b + Y.b * Z.a - (Y.v 0 * Z.w 0 + Y.v 1 * Z.w 1 + Y.v 2 * Z.w 2 + Z.v 0 * Y.w 0 + Z.v 1 * Y.w 1 + Z.v 2 * Y.w 2)) := by ring
    rw [h3, hmx, hmy]
    push_cast
    ring

lemma smul_isMaximalSplitOrder (z : ℤ) {X : ZornVectorMatrix ℚ} (hX : isMaximalSplitOrder X) : 
    isMaximalSplitOrder (smul (z : ℚ) X) := by
  rcases hX with ⟨hX_half, ⟨tx, htx⟩, ⟨nx, hnx⟩, hX_bilin⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hX_half with ⟨xa, xb, xv, xw, ha, hb, hv, hw⟩
    use (z * xa), (z * xb), (fun i => z * xv i), (fun i => z * xw i)
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [smul]; rw [ha]; push_cast; ring
    · dsimp [smul]; rw [hb]; push_cast; ring
    · intro i; dsimp [smul]; rw [hv i]; push_cast; ring
    · intro i; dsimp [smul]; rw [hw i]; push_cast; ring
  · use z * tx
    dsimp [smul]
    have h1 : (z : ℚ) * X.a + (z : ℚ) * X.b = (z : ℚ) * (X.a + X.b) := by ring
    rw [h1, htx]
    push_cast; ring
  · use z * z * nx
    dsimp [smul]
    have h : (z : ℚ) * (z : ℚ) * (nx : ℚ) = ((z * z * nx : ℤ) : ℚ) := by push_cast; rfl
    have h2 : ((z : ℚ) * X.a) * ((z : ℚ) * X.b) - (((z : ℚ) * X.v 0) * ((z : ℚ) * X.w 0) + ((z : ℚ) * X.v 1) * ((z : ℚ) * X.w 1) + ((z : ℚ) * X.v 2) * ((z : ℚ) * X.w 2)) = (z : ℚ) * (z : ℚ) * (X.a * X.b - (X.v 0 * X.w 0 + X.v 1 * X.w 1 + X.v 2 * X.w 2)) := by ring
    rw [h2, hnx, <- h]
  · intro Z hZ_half hZ_int1 hZ_int2
    rcases hX_bilin Z hZ_half hZ_int1 hZ_int2 with ⟨m, hm⟩
    use z * m
    dsimp [smul]
    have h : (z : ℚ) * (m : ℚ) = (z * m : ℤ) := by push_cast; rfl
    have h2 : ((z : ℚ) * X.a) * Z.b + ((z : ℚ) * X.b) * Z.a - (((z : ℚ) * X.v 0) * Z.w 0 + ((z : ℚ) * X.v 1) * Z.w 1 + ((z : ℚ) * X.v 2) * Z.w 2 + Z.v 0 * ((z : ℚ) * X.w 0) + Z.v 1 * ((z : ℚ) * X.w 1) + Z.v 2 * ((z : ℚ) * X.w 2)) = (z : ℚ) * (X.a * Z.b + X.b * Z.a - (X.v 0 * Z.w 0 + X.v 1 * Z.w 1 + X.v 2 * Z.w 2 + Z.v 0 * X.w 0 + Z.v 1 * X.w 1 + Z.v 2 * X.w 2)) := by ring
    rw [h2, hm, <- h]

end InfoGeometry.Algebra.ZornVectorMatrix
