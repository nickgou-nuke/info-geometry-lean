/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornColorOperatorCoordinates
import InfoGeometry.Canonical.GLSupermatrixGradedLie

/-! # The actual homogeneous color operator superalgebra

Even parameters are gl3 plus a central scalar; odd parameters are a vector
and a covector. Their odd bracket is scalar, not the gl(3|1) matrix-unit bracket.
Closure is proved for actual submodules of `Module.End`, and the inherited
super-Jacobi law comes from the existing universal associative-ring theorem.
-/
noncomputable section
namespace InfoGeometry.Algebra.ZornColorOperatorCoordinates

open ZornVectorMatrix
open InfoGeometry.Canonical.GLSupermatrixGradedLie
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
/-- The central even parameter drops out of the even commutator. -/
theorem even_even_bracket (M N : Mat R) (c d : R) :
    evenMap (M, c) * evenMap (N, d) - evenMap (N, d) * evenMap (M, c) =
      evenMap (M * N - N * M, 0) := by
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, LinearMap.sub_apply, evenMap_apply]
  ext i
  all_goals try fin_cases i
  all_goals simp [zvm_add_def, zvm_neg_def, _root_.sub_eq_add_neg, add, neg,
    Matrix.mulVec, Matrix.mul_apply, Matrix.transpose, dotProduct,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  all_goals ring

set_option maxHeartbeats 1000000 in
/-- The vector and covector transform contragrediently; no common-source assumption. -/
theorem even_odd_bracket (M : Mat R) (c : R) (p q : ZornVec3 R) :
    evenMap (M, c) * oddMap (p, q) - oddMap (p, q) * evenMap (M, c) =
      oddMap (M.mulVec p, -M.transpose.mulVec q) := by
  apply LinearMap.ext
  intro X
  simp only [Module.End.mul_apply, LinearMap.sub_apply, evenMap_apply, oddMap_apply]
  ext i
  all_goals try fin_cases i
  all_goals simp [mul, offDiagonal, zvm_add_def, zvm_neg_def,
    _root_.sub_eq_add_neg, add, neg, Matrix.mulVec, Matrix.transpose, dotProduct,
    Matrix.trace, Matrix.diag, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
  all_goals ring

/-- All odd-odd superbrackets are scalar central operators. -/
theorem odd_odd_bracket (p q r s : ZornVec3 R) :
    oddMap (p, q) * oddMap (r, s) + oddMap (r, s) * oddMap (p, q) =
      (-(ZornVec3.dot p s + ZornVec3.dot r q)) • (1 : Op R) := by
  change L_map (offDiagonal p (-q)) * L_map (offDiagonal r (-s)) +
    L_map (offDiagonal r (-s)) * L_map (offDiagonal p (-q)) = _
  rw [left_offDiagonal_anticommutator]
  congr 1
  simp [ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- Every even color operator preserves the actual left Peirce projector. -/
theorem evenPart_commutes_projector {X : Op R} (hX : X ∈ evenPart) :
    Commute (L_map (R := R) (E11 : ZornVectorMatrix R)) X := by
  obtain ⟨⟨M, c⟩, rfl⟩ := hX
  apply LinearMap.ext
  intro Y
  simp only [Module.End.mul_apply, left_E11_apply, evenMap_apply]
  ext i <;> simp [Matrix.mulVec, dotProduct]

/-- Oddness is proved by the tangent equation itself, including characteristic two. -/
theorem oddPart_tangent {X : Op R} (hX : X ∈ oddPart) :
    L_map (R := R) (E11 : ZornVectorMatrix R) * X +
      X * L_map (R := R) E11 = X := by
  obtain ⟨⟨p, q⟩, rfl⟩ := hX
  exact left_E11_tangent_offDiagonal p (-q)

/-- The corrected homogeneous components, indexed by the existing parity type. -/
def component : Parity → Submodule R (Op R)
  | .even => evenPart
  | .odd => oddPart

/-- All parity combinations close under the actual superbracket. -/
theorem bracket_mem (p q : Parity) {X Y : Op R}
    (hX : X ∈ component p) (hY : Y ∈ component q) :
    ringSuperbracket p q X Y ∈ component (p + q) := by
  cases p <;> cases q
  · obtain ⟨⟨M, c⟩, rfl⟩ := hX
    obtain ⟨⟨N, d⟩, rfl⟩ := hY
    exact ⟨(M * N - N * M, 0), (even_even_bracket M N c d).symm⟩
  · obtain ⟨⟨M, c⟩, rfl⟩ := hX
    obtain ⟨⟨p, q⟩, rfl⟩ := hY
    exact ⟨(M.mulVec p, -M.transpose.mulVec q), (even_odd_bracket M c p q).symm⟩
  · obtain ⟨⟨p, q⟩, rfl⟩ := hX
    obtain ⟨⟨M, c⟩, rfl⟩ := hY
    refine ⟨-(M.mulVec p, -M.transpose.mulVec q), ?_⟩
    rw [map_neg, ← even_odd_bracket]
    change -(evenMap (M, c) * oddMap (p, q) - oddMap (p, q) * evenMap (M, c)) =
      oddMap (p, q) * evenMap (M, c) - evenMap (M, c) * oddMap (p, q)
    exact neg_sub _ _
  · obtain ⟨⟨p, q⟩, rfl⟩ := hX
    obtain ⟨⟨r, s⟩, rfl⟩ := hY
    refine ⟨(0, -(ZornVec3.dot p s + ZornVec3.dot r q)), ?_⟩
    rw [evenMap_zero_matrix]
    exact (odd_odd_bracket p q r s).symm

/-- The closed operator-valued bracket on the homogeneous submodules. -/
def homogeneousBracket (p q : Parity) (X : component (R := R) p)
    (Y : component (R := R) q) : component (R := R) (p + q) := ⟨ringSuperbracket p q X.1 Y.1, bracket_mem p q X.2 Y.2⟩

/-- Super-Jacobi for the actual closed homogeneous carrier. -/
theorem homogeneous_super_jacobi (p q r : Parity)
    (X : component (R := R) p) (Y : component (R := R) q)
    (Z : component (R := R) r) :
    Parity.sign (Op R) p r *
        (homogeneousBracket p (q + r) X (homogeneousBracket q r Y Z)).1 +
      Parity.sign (Op R) q p *
        (homogeneousBracket q (r + p) Y (homogeneousBracket r p Z X)).1 +
      Parity.sign (Op R) r q *
        (homogeneousBracket r (p + q) Z (homogeneousBracket p q X Y)).1 = 0 :=
  graded_super_jacobi p q r X.1 Y.1 Z.1

/-- Centrality holds against every endomorphism, not just the displayed generators. -/
theorem odd_bracket_central {X Y : Op R} (hX : X ∈ oddPart) (hY : Y ∈ oddPart)
    (T : Op R) : Commute (X * Y + Y * X) T := by
  obtain ⟨⟨p, q⟩, rfl⟩ := hX
  obtain ⟨⟨r, s⟩, rfl⟩ := hY
  rw [odd_odd_bracket]
  show _ * T = T * _
  simp

end InfoGeometry.Algebra.ZornColorOperatorCoordinates
