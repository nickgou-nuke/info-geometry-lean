/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornColorBilinears
import InfoGeometry.Algebra.ZornLeftMajorana
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Faithful even and odd color operator coordinates

These are native linear maps into the existing associative endomorphism algebra.
The even map uses the already proved CAR bilinears, not a substitute matrix action.
The signed lower parameter is a label, not a Hilbert-space adjoint.
-/
noncomputable section
namespace InfoGeometry.Algebra.ZornColorOperatorCoordinates

open ZornVectorMatrix ZornColorBilinears
variable {R : Type*} [CommRing R]
abbrev Op (R : Type*) [CommRing R] := Module.End R (ZornVectorMatrix R)
abbrev Mat (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-- The nine actual color bilinears and the scalar identity. -/
def evenMap : (Mat R × R) →ₗ[R] Op R where
  toFun t := (∑ i : Fin 3, ∑ j : Fin 3, t.1 i j • E i j) + t.2 • 1
  map_add' t s := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.add_apply, _root_.add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' r t := by
    simp [_root_.smul_add, Finset.smul_sum, smul_smul]

/-- All six odd generators, with coefficients, on the native eight-dimensional module. -/
def oddMap : (ZornVec3 R × ZornVec3 R) →ₗ[R] Op R where
  toFun t := L_map (R := R) (offDiagonal t.1 (-t.2))
  map_add' t s := by
    apply LinearMap.ext
    intro X
    ext i
    all_goals try fin_cases i
    all_goals simp [L_map, mul, offDiagonal, zvm_add_def,
      add, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring
  map_smul' r t := by
    apply LinearMap.ext
    intro X
    ext i
    all_goals try fin_cases i
    all_goals simp [L_map, mul, offDiagonal, zvm_smul_def,
      smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]
    all_goals ring

set_option maxHeartbeats 1500000 in
/-- Explicit action, including the determinant-weight scalar and dual-vector sectors. -/
theorem evenMap_apply (M : Mat R) (c : R) (X : ZornVectorMatrix R) :
    evenMap (M, c) X =
      ⟨(c + Matrix.trace M) * X.a,
        fun i => M.mulVec X.v i + c * X.v i,
        fun i => (c + Matrix.trace M) * X.w i - M.transpose.mulVec X.w i,
        c * X.b⟩ := by
  ext k
  all_goals try fin_cases k
  all_goals simp [evenMap, E, L_map, mul, U, V, zvm_add_def, zvm_neg_def,
    zvm_smul_def, add, neg, smul, ZornVec3.basis, ZornVec3.dot, ZornVec3.cross,
    Matrix.mulVec, dotProduct, Matrix.trace, Matrix.diag, Fin.sum_univ_three]
  all_goals ring

@[simp] theorem evenMap_zero_matrix (c : R) : evenMap (0, c) = c • (1 : Op R) := by
  simp [evenMap]

@[simp] theorem oddMap_apply (p q : ZornVec3 R) (X : ZornVectorMatrix R) :
    oddMap (p, q) X = mul (offDiagonal p (-q)) X := rfl

/-- The even operator's scalar coordinate is read off on the vacuum pole. -/
theorem evenMap_E22 (M : Mat R) (c : R) :
    evenMap (M, c) E22 = smul c E22 := by
  rw [evenMap_apply]
  ext i <;> simp [E22, smul, Matrix.mulVec, dotProduct]

/-- Faithfulness of all ten even parameters, valid also in small characteristics. -/
theorem evenMap_injective : Function.Injective (evenMap (R := R)) := by
  rintro ⟨M, c⟩ ⟨N, d⟩ h
  have hc : c = d := by
    have ht := congrArg (fun T : Op R => (T E22).b) h
    rw [evenMap_E22, evenMap_E22] at ht
    simpa [smul, E22] using ht
  subst d
  have hM : M = N := by
    ext i j
    have ht := congrArg (fun T : Op R => (T (U j)).v i) h
    fin_cases i <;> fin_cases j <;>
      simpa [evenMap_apply, U, Matrix.mulVec, dotProduct, ZornVec3.basis,
        Fin.sum_univ_three] using ht
  exact Prod.ext hM rfl

/-- The upper and lower input vectors are recovered on opposite Peirce poles. -/
theorem oddMap_injective : Function.Injective (oddMap (R := R)) := by
  rintro ⟨p, q⟩ ⟨r, s⟩ h
  have hp : p = r := by
    have ht := congrArg (fun T : Op R => (T E22).v) h
    simpa [oddMap_apply, mul, offDiagonal, E22, ZornVec3.cross] using ht
  have hq : q = s := by
    have ht := congrArg (fun T : Op R => (T E11).w) h
    funext i
    have hi := congrFun ht i
    simpa [oddMap_apply, mul, offDiagonal, E11, ZornVec3.cross] using hi
  exact Prod.ext hp hq

/-- Actual homogeneous submodules in the associative operator carrier. -/
abbrev evenPart : Submodule R (Op R) := LinearMap.range evenMap
abbrev oddPart : Submodule R (Op R) := LinearMap.range oddMap

/-- The two ranges are disjoint without using eigenspaces or dividing by two. -/
theorem even_odd_disjoint : Disjoint (evenPart (R := R)) oddPart := by
  apply Submodule.disjoint_def.mpr
  rintro T ⟨⟨M, c⟩, he⟩ ⟨⟨p, q⟩, ho⟩
  have h := he.trans ho.symm
  have hp : p = 0 := by
    have ht := congrArg (fun A : Op R => (A E22).v) h
    rw [evenMap_E22] at ht
    funext i
    have hi := congrFun ht i
    simpa [oddMap_apply, mul, offDiagonal, E22, smul, ZornVec3.cross, eq_comm] using hi
  have hq : q = 0 := by
    have ht := congrArg (fun A : Op R => (A E11).w) h
    funext i
    have hi := congrFun ht i
    simpa [evenMap_apply, oddMap_apply, mul, offDiagonal, E11, Matrix.mulVec,
      dotProduct, ZornVec3.cross, eq_comm] using hi
  rw [hp, hq] at ho
  change oddMap (0 : ZornVec3 R × ZornVec3 R) = T at ho
  simpa only [map_zero] using ho.symm

section Dimension
variable {K : Type*} [Field K]

theorem finrank_evenPart : Module.finrank K (evenPart (R := K)) = 10 := by
  have h := (LinearEquiv.ofInjective (evenMap (R := K)) evenMap_injective).finrank_eq
  apply h.symm.trans
  simp [Mat, Module.finrank_prod, Module.finrank_matrix]

theorem finrank_oddPart : Module.finrank K (oddPart (R := K)) = 6 := by
  have h := (LinearEquiv.ofInjective (oddMap (R := K)) oddMap_injective).finrank_eq
  apply h.symm.trans
  simp [ZornVec3, Module.finrank_prod]
end Dimension

end InfoGeometry.Algebra.ZornColorOperatorCoordinates
