/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCore
import InfoGeometry.Exceptional.CFSGPort.ChevalleyRoots
import Mathlib.Algebra.Lie.CartanSubalgebra

/-!
# 6D Split Cartan Subalgebra and 72-Root Chevalley System for `h3zornCubicStabilizer` (`𝔢₆(6)`)

On the 78-dimensional reduced structure Lie algebra `h3zornCubicStabilizer`, this module
constructs:
1. A sparse integer matrix certification layer via `h3zornToMatrix : Module.End ℝ (H3Zorn ℝ) ≃ₐ[ℝ] Matrix (Fin 27) (Fin 27) ℝ`.
2. The 6 simple Chevalley triples `(e6SimpleE i, e6SimpleF i, e6SimpleH i)` satisfying the exact
   Bourbaki `E₆` Cartan relations for `Tag.cartan .E6`.
3. All 72 root operators `e6RootVec (r : Fin 72)` (`(e6RootVec r : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0`),
   their root vectors `e6RootCoord r`, and the bijection `e6RootEquiv : Fin 72 ≃ CFSGPort.Chevalley.RootOps.RootCarrier .E6`.
4. The 78D Chevalley basis `e6ChevalleyBasis : Module.Basis (Fin 6 ⊕ Fin 72) ℝ h3zornCubicStabilizer`
   and the `IsCartanSubalgebra` instance for the 6D split Cartan subalgebra `h3zornCartan`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

private instance : Module.Finite ℝ (H3Zorn ℝ) :=
  Module.Finite.of_basis h3ZornBasis

private instance : Module.Finite ℝ h3zornCubicStabilizer :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_h3zornCubicStabilizer]; decide)

section SparseMatrixLayer

abbrev SparseMat27 := List (Fin 27 × Fin 27 × ℤ)

def sparseVal (s : SparseMat27) (i j : Fin 27) : ℤ :=
  s.foldr (fun p acc => (if p.1 == i && p.2.1 == j then p.2.2 else 0) + acc) 0

@[simp] theorem sparseVal_nil (i j : Fin 27) : sparseVal [] i j = 0 := rfl

@[simp] theorem sparseVal_cons (r c : Fin 27) (v : ℤ) (t : SparseMat27) (i j : Fin 27) :
    sparseVal ((r, c, v) :: t) i j =
      (if r == i && c == j then v else 0) + sparseVal t i j := rfl

def sparseToMat (s : SparseMat27) : Matrix (Fin 27) (Fin 27) ℤ :=
  fun i j => sparseVal s i j

def sparseNeg (s : SparseMat27) : SparseMat27 :=
  s.map fun (r, c, v) => (r, c, -v)

def sparseAdd (s t : SparseMat27) : SparseMat27 := s ++ t

def sparseSub (s t : SparseMat27) : SparseMat27 := s ++ sparseNeg t

def sparseSmul (c : ℤ) (s : SparseMat27) : SparseMat27 :=
  s.map fun (r, col, v) => (r, col, c * v)

def sparseMul (s t : SparseMat27) : SparseMat27 :=
  s.flatMap fun (i, k, v) =>
    t.filterMap fun (k', j, w) => if k == k' then some (i, j, v * w) else none

def sparseComm (s t : SparseMat27) : SparseMat27 :=
  sparseSub (sparseMul s t) (sparseMul t s)

def sparseZeroCheck (s : SparseMat27) : Bool :=
  s.all fun p => sparseVal s p.1 p.2.1 == 0

def sparseEq (s t : SparseMat27) : Bool :=
  sparseZeroCheck (sparseSub s t)

private theorem sparseVal_append (s t : SparseMat27) (i j : Fin 27) :
    sparseVal (s ++ t) i j = sparseVal s i j + sparseVal t i j := by
  induction s with
  | nil => simp
  | cons p s ih =>
    rcases p with ⟨r, c, v⟩
    simp only [List.cons_append, sparseVal_cons, ih, add_assoc]

theorem sparseVal_add (s t : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseAdd s t) i j = sparseVal s i j + sparseVal t i j :=
  sparseVal_append s t i j

theorem sparseToMat_add (s t : SparseMat27) :
    sparseToMat (sparseAdd s t) = sparseToMat s + sparseToMat t := by
  ext i j
  exact sparseVal_add s t i j

private theorem sparseVal_map_neg (s : SparseMat27) (i j : Fin 27) :
    sparseVal (s.map fun (r, c, v) => (r, c, -v)) i j = -sparseVal s i j := by
  induction s with
  | nil => simp
  | cons p s ih =>
    rcases p with ⟨r, c, v⟩
    simp only [List.map_cons, sparseVal_cons]
    rw [ih]
    split_ifs <;> ring

theorem sparseVal_neg (s : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseNeg s) i j = -sparseVal s i j :=
  sparseVal_map_neg s i j

theorem sparseToMat_neg (s : SparseMat27) :
    sparseToMat (sparseNeg s) = -sparseToMat s := by
  ext i j
  exact sparseVal_neg s i j

theorem sparseVal_sub (s t : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseSub s t) i j = sparseVal s i j - sparseVal t i j := by
  change sparseVal (s ++ sparseNeg t) i j = _
  rw [sparseVal_append, sparseVal_neg, sub_eq_add_neg]

theorem sparseToMat_sub (s t : SparseMat27) :
    sparseToMat (sparseSub s t) = sparseToMat s - sparseToMat t := by
  ext i j
  exact sparseVal_sub s t i j

private theorem sparseVal_map_smul (c : ℤ) (s : SparseMat27) (i j : Fin 27) :
    sparseVal (s.map fun (r, col, v) => (r, col, c * v)) i j = c * sparseVal s i j := by
  induction s with
  | nil => simp
  | cons p s ih =>
    rcases p with ⟨r, col, v⟩
    simp only [List.map_cons, sparseVal_cons]
    rw [ih]
    split_ifs <;> ring

theorem sparseVal_smul (c : ℤ) (s : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseSmul c s) i j = c * sparseVal s i j :=
  sparseVal_map_smul c s i j

theorem sparseToMat_smul (c : ℤ) (s : SparseMat27) :
    sparseToMat (sparseSmul c s) = c • sparseToMat s := by
  ext i j
  exact sparseVal_smul c s i j

private theorem sparseVal_filterMap_mul_row (a i k₀ : Fin 27) (v : ℤ) (t : SparseMat27)
    (j : Fin 27) :
    sparseVal (t.filterMap fun (k', c, w) => if k₀ == k' then some (a, c, v * w) else none) i j =
      (if a == i then v * sparseVal t k₀ j else 0) := by
  induction t with
  | nil => simp
  | cons p t ih =>
    rcases p with ⟨k', c, w⟩
    by_cases hk : k₀ == k'
    · have hk' : k' == k₀ := by rw [beq_iff_eq] at hk ⊢; exact hk.symm
      simp only [List.filterMap_cons, hk, ↓reduceIte, sparseVal_cons, hk', Bool.true_and, ih]
      by_cases hai : a == i <;> by_cases hcj : c == j <;> simp [hai, hcj]
      ring
    · have hkf : (k₀ == k') = false := Bool.eq_false_iff.mpr hk
      have hk' : (k' == k₀) = false := by
        rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]
        rw [beq_iff_eq] at hk
        exact fun h => hk h.symm
      simp only [List.filterMap_cons, hkf, Bool.false_eq_true, ↓reduceIte, sparseVal_cons, hk',
        Bool.false_and, zero_add, ih]

theorem sparseVal_mul (s t : SparseMat27) (i j : Fin 27) :
    sparseVal (sparseMul s t) i j = ∑ k : Fin 27, sparseVal s i k * sparseVal t k j := by
  induction s with
  | nil => simp [sparseMul]
  | cons p s ih =>
    rcases p with ⟨a, k₀, v⟩
    change sparseVal (sparseAdd
      (t.filterMap fun (k', c, w) => if k₀ == k' then some (a, c, v * w) else none)
      (sparseMul s t)) i j =
      ∑ k : Fin 27, ((if (a == i && k₀ == k) = true then v else 0) + sparseVal s i k) * sparseVal t k j
    rw [sparseVal_add, sparseVal_filterMap_mul_row, ih]
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    by_cases hai : a == i
    · have hsing : ∑ x : Fin 27, (if (a == i && k₀ == x) = true then v else 0) * sparseVal t x j =
          v * sparseVal t k₀ j := by
        rw [Finset.sum_eq_single k₀]
        · simp [hai]
        · intro x _ hxk
          simp [hai, hxk.symm]
        · intro hk₀; exact absurd (Finset.mem_univ k₀) hk₀
      rw [hsing]
      simp only [hai, ↓reduceIte]
    · simp [hai]

theorem sparseToMat_mul (s t : SparseMat27) :
    sparseToMat (sparseMul s t) = sparseToMat s * sparseToMat t := by
  ext i j
  exact sparseVal_mul s t i j

theorem sparseToMat_comm (s t : SparseMat27) :
    sparseToMat (sparseComm s t) =
      sparseToMat s * sparseToMat t - sparseToMat t * sparseToMat s := by
  rw [sparseComm, sparseToMat_sub, sparseToMat_mul, sparseToMat_mul]

private theorem sparseVal_eq_zero_of_not_mem (s : SparseMat27) (i j : Fin 27)
    (h : ∀ p ∈ s, ¬(p.1 = i ∧ p.2.1 = j)) : sparseVal s i j = 0 := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    rcases p with ⟨r, c, v⟩
    have hp := h (r, c, v) List.mem_cons_self
    have hs : ∀ q ∈ s, ¬(q.1 = i ∧ q.2.1 = j) := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hrc : (r == i && c == j) = false := by
      rw [Bool.eq_false_iff, ne_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      exact hp
    simp only [sparseVal_cons, hrc, Bool.false_eq_true, ↓reduceIte, zero_add, ih hs]

theorem sparseToMat_eq_zero_of_sparseZeroCheck {s : SparseMat27}
    (h : sparseZeroCheck s = true) : sparseToMat s = 0 := by
  ext i j
  change sparseVal s i j = 0
  by_cases hmem : ∃ p ∈ s, p.1 = i ∧ p.2.1 = j
  · rcases hmem with ⟨p, hp, hi, hj⟩
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq] at h
    have hpz := h p hp
    rwa [hi, hj] at hpz
  · push Not at hmem
    exact sparseVal_eq_zero_of_not_mem s i j (fun p hp hpair => hmem p hp hpair.1 hpair.2)

theorem sparseToMat_eq_of_sparseEq {s t : SparseMat27}
    (h : sparseEq s t = true) : sparseToMat s = sparseToMat t := by
  have hz := sparseToMat_eq_zero_of_sparseZeroCheck h
  rw [sparseToMat_sub] at hz
  exact sub_eq_zero.mp hz

end SparseMatrixLayer

section BasisAndOperatorMatrix

/-- Canonical 27D coordinate matrix equivalence on `Module.End ℝ (H3Zorn ℝ)`. -/
def h3zornToMatrix : Module.End ℝ (H3Zorn ℝ) ≃ₐ[ℝ] Matrix (Fin 27) (Fin 27) ℝ :=
  LinearMap.toMatrixAlgEquiv h3ZornBasis

def h3zornCoordVec (k : Fin 27) : H3Zorn ℝ := h3ZornBasis k

def intMatToEnd (M : Matrix (Fin 27) (Fin 27) ℤ) : Module.End ℝ (H3Zorn ℝ) :=
  h3zornToMatrix.symm (M.map Int.cast)

@[simp] theorem h3zornToMatrix_intMatToEnd (M : Matrix (Fin 27) (Fin 27) ℤ) :
    h3zornToMatrix (intMatToEnd M) = M.map Int.cast := by
  simp [intMatToEnd]

theorem h3zornToMatrix_apply (T : Module.End ℝ (H3Zorn ℝ)) (r q : Fin 27) :
    h3zornToMatrix T r q = h3ZornCoordinate (T (h3ZornBasis q)) r := by
  change LinearMap.toMatrix h3ZornBasis h3ZornBasis T r q = _
  rw [LinearMap.toMatrix_apply]
  rfl

theorem h3ZornCoordinate_basis_self (k r : Fin 27) :
    h3ZornCoordinate (h3ZornBasis k) r = if k = r then 1 else 0 := by
  have hb : h3ZornBasis.repr (h3ZornBasis k) = Finsupp.single k (1 : ℝ) := h3ZornBasis.repr_self k
  have h1 : h3ZornBasis.repr (h3ZornBasis k) r = (if k = r then (1 : ℝ) else 0) := by
    rw [hb, Finsupp.single_apply]
  exact h1

theorem h3ZornBasis_zero : h3ZornBasis 0 = h3_diag₁ := by
  apply h3ZornCoordEquiv.injective
  ext r
  change h3ZornCoordinate (h3ZornBasis 0) r = h3ZornCoordinate h3_diag₁ r
  rw [h3ZornCoordinate_basis_self]
  fin_cases r <;> simp [h3ZornCoordinate, h3_diag₁]

theorem h3ZornBasis_one : h3ZornBasis 1 = h3_diag₂ := by
  apply h3ZornCoordEquiv.injective
  ext r
  change h3ZornCoordinate (h3ZornBasis 1) r = h3ZornCoordinate h3_diag₂ r
  rw [h3ZornCoordinate_basis_self]
  fin_cases r <;> simp [h3ZornCoordinate, h3_diag₂]

theorem h3ZornBasis_two : h3ZornBasis 2 = h3_diag₃ := by
  apply h3ZornCoordEquiv.injective
  ext r
  change h3ZornCoordinate (h3ZornBasis 2) r = h3ZornCoordinate h3_diag₃ r
  rw [h3ZornCoordinate_basis_self]
  fin_cases r <;> simp [h3ZornCoordinate, h3_diag₃]

private theorem zorn_basis_coord_v (i : Fin 8) (j : Fin 3) :
    (zorn_basis i).v j =
      if (i.val = 1 ∧ j.val = 0) ∨ (i.val = 2 ∧ j.val = 1) ∨ (i.val = 3 ∧ j.val = 2) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem zorn_basis_coord_w (i : Fin 8) (j : Fin 3) :
    (zorn_basis i).w j =
      if (i.val = 4 ∧ j.val = 0) ∨ (i.val = 5 ∧ j.val = 1) ∨ (i.val = 6 ∧ j.val = 2) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem h3ZornCoord_embedJ12 (x : ZornVectorMatrix ℝ) (r : Fin 27) :
    h3ZornCoordinate (embedJ12 x) r =
      match r.val with
      | 3 => x.a | 4 => x.v 0 | 5 => x.v 1 | 6 => x.v 2
      | 7 => x.w 0 | 8 => x.w 1 | 9 => x.w 2 | 10 => x.b | _ => 0 := by
  fin_cases r <;> rfl

private theorem h3ZornCoord_embedJ23 (x : ZornVectorMatrix ℝ) (r : Fin 27) :
    h3ZornCoordinate (embedJ23 x) r =
      match r.val with
      | 11 => x.a | 12 => x.v 0 | 13 => x.v 1 | 14 => x.v 2
      | 15 => x.w 0 | 16 => x.w 1 | 17 => x.w 2 | 18 => x.b | _ => 0 := by
  fin_cases r <;> rfl

private theorem h3ZornCoord_embedJ31 (x : ZornVectorMatrix ℝ) (r : Fin 27) :
    h3ZornCoordinate (embedJ31 x) r =
      match r.val with
      | 19 => x.a | 20 => x.v 0 | 21 => x.v 1 | 22 => x.v 2
      | 23 => x.w 0 | 24 => x.w 1 | 25 => x.w 2 | 26 => x.b | _ => 0 := by
  fin_cases r <;> rfl

private theorem h3ZornBasis_eq_of_coord_table (k : Fin 27) (v : H3Zorn ℝ)
    (h : ∀ r : Fin 27, h3ZornCoordinate v r = if k = r then 1 else 0) :
    h3ZornBasis k = v := by
  apply h3ZornCoordEquiv.injective
  ext r
  change h3ZornCoordinate (h3ZornBasis k) r = h3ZornCoordinate v r
  rw [h3ZornCoordinate_basis_self, h]

theorem h3ZornBasis_12 (i : Fin 8) :
    h3ZornBasis ⟨3 + i.val, by omega⟩ = embedJ12 (zorn_basis i) := by
  apply h3ZornBasis_eq_of_coord_table
  intro r
  rw [h3ZornCoord_embedJ12]
  fin_cases i <;> fin_cases r <;> simp [zorn_basis]

theorem h3ZornBasis_23 (i : Fin 8) :
    h3ZornBasis ⟨11 + i.val, by omega⟩ = embedJ23 (zorn_basis i) := by
  apply h3ZornBasis_eq_of_coord_table
  intro r
  rw [h3ZornCoord_embedJ23]
  fin_cases i <;> fin_cases r <;> simp [zorn_basis]

theorem h3ZornBasis_31 (i : Fin 8) :
    h3ZornBasis ⟨19 + i.val, by omega⟩ = embedJ31 (zorn_basis i) := by
  apply h3ZornBasis_eq_of_coord_table
  intro r
  rw [h3ZornCoord_embedJ31]
  fin_cases i <;> fin_cases r <;> simp [zorn_basis]

theorem h3ZornCoordinate_smul (c : ℝ) (X : H3Zorn ℝ) (r : Fin 27) :
    h3ZornCoordinate (c • X) r = c * h3ZornCoordinate X r := by
  change h3ZornCoordinateLM (c • X) r = c * h3ZornCoordinateLM X r
  rw [map_smul]
  rfl

theorem h3ZornCoordinate_add (X Y : H3Zorn ℝ) (r : Fin 27) :
    h3ZornCoordinate (X + Y) r = h3ZornCoordinate X r + h3ZornCoordinate Y r := by
  change h3ZornCoordinateLM (X + Y) r = h3ZornCoordinateLM X r + h3ZornCoordinateLM Y r
  rw [map_add]
  rfl

def zornBilinInt (i j : Fin 8) : ℤ :=
  match i.val, j.val with

  | 0, 7 => 1
  | 1, 4 => -1
  | 2, 5 => -1
  | 3, 6 => -1
  | 4, 1 => -1
  | 5, 2 => -1
  | 6, 3 => -1
  | 7, 0 => 1
  | _, _ => 0


def zornConjMulCoeff (i j : Fin 8) : ℤ :=
  match i.val, j.val with

  | 0, 0 => 1
  | 0, 4 => -1
  | 0, 5 => -1
  | 0, 6 => -1
  | 1, 0 => -1
  | 1, 2 => 1
  | 1, 3 => -1
  | 1, 4 => 1
  | 2, 0 => -1
  | 2, 1 => -1
  | 2, 3 => 1
  | 2, 5 => 1
  | 3, 0 => -1
  | 3, 1 => 1
  | 3, 2 => -1
  | 3, 6 => 1
  | 4, 1 => 1
  | 4, 5 => -1
  | 4, 6 => 1
  | 4, 7 => -1
  | 5, 2 => 1
  | 5, 4 => 1
  | 5, 6 => -1
  | 5, 7 => -1
  | 6, 3 => 1
  | 6, 4 => -1
  | 6, 5 => 1
  | 6, 7 => -1
  | 7, 1 => -1
  | 7, 2 => -1
  | 7, 3 => -1
  | 7, 7 => 1
  | _, _ => 0


def zornConjMulIdx (i j : Fin 8) : Fin 8 :=
  match i.val, j.val with

  | 0, 0 => 7
  | 0, 4 => 4
  | 0, 5 => 5
  | 0, 6 => 6
  | 1, 0 => 1
  | 1, 2 => 6
  | 1, 3 => 5
  | 1, 4 => 0
  | 2, 0 => 2
  | 2, 1 => 6
  | 2, 3 => 4
  | 2, 5 => 0
  | 3, 0 => 3
  | 3, 1 => 5
  | 3, 2 => 4
  | 3, 6 => 0
  | 4, 1 => 7
  | 4, 5 => 3
  | 4, 6 => 2
  | 4, 7 => 4
  | 5, 2 => 7
  | 5, 4 => 3
  | 5, 6 => 1
  | 5, 7 => 5
  | 6, 3 => 7
  | 6, 4 => 2
  | 6, 5 => 1
  | 6, 7 => 6
  | 7, 1 => 1
  | 7, 2 => 2
  | 7, 3 => 3
  | 7, 7 => 0
  | _, _ => 0


theorem zornBilin_zorn_basis (i j : Fin 8) :
    zornBilin (zorn_basis i) (zorn_basis j) = (zornBilinInt i j : ℝ) := by
  fin_cases i <;> fin_cases j <;>
    simp [zornBilin, zornBilinInt, zorn_basis, ZornVectorMatrix.trace, ZornVectorMatrix.mul,
      ZornVectorMatrix.conj, ZornVec3.dot]

private def zorn_basis_Z (i : Fin 8) : ZornVectorMatrix ℤ :=
  match i.val with
  | 0 => { a := 1, v := 0, w := 0, b := 0 }
  | 1 => { a := 0, v := fun j => if j = 0 then 1 else 0, w := 0, b := 0 }
  | 2 => { a := 0, v := fun j => if j = 1 then 1 else 0, w := 0, b := 0 }
  | 3 => { a := 0, v := fun j => if j = 2 then 1 else 0, w := 0, b := 0 }
  | 4 => { a := 0, v := 0, w := fun j => if j = 0 then 1 else 0, b := 0 }
  | 5 => { a := 0, v := 0, w := fun j => if j = 1 then 1 else 0, b := 0 }
  | 6 => { a := 0, v := 0, w := fun j => if j = 2 then 1 else 0, b := 0 }
  | 7 => { a := 0, v := 0, w := 0, b := 1 }
  | _ => { a := 0, v := 0, w := 0, b := 0 }

private def zornCast (X : ZornVectorMatrix ℤ) : ZornVectorMatrix ℝ :=
  ⟨X.a, fun k => X.v k, fun k => X.w k, X.b⟩

private theorem zornCast_basis (i : Fin 8) : zornCast (zorn_basis_Z i) = zorn_basis i := by
  fin_cases i <;> apply ZornVectorMatrix.ext <;>
    (try (funext k; fin_cases k)) <;>
    simp [zornCast, zorn_basis_Z, zorn_basis]

private theorem zornCast_conj (X : ZornVectorMatrix ℤ) :
    zornCast (ZornVectorMatrix.conj X) = ZornVectorMatrix.conj (zornCast X) := by
  apply ZornVectorMatrix.ext
  · rfl
  · funext k; exact Int.cast_neg (X.v k)
  · funext k; exact Int.cast_neg (X.w k)
  · rfl

private theorem zornCast_mul (X Y : ZornVectorMatrix ℤ) :
    zornCast (ZornVectorMatrix.mul X Y) = ZornVectorMatrix.mul (zornCast X) (zornCast Y) := by
  apply ZornVectorMatrix.ext
  · change ((X.a * Y.a + ZornVec3.dot X.v Y.w : ℤ) : ℝ) = _; simp [zornCast, ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]
  · funext k; fin_cases k <;> simp [zornCast, ZornVectorMatrix.mul, ZornVec3.cross]
  · funext k; fin_cases k <;> simp [zornCast, ZornVectorMatrix.mul, ZornVec3.cross]
  · change ((ZornVec3.dot X.w Y.v + X.b * Y.b : ℤ) : ℝ) = _; simp [zornCast, ZornVectorMatrix.mul, ZornVec3.dot, Fin.sum_univ_three]

private theorem zornCast_smul (c : ℤ) (X : ZornVectorMatrix ℤ) :
    zornCast (ZornVectorMatrix.smul c X) = (c : ℝ) • zornCast X := by
  apply ZornVectorMatrix.ext
  · exact Int.cast_mul c X.a
  · funext k; exact Int.cast_mul c (X.v k)
  · funext k; exact Int.cast_mul c (X.w k)
  · exact Int.cast_mul c X.b

theorem zornConjMul_zorn_basis (i j : Fin 8) :
    ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis i))
      (ZornVectorMatrix.conj (zorn_basis j)) =
        (zornConjMulCoeff i j : ℝ) • zorn_basis (zornConjMulIdx i j) := by
  have hchk : (List.finRange 8).all (fun i => (List.finRange 8).all (fun j =>
      let L := ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis_Z i))
        (ZornVectorMatrix.conj (zorn_basis_Z j))
      let R := ZornVectorMatrix.smul (zornConjMulCoeff i j) (zorn_basis_Z (zornConjMulIdx i j))
      (L.a == R.a) && (L.b == R.b) &&
        ((List.finRange 3).all fun k => (L.v k == R.v k) && (L.w k == R.w k)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, beq_iff_eq, true_implies] at hchk
  have hij := hchk i j
  have hZ : ZornVectorMatrix.mul (ZornVectorMatrix.conj (zorn_basis_Z i))
      (ZornVectorMatrix.conj (zorn_basis_Z j)) =
      ZornVectorMatrix.smul (zornConjMulCoeff i j) (zorn_basis_Z (zornConjMulIdx i j)) := by
    apply ZornVectorMatrix.ext
    · exact hij.1.1
    · funext k; exact (hij.2 k).1
    · funext k; exact (hij.2 k).2
    · exact hij.1.2
  rw [← zornCast_basis i, ← zornCast_basis j, ← zornCast_basis (zornConjMulIdx i j),
    ← zornCast_conj, ← zornCast_conj, ← zornCast_mul, hZ, zornCast_smul]

inductive H3Sector
  | diag (d : Fin 3)
  | j12 (i : Fin 8)
  | j23 (i : Fin 8)
  | j31 (i : Fin 8)
  deriving DecidableEq

def sectorOfFin (p : Fin 27) : H3Sector :=
  if h0 : p.val < 3 then .diag ⟨p.val, h0⟩
  else if h1 : p.val < 11 then .j12 ⟨p.val - 3, by omega⟩
  else if h2 : p.val < 19 then .j23 ⟨p.val - 11, by omega⟩
  else .j31 ⟨p.val - 19, by omega⟩

def finOfSector : H3Sector → Fin 27
  | .diag d => ⟨d.val, by omega⟩
  | .j12 i => ⟨3 + i.val, by omega⟩
  | .j23 i => ⟨11 + i.val, by omega⟩
  | .j31 i => ⟨19 + i.val, by omega⟩

theorem finOfSector_sectorOfFin (p : Fin 27) : finOfSector (sectorOfFin p) = p := by
  fin_cases p <;> rfl

theorem h3ZornBasis_sector (s : H3Sector) :
    h3ZornBasis (finOfSector s) = match s with
      | .diag 0 => h3_diag₁
      | .diag 1 => h3_diag₂
      | .diag 2 => h3_diag₃
      | .j12 i => embedJ12 (zorn_basis i)
      | .j23 i => embedJ23 (zorn_basis i)
      | .j31 i => embedJ31 (zorn_basis i) := by
  cases s with
  | diag d => fin_cases d; exact h3ZornBasis_zero; exact h3ZornBasis_one; exact h3ZornBasis_two
  | j12 i => exact h3ZornBasis_12 i
  | j23 i => exact h3ZornBasis_23 i
  | j31 i => exact h3ZornBasis_31 i

def twoLSectorFormula (s₁ s₂ : H3Sector) : Fin 27 → ℤ := fun r =>
  match s₁, s₂ with
  | .diag d₁, .diag d₂ => if d₁ = d₂ ∧ r.val = d₁.val then 2 else 0
  | .diag d, .j12 i => if (d.val = 0 ∨ d.val = 1) ∧ r.val = 3 + i.val then 1 else 0
  | .diag d, .j23 i => if (d.val = 1 ∨ d.val = 2) ∧ r.val = 11 + i.val then 1 else 0
  | .diag d, .j31 i => if (d.val = 2 ∨ d.val = 0) ∧ r.val = 19 + i.val then 1 else 0
  | .j12 i, .diag d => if (d.val = 0 ∨ d.val = 1) ∧ r.val = 3 + i.val then 1 else 0
  | .j23 i, .diag d => if (d.val = 1 ∨ d.val = 2) ∧ r.val = 11 + i.val then 1 else 0
  | .j31 i, .diag d => if (d.val = 2 ∨ d.val = 0) ∧ r.val = 19 + i.val then 1 else 0
  | .j12 i, .j12 j => if r.val = 0 ∨ r.val = 1 then zornBilinInt i j else 0
  | .j23 i, .j23 j => if r.val = 1 ∨ r.val = 2 then zornBilinInt i j else 0
  | .j31 i, .j31 j => if r.val = 2 ∨ r.val = 0 then zornBilinInt i j else 0
  | .j12 i, .j23 j => if r.val = 19 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0
  | .j23 j, .j12 i => if r.val = 19 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0
  | .j23 i, .j31 j => if r.val = 3 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0
  | .j31 j, .j23 i => if r.val = 3 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0
  | .j31 i, .j12 j => if r.val = 11 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0
  | .j12 j, .j31 i => if r.val = 11 + (zornConjMulIdx j i).val then zornConjMulCoeff j i else 0

def twoLData (p : Fin 27) : SparseMat27 :=
  match p.val with
  | 0 => [(0, 0, 2), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 10, 1), (19, 19, 1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 26, 1)]
  | 1 => [(1, 1, 2), (3, 3, 1), (4, 4, 1), (5, 5, 1), (6, 6, 1), (7, 7, 1), (8, 8, 1), (9, 9, 1), (10, 10, 1), (11, 11, 1), (12, 12, 1), (13, 13, 1), (14, 14, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 18, 1)]
  | 2 => [(2, 2, 2), (11, 11, 1), (12, 12, 1), (13, 13, 1), (14, 14, 1), (15, 15, 1), (16, 16, 1), (17, 17, 1), (18, 18, 1), (19, 19, 1), (20, 20, 1), (21, 21, 1), (22, 22, 1), (23, 23, 1), (24, 24, 1), (25, 25, 1), (26, 26, 1)]
  | 3 => [(0, 10, 1), (1, 10, 1), (3, 0, 1), (3, 1, 1), (15, 23, -1), (16, 24, -1), (17, 25, -1), (18, 19, 1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (26, 11, 1)]
  | 4 => [(0, 7, -1), (1, 7, -1), (4, 0, 1), (4, 1, 1), (11, 23, 1), (12, 19, -1), (16, 22, -1), (17, 21, 1), (20, 18, -1), (24, 14, 1), (25, 13, -1), (26, 15, 1)]
  | 5 => [(0, 8, -1), (1, 8, -1), (5, 0, 1), (5, 1, 1), (11, 24, 1), (13, 19, -1), (15, 22, 1), (17, 20, -1), (21, 18, -1), (23, 14, -1), (25, 12, 1), (26, 16, 1)]
  | 6 => [(0, 9, -1), (1, 9, -1), (6, 0, 1), (6, 1, 1), (11, 25, 1), (14, 19, -1), (15, 21, -1), (16, 20, 1), (22, 18, -1), (23, 13, 1), (24, 12, -1), (26, 17, 1)]
  | 7 => [(0, 4, -1), (1, 4, -1), (7, 0, 1), (7, 1, 1), (13, 25, 1), (14, 24, -1), (15, 26, -1), (18, 20, 1), (19, 12, 1), (21, 17, -1), (22, 16, 1), (23, 11, -1)]
  | 8 => [(0, 5, -1), (1, 5, -1), (8, 0, 1), (8, 1, 1), (12, 25, -1), (14, 23, 1), (16, 26, -1), (18, 21, 1), (19, 13, 1), (20, 17, 1), (22, 15, -1), (24, 11, -1)]
  | 9 => [(0, 6, -1), (1, 6, -1), (9, 0, 1), (9, 1, 1), (12, 24, 1), (13, 23, -1), (17, 26, -1), (18, 22, 1), (19, 14, 1), (20, 16, -1), (21, 15, 1), (25, 11, -1)]
  | 10 => [(0, 3, 1), (1, 3, 1), (10, 0, 1), (10, 1, 1), (11, 26, 1), (12, 20, -1), (13, 21, -1), (14, 22, -1), (19, 18, 1), (23, 15, -1), (24, 16, -1), (25, 17, -1)]
  | 11 => [(1, 18, 1), (2, 18, 1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (10, 19, 1), (11, 1, 1), (11, 2, 1), (23, 7, -1), (24, 8, -1), (25, 9, -1), (26, 3, 1)]
  | 12 => [(1, 15, -1), (2, 15, -1), (4, 26, -1), (8, 22, 1), (9, 21, -1), (10, 23, 1), (12, 1, 1), (12, 2, 1), (19, 7, 1), (20, 3, -1), (24, 6, -1), (25, 5, 1)]
  | 13 => [(1, 16, -1), (2, 16, -1), (5, 26, -1), (7, 22, -1), (9, 20, 1), (10, 24, 1), (13, 1, 1), (13, 2, 1), (19, 8, 1), (21, 3, -1), (23, 6, 1), (25, 4, -1)]
  | 14 => [(1, 17, -1), (2, 17, -1), (6, 26, -1), (7, 21, 1), (8, 20, -1), (10, 25, 1), (14, 1, 1), (14, 2, 1), (19, 9, 1), (22, 3, -1), (23, 5, -1), (24, 4, 1)]
  | 15 => [(1, 12, -1), (2, 12, -1), (3, 20, 1), (5, 25, -1), (6, 24, 1), (7, 19, -1), (15, 1, 1), (15, 2, 1), (21, 9, 1), (22, 8, -1), (23, 10, -1), (26, 4, 1)]
  | 16 => [(1, 13, -1), (2, 13, -1), (3, 21, 1), (4, 25, 1), (6, 23, -1), (8, 19, -1), (16, 1, 1), (16, 2, 1), (20, 9, -1), (22, 7, 1), (24, 10, -1), (26, 5, 1)]
  | 17 => [(1, 14, -1), (2, 14, -1), (3, 22, 1), (4, 24, -1), (5, 23, 1), (9, 19, -1), (17, 1, 1), (17, 2, 1), (20, 8, 1), (21, 7, -1), (25, 10, -1), (26, 6, 1)]
  | 18 => [(1, 11, 1), (2, 11, 1), (3, 26, 1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (18, 1, 1), (18, 2, 1), (19, 10, 1), (20, 4, -1), (21, 5, -1), (22, 6, -1)]
  | 19 => [(0, 26, 1), (2, 26, 1), (7, 15, -1), (8, 16, -1), (9, 17, -1), (10, 11, 1), (12, 4, -1), (13, 5, -1), (14, 6, -1), (18, 3, 1), (19, 0, 1), (19, 2, 1)]
  | 20 => [(0, 23, -1), (2, 23, -1), (3, 15, 1), (4, 11, -1), (8, 14, -1), (9, 13, 1), (12, 10, -1), (16, 6, 1), (17, 5, -1), (18, 7, 1), (20, 0, 1), (20, 2, 1)]
  | 21 => [(0, 24, -1), (2, 24, -1), (3, 16, 1), (5, 11, -1), (7, 14, 1), (9, 12, -1), (13, 10, -1), (15, 6, -1), (17, 4, 1), (18, 8, 1), (21, 0, 1), (21, 2, 1)]
  | 22 => [(0, 25, -1), (2, 25, -1), (3, 17, 1), (6, 11, -1), (7, 13, -1), (8, 12, 1), (14, 10, -1), (15, 5, 1), (16, 4, -1), (18, 9, 1), (22, 0, 1), (22, 2, 1)]
  | 23 => [(0, 20, -1), (2, 20, -1), (5, 17, 1), (6, 16, -1), (7, 18, -1), (10, 12, 1), (11, 4, 1), (13, 9, -1), (14, 8, 1), (15, 3, -1), (23, 0, 1), (23, 2, 1)]
  | 24 => [(0, 21, -1), (2, 21, -1), (4, 17, -1), (6, 15, 1), (8, 18, -1), (10, 13, 1), (11, 5, 1), (12, 9, 1), (14, 7, -1), (16, 3, -1), (24, 0, 1), (24, 2, 1)]
  | 25 => [(0, 22, -1), (2, 22, -1), (4, 16, 1), (5, 15, -1), (9, 18, -1), (10, 14, 1), (11, 6, 1), (12, 8, -1), (13, 7, 1), (17, 3, -1), (25, 0, 1), (25, 2, 1)]
  | 26 => [(0, 19, 1), (2, 19, 1), (3, 18, 1), (4, 12, -1), (5, 13, -1), (6, 14, -1), (11, 10, 1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (26, 0, 1), (26, 2, 1)]
  | _ => []

private def twoLRowCheck (p : Fin 27) : Bool :=
  (List.finRange 27).all fun q =>
    (List.finRange 27).all fun r =>
      twoLSectorFormula (sectorOfFin p) (sectorOfFin q) r == sparseVal (twoLData p) r q

private theorem twoLRowCheck_lt9 : ((List.finRange 9).all fun n => twoLRowCheck ⟨n.val, by omega⟩) = true := by decide
private theorem twoLRowCheck_9_18 : ((List.finRange 9).all fun n => twoLRowCheck ⟨n.val + 9, by omega⟩) = true := by decide
private theorem twoLRowCheck_18_27 : ((List.finRange 9).all fun n => twoLRowCheck ⟨n.val + 18, by omega⟩) = true := by decide

private theorem twoLSectorFormula_eq_sparseVal (p q r : Fin 27) :
    twoLSectorFormula (sectorOfFin p) (sectorOfFin q) r = sparseVal (twoLData p) r q := by
  have hrow : twoLRowCheck p = true := by
    by_cases hp9 : p.val < 9
    · have h1 := twoLRowCheck_lt9
      simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
      simpa using h1 ⟨p.val, hp9⟩
    · by_cases hp18 : p.val < 18
      · have h2 := twoLRowCheck_9_18
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h2
        have hp' : p.val - 9 < 9 := by omega
        have hval := h2 ⟨p.val - 9, hp'⟩
        have heq : (⟨(⟨p.val - 9, hp'⟩ : Fin 9).val + 9, by omega⟩ : Fin 27) = p :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hval
      · have h3 := twoLRowCheck_18_27
        simp only [List.all_eq_true, List.mem_finRange, true_implies] at h3
        have hp' : p.val - 18 < 9 := by omega
        have hval := h3 ⟨p.val - 18, hp'⟩
        have heq : (⟨(⟨p.val - 18, hp'⟩ : Fin 9).val + 18, by omega⟩ : Fin 27) = p :=
          Fin.ext (by dsimp; omega)
        simpa [heq] using hval
  dsimp [twoLRowCheck] at hrow
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hrow
  exact hrow q r

private theorem embedJ12_smul (c : ℝ) (x : ZornVectorMatrix ℝ) :
    embedJ12 (c • x) = c • embedJ12 x := by
  apply ext_h3 <;> simp [embedJ12, smul_readback, ZornVectorMatrix.smul_zero]

private theorem embedJ23_smul (c : ℝ) (x : ZornVectorMatrix ℝ) :
    embedJ23 (c • x) = c • embedJ23 x := by
  apply ext_h3 <;> simp [embedJ23, smul_readback, ZornVectorMatrix.smul_zero]

private theorem embedJ31_smul (c : ℝ) (x : ZornVectorMatrix ℝ) :
    embedJ31 (c • x) = c • embedJ31 x := by
  apply ext_h3 <;> simp [embedJ31, smul_readback, ZornVectorMatrix.smul_zero]

private theorem h3ZornCoord_two_mul_sector (s₁ s₂ : H3Sector) (r : Fin 27) :
    h3ZornCoordinate ((2 : ℝ) • (h3ZornBasis (finOfSector s₁) * h3ZornBasis (finOfSector s₂))) r =
      (twoLSectorFormula s₁ s₂ r : ℝ) := by
  have half2 : ∀ V : H3Zorn ℝ, (2 : ℝ) • ((1 / 2 : ℝ) • V) = V := by
    intro V; rw [smul_smul]; norm_num
  have h0_coord : h3ZornCoordinate h3_diag₁ r = if r.val = 0 then 1 else 0 := by
    rw [← h3ZornBasis_zero, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 0
    · have : (0 : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (0 : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm; simp [this, h]
  have h1_coord : h3ZornCoordinate h3_diag₂ r = if r.val = 1 then 1 else 0 := by
    rw [← h3ZornBasis_one, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 1
    · have : (1 : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (1 : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm; simp [this, h]
  have h2_coord : h3ZornCoordinate h3_diag₃ r = if r.val = 2 then 1 else 0 := by
    rw [← h3ZornBasis_two, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 2
    · have : (2 : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (2 : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm; simp [this, h]
  have h12_coord : ∀ i : Fin 8, h3ZornCoordinate (embedJ12 (zorn_basis i)) r =
      if r.val = 3 + i.val then 1 else 0 := by
    intro i; rw [← h3ZornBasis_12 i, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 3 + i.val
    · have : (⟨3 + i.val, by omega⟩ : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (⟨3 + i.val, by omega⟩ : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm
      simp [this, h]
  have h23_coord : ∀ i : Fin 8, h3ZornCoordinate (embedJ23 (zorn_basis i)) r =
      if r.val = 11 + i.val then 1 else 0 := by
    intro i; rw [← h3ZornBasis_23 i, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 11 + i.val
    · have : (⟨11 + i.val, by omega⟩ : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (⟨11 + i.val, by omega⟩ : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm
      simp [this, h]
  have h31_coord : ∀ i : Fin 8, h3ZornCoordinate (embedJ31 (zorn_basis i)) r =
      if r.val = 19 + i.val then 1 else 0 := by
    intro i; rw [← h3ZornBasis_31 i, h3ZornCoordinate_basis_self]
    by_cases h : r.val = 19 + i.val
    · have : (⟨19 + i.val, by omega⟩ : Fin 27) = r := Fin.ext h.symm; simp [this, h]
    · have : (⟨19 + i.val, by omega⟩ : Fin 27) ≠ r := fun he => h (congrArg Fin.val he).symm
      simp [this, h]
  cases s₁ with
  | diag d₁ =>
    cases s₂ with
    | diag d₂ =>
      fin_cases d₁ <;> fin_cases d₂ <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_h3_diag₁, h3_diag₂_mul_h3_diag₂,
          h3_diag₃_mul_h3_diag₃, h3_diag₁_mul_h3_diag₂, h3_diag₁_mul_h3_diag₃, h3_diag₂_mul_h3_diag₃,
          mul_comm h3_diag₂ h3_diag₁, mul_comm h3_diag₃ h3_diag₁, mul_comm h3_diag₃ h3_diag₂,
          smul_zero, h3ZornCoordinate_zero, h3ZornCoordinate_smul, h0_coord, h1_coord, h2_coord] <;>
        simp [twoLSectorFormula]
    | j12 i =>
      fin_cases d₁ <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12,
          h3_diag₃_mul_embedJ12, half2, smul_zero, h3ZornCoordinate_zero, h12_coord] <;>
        simp [twoLSectorFormula]
    | j23 i =>
      fin_cases d₁ <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ23, h3_diag₂_mul_embedJ23,
          h3_diag₃_mul_embedJ23, half2, smul_zero, h3ZornCoordinate_zero, h23_coord] <;>
        simp [twoLSectorFormula]
    | j31 i =>
      fin_cases d₁ <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ31, h3_diag₂_mul_embedJ31,
          h3_diag₃_mul_embedJ31, half2, smul_zero, h3ZornCoordinate_zero, h31_coord] <;>
        simp [twoLSectorFormula]
  | j12 i =>
    cases s₂ with
    | diag d =>
      rw [mul_comm]
      fin_cases d <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12,
          h3_diag₃_mul_embedJ12, half2, smul_zero, h3ZornCoordinate_zero, h12_coord] <;>
        simp [twoLSectorFormula]
    | j12 j =>
      simp only [h3ZornBasis_sector, embedJ12_mul_embedJ12, zornBilin_zorn_basis,
        h3ZornCoordinate_smul, h3ZornCoordinate_add, h0_coord, h1_coord, twoLSectorFormula]
      by_cases h0 : r.val = 0 <;> by_cases h1 : r.val = 1 <;> simp [h0, h1]
    | j23 j =>
      simp only [h3ZornBasis_sector, embedJ12_mul_embedJ23, half2, zornConjMul_zorn_basis,
        embedJ31_smul, h3ZornCoordinate_smul, h31_coord, twoLSectorFormula]
      split_ifs <;> simp
    | j31 j =>
      rw [mul_comm]
      simp only [h3ZornBasis_sector, embedJ31_mul_embedJ12, half2, zornConjMul_zorn_basis,
        embedJ23_smul, h3ZornCoordinate_smul, h23_coord, twoLSectorFormula]
      split_ifs <;> simp
  | j23 i =>
    cases s₂ with
    | diag d =>
      rw [mul_comm]
      fin_cases d <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ23, h3_diag₂_mul_embedJ23,
          h3_diag₃_mul_embedJ23, half2, smul_zero, h3ZornCoordinate_zero, h23_coord] <;>
        simp [twoLSectorFormula]
    | j12 j =>
      rw [mul_comm]
      simp only [h3ZornBasis_sector, embedJ12_mul_embedJ23, half2, zornConjMul_zorn_basis,
        embedJ31_smul, h3ZornCoordinate_smul, h31_coord, twoLSectorFormula]
      split_ifs <;> simp
    | j23 j =>
      simp only [h3ZornBasis_sector, embedJ23_mul_embedJ23, zornBilin_zorn_basis,
        h3ZornCoordinate_smul, h3ZornCoordinate_add, h1_coord, h2_coord, twoLSectorFormula]
      by_cases h1 : r.val = 1 <;> by_cases h2 : r.val = 2 <;> simp [h1, h2]
    | j31 j =>
      simp only [h3ZornBasis_sector, embedJ23_mul_embedJ31, half2, zornConjMul_zorn_basis,
        embedJ12_smul, h3ZornCoordinate_smul, h12_coord, twoLSectorFormula]
      split_ifs <;> simp
  | j31 i =>
    cases s₂ with
    | diag d =>
      rw [mul_comm]
      fin_cases d <;>
        simp only [h3ZornBasis_sector, h3_diag₁_mul_embedJ31, h3_diag₂_mul_embedJ31,
          h3_diag₃_mul_embedJ31, half2, smul_zero, h3ZornCoordinate_zero, h31_coord] <;>
        simp [twoLSectorFormula]
    | j12 j =>
      simp only [h3ZornBasis_sector, embedJ31_mul_embedJ12, half2, zornConjMul_zorn_basis,
        embedJ23_smul, h3ZornCoordinate_smul, h23_coord, twoLSectorFormula]
      split_ifs <;> simp
    | j23 j =>
      rw [mul_comm]
      simp only [h3ZornBasis_sector, embedJ23_mul_embedJ31, half2, zornConjMul_zorn_basis,
        embedJ12_smul, h3ZornCoordinate_smul, h12_coord, twoLSectorFormula]
      split_ifs <;> simp
    | j31 j =>
      simp only [h3ZornBasis_sector, embedJ31_mul_embedJ31, zornBilin_zorn_basis,
        h3ZornCoordinate_smul, h3ZornCoordinate_add, h2_coord, h0_coord, twoLSectorFormula]
      by_cases h2 : r.val = 2 <;> by_cases h0 : r.val = 0 <;> simp [h2, h0]

theorem h3zornToMatrix_two_jordanLmul_basis (p : Fin 27) :
    h3zornToMatrix ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) =
      (sparseToMat (twoLData p)).map Int.cast := by
  ext r q
  rw [h3zornToMatrix_apply, Matrix.map_apply]
  change h3ZornCoordinate ((2 : ℝ) • (h3ZornBasis p * h3ZornBasis q)) r = _
  rw [← finOfSector_sectorOfFin p, ← finOfSector_sectorOfFin q, h3ZornCoord_two_mul_sector,
    finOfSector_sectorOfFin p, finOfSector_sectorOfFin q, twoLSectorFormula_eq_sparseVal]
  rfl

end BasisAndOperatorMatrix

section RootSystemAndChevalley

inductive RootOpSpec
  | d4 (a b : Fin 8)
  | slot (s : Fin 3) (i : Fin 8) (sgn : ℤ)
  deriving DecidableEq

def e6RootSpec (r : Fin 72) : RootOpSpec :=
  match r.val with
  | 0 => .d4 0 1
  | 1 => .d4 0 2
  | 2 => .d4 0 3
  | 3 => .d4 0 4
  | 4 => .d4 0 5
  | 5 => .d4 0 6
  | 6 => .d4 1 2
  | 7 => .d4 1 3
  | 8 => .d4 1 5
  | 9 => .d4 1 6
  | 10 => .d4 1 7
  | 11 => .d4 2 3
  | 12 => .d4 2 4
  | 13 => .d4 2 6
  | 14 => .d4 2 7
  | 15 => .d4 3 4
  | 16 => .d4 3 5
  | 17 => .d4 3 7
  | 18 => .d4 4 5
  | 19 => .d4 4 6
  | 20 => .d4 4 7
  | 21 => .d4 5 6
  | 22 => .d4 5 7
  | 23 => .d4 6 7
  | 24 => .slot 0 0 1
  | 25 => .slot 0 0 (-1)
  | 26 => .slot 0 1 1
  | 27 => .slot 0 1 (-1)
  | 28 => .slot 0 2 1
  | 29 => .slot 0 2 (-1)
  | 30 => .slot 0 3 1
  | 31 => .slot 0 3 (-1)
  | 32 => .slot 0 4 1
  | 33 => .slot 0 4 (-1)
  | 34 => .slot 0 5 1
  | 35 => .slot 0 5 (-1)
  | 36 => .slot 0 6 1
  | 37 => .slot 0 6 (-1)
  | 38 => .slot 0 7 1
  | 39 => .slot 0 7 (-1)
  | 40 => .slot 1 0 1
  | 41 => .slot 1 0 (-1)
  | 42 => .slot 1 1 1
  | 43 => .slot 1 1 (-1)
  | 44 => .slot 1 2 1
  | 45 => .slot 1 2 (-1)
  | 46 => .slot 1 3 1
  | 47 => .slot 1 3 (-1)
  | 48 => .slot 1 4 1
  | 49 => .slot 1 4 (-1)
  | 50 => .slot 1 5 1
  | 51 => .slot 1 5 (-1)
  | 52 => .slot 1 6 1
  | 53 => .slot 1 6 (-1)
  | 54 => .slot 1 7 1
  | 55 => .slot 1 7 (-1)
  | 56 => .slot 2 0 1
  | 57 => .slot 2 0 (-1)
  | 58 => .slot 2 1 1
  | 59 => .slot 2 1 (-1)
  | 60 => .slot 2 2 1
  | 61 => .slot 2 2 (-1)
  | 62 => .slot 2 3 1
  | 63 => .slot 2 3 (-1)
  | 64 => .slot 2 4 1
  | 65 => .slot 2 4 (-1)
  | 66 => .slot 2 5 1
  | 67 => .slot 2 5 (-1)
  | 68 => .slot 2 6 1
  | 69 => .slot 2 6 (-1)
  | 70 => .slot 2 7 1
  | 71 => .slot 2 7 (-1)
  | _ => .d4 0 1

def rootOpFromSpec : RootOpSpec → h3zornCubicStabilizer
  | .d4 a b =>
    (2 : ℝ) • ⟨(h3ZornJordanInnerDerivation (h3_off₁₂ a) (h3_off₁₂ b) : Module.End ℝ (H3Zorn ℝ)),
      H3ZornF4Derivations_le_h3zornCubicStabilizer (h3ZornJordanInnerDerivation_mem_F4 _ _)⟩
  | .slot 0 i sgn =>
    ⟨jordanLmul (R := ℝ) (h3_off₁₂ i),
      (jordanLmul_mem_h3zornCubicStabilizer_iff (h3_off₁₂ i)).mpr (by simp [linearTrace, h3_off₁₂])⟩ +
    (2 * sgn : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ i) : Module.End ℝ (H3Zorn ℝ)),
      H3ZornF4Derivations_le_h3zornCubicStabilizer (h3ZornJordanInnerDerivation_mem_F4 _ _)⟩
  | .slot 1 i sgn =>
    ⟨jordanLmul (R := ℝ) (h3_off₂₃ i),
      (jordanLmul_mem_h3zornCubicStabilizer_iff (h3_off₂₃ i)).mpr (by simp [linearTrace, h3_off₂₃])⟩ +
    (2 * sgn : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ i) : Module.End ℝ (H3Zorn ℝ)),
      H3ZornF4Derivations_le_h3zornCubicStabilizer (h3ZornJordanInnerDerivation_mem_F4 _ _)⟩
  | .slot _ i sgn =>
    ⟨jordanLmul (R := ℝ) (h3_off₃₁ i),
      (jordanLmul_mem_h3zornCubicStabilizer_iff (h3_off₃₁ i)).mpr (by simp [linearTrace, h3_off₃₁])⟩ +
    (2 * sgn : ℝ) • ⟨(h3ZornJordanInnerDerivation h3_diag₃ (h3_off₃₁ i) : Module.End ℝ (H3Zorn ℝ)),
      H3ZornF4Derivations_le_h3zornCubicStabilizer (h3ZornJordanInnerDerivation_mem_F4 _ _)⟩

/-- The 72 Chevalley root operators inside `h3zornCubicStabilizer`. -/
def e6RootVec (r : Fin 72) : h3zornCubicStabilizer :=
  rootOpFromSpec (e6RootSpec r)

def rootDoubledSparse : RootOpSpec → SparseMat27
  | .d4 a b => sparseComm (twoLData ⟨3 + a.val, by omega⟩) (twoLData ⟨3 + b.val, by omega⟩)
  | .slot 0 i sgn =>
    sparseAdd (twoLData ⟨3 + i.val, by omega⟩)
      (sparseSmul sgn (sparseComm (twoLData 0) (twoLData ⟨3 + i.val, by omega⟩)))
  | .slot 1 i sgn =>
    sparseAdd (twoLData ⟨11 + i.val, by omega⟩)
      (sparseSmul sgn (sparseComm (twoLData 1) (twoLData ⟨11 + i.val, by omega⟩)))
  | .slot _ i sgn =>
    sparseAdd (twoLData ⟨19 + i.val, by omega⟩)
      (sparseSmul sgn (sparseComm (twoLData 2) (twoLData ⟨19 + i.val, by omega⟩)))

def e6RootSparse (r : Fin 72) : SparseMat27 :=
  match r.val with
  | 0 => [(3, 7, -1), (4, 10, -1), (16, 14, -1), (17, 13, 1), (20, 19, 1), (26, 23, 1)]
  | 1 => [(3, 8, -1), (5, 10, -1), (15, 14, 1), (17, 12, -1), (21, 19, 1), (26, 24, 1)]
  | 2 => [(3, 9, -1), (6, 10, -1), (15, 13, -1), (16, 12, 1), (22, 19, 1), (26, 25, 1)]
  | 3 => [(3, 4, -1), (7, 10, -1), (15, 11, 1), (18, 12, 1), (21, 25, -1), (22, 24, 1)]
  | 4 => [(3, 5, -1), (8, 10, -1), (16, 11, 1), (18, 13, 1), (20, 25, 1), (22, 23, -1)]
  | 5 => [(3, 6, -1), (9, 10, -1), (17, 11, 1), (18, 14, 1), (20, 24, -1), (21, 23, 1)]
  | 6 => [(4, 8, -1), (5, 7, 1), (11, 14, -1), (17, 18, -1), (25, 19, 1), (26, 22, 1)]
  | 7 => [(4, 9, -1), (6, 7, 1), (11, 13, 1), (16, 18, 1), (24, 19, -1), (26, 21, -1)]
  | 8 => [(4, 5, -1), (8, 7, 1), (12, 13, -1), (16, 15, 1), (20, 21, -1), (24, 23, 1)]
  | 9 => [(4, 6, -1), (9, 7, 1), (12, 14, -1), (17, 15, 1), (20, 22, -1), (25, 23, 1)]
  | 10 => [(4, 3, 1), (10, 7, 1), (11, 15, -1), (12, 18, -1), (24, 22, -1), (25, 21, 1)]
  | 11 => [(5, 9, -1), (6, 8, 1), (11, 12, -1), (15, 18, -1), (23, 19, 1), (26, 20, 1)]
  | 12 => [(5, 4, -1), (7, 8, 1), (13, 12, -1), (15, 16, 1), (21, 20, -1), (23, 24, 1)]
  | 13 => [(5, 6, -1), (9, 8, 1), (13, 14, -1), (17, 16, 1), (21, 22, -1), (25, 24, 1)]
  | 14 => [(5, 3, 1), (10, 8, 1), (11, 16, -1), (13, 18, -1), (23, 22, 1), (25, 20, -1)]
  | 15 => [(6, 4, -1), (7, 9, 1), (14, 12, -1), (15, 17, 1), (22, 20, -1), (23, 25, 1)]
  | 16 => [(6, 5, -1), (8, 9, 1), (14, 13, -1), (16, 17, 1), (22, 21, -1), (24, 25, 1)]
  | 17 => [(6, 3, 1), (10, 9, 1), (11, 17, -1), (14, 18, -1), (23, 21, -1), (24, 20, 1)]
  | 18 => [(7, 5, -1), (8, 4, 1), (14, 11, 1), (18, 17, 1), (19, 25, -1), (22, 26, -1)]
  | 19 => [(7, 6, -1), (9, 4, 1), (13, 11, -1), (18, 16, -1), (19, 24, 1), (21, 26, 1)]
  | 20 => [(7, 3, 1), (10, 4, 1), (13, 17, -1), (14, 16, 1), (19, 20, -1), (23, 26, -1)]
  | 21 => [(8, 6, -1), (9, 5, 1), (12, 11, 1), (18, 15, 1), (19, 23, -1), (20, 26, -1)]
  | 22 => [(8, 3, 1), (10, 5, 1), (12, 17, 1), (14, 15, -1), (19, 21, -1), (24, 26, -1)]
  | 23 => [(9, 3, 1), (10, 6, 1), (12, 16, -1), (13, 15, 1), (19, 22, -1), (25, 26, -1)]
  | 24 => [(0, 10, 1), (3, 1, 1), (20, 12, -1), (21, 13, -1), (22, 14, -1), (26, 11, 1)]
  | 25 => [(1, 10, 1), (3, 0, 1), (15, 23, -1), (16, 24, -1), (17, 25, -1), (18, 19, 1)]
  | 26 => [(0, 7, -1), (4, 1, 1), (20, 18, -1), (24, 14, 1), (25, 13, -1), (26, 15, 1)]
  | 27 => [(1, 7, -1), (4, 0, 1), (11, 23, 1), (12, 19, -1), (16, 22, -1), (17, 21, 1)]
  | 28 => [(0, 8, -1), (5, 1, 1), (21, 18, -1), (23, 14, -1), (25, 12, 1), (26, 16, 1)]
  | 29 => [(1, 8, -1), (5, 0, 1), (11, 24, 1), (13, 19, -1), (15, 22, 1), (17, 20, -1)]
  | 30 => [(0, 9, -1), (6, 1, 1), (22, 18, -1), (23, 13, 1), (24, 12, -1), (26, 17, 1)]
  | 31 => [(1, 9, -1), (6, 0, 1), (11, 25, 1), (14, 19, -1), (15, 21, -1), (16, 20, 1)]
  | 32 => [(0, 4, -1), (7, 1, 1), (19, 12, 1), (21, 17, -1), (22, 16, 1), (23, 11, -1)]
  | 33 => [(1, 4, -1), (7, 0, 1), (13, 25, 1), (14, 24, -1), (15, 26, -1), (18, 20, 1)]
  | 34 => [(0, 5, -1), (8, 1, 1), (19, 13, 1), (20, 17, 1), (22, 15, -1), (24, 11, -1)]
  | 35 => [(1, 5, -1), (8, 0, 1), (12, 25, -1), (14, 23, 1), (16, 26, -1), (18, 21, 1)]
  | 36 => [(0, 6, -1), (9, 1, 1), (19, 14, 1), (20, 16, -1), (21, 15, 1), (25, 11, -1)]
  | 37 => [(1, 6, -1), (9, 0, 1), (12, 24, 1), (13, 23, -1), (17, 26, -1), (18, 22, 1)]
  | 38 => [(0, 3, 1), (10, 1, 1), (19, 18, 1), (23, 15, -1), (24, 16, -1), (25, 17, -1)]
  | 39 => [(1, 3, 1), (10, 0, 1), (11, 26, 1), (12, 20, -1), (13, 21, -1), (14, 22, -1)]
  | 40 => [(1, 18, 1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (10, 19, 1), (11, 2, 1)]
  | 41 => [(2, 18, 1), (11, 1, 1), (23, 7, -1), (24, 8, -1), (25, 9, -1), (26, 3, 1)]
  | 42 => [(1, 15, -1), (4, 26, -1), (8, 22, 1), (9, 21, -1), (10, 23, 1), (12, 2, 1)]
  | 43 => [(2, 15, -1), (12, 1, 1), (19, 7, 1), (20, 3, -1), (24, 6, -1), (25, 5, 1)]
  | 44 => [(1, 16, -1), (5, 26, -1), (7, 22, -1), (9, 20, 1), (10, 24, 1), (13, 2, 1)]
  | 45 => [(2, 16, -1), (13, 1, 1), (19, 8, 1), (21, 3, -1), (23, 6, 1), (25, 4, -1)]
  | 46 => [(1, 17, -1), (6, 26, -1), (7, 21, 1), (8, 20, -1), (10, 25, 1), (14, 2, 1)]
  | 47 => [(2, 17, -1), (14, 1, 1), (19, 9, 1), (22, 3, -1), (23, 5, -1), (24, 4, 1)]
  | 48 => [(1, 12, -1), (3, 20, 1), (5, 25, -1), (6, 24, 1), (7, 19, -1), (15, 2, 1)]
  | 49 => [(2, 12, -1), (15, 1, 1), (21, 9, 1), (22, 8, -1), (23, 10, -1), (26, 4, 1)]
  | 50 => [(1, 13, -1), (3, 21, 1), (4, 25, 1), (6, 23, -1), (8, 19, -1), (16, 2, 1)]
  | 51 => [(2, 13, -1), (16, 1, 1), (20, 9, -1), (22, 7, 1), (24, 10, -1), (26, 5, 1)]
  | 52 => [(1, 14, -1), (3, 22, 1), (4, 24, -1), (5, 23, 1), (9, 19, -1), (17, 2, 1)]
  | 53 => [(2, 14, -1), (17, 1, 1), (20, 8, 1), (21, 7, -1), (25, 10, -1), (26, 6, 1)]
  | 54 => [(1, 11, 1), (3, 26, 1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (18, 2, 1)]
  | 55 => [(2, 11, 1), (18, 1, 1), (19, 10, 1), (20, 4, -1), (21, 5, -1), (22, 6, -1)]
  | 56 => [(2, 26, 1), (12, 4, -1), (13, 5, -1), (14, 6, -1), (18, 3, 1), (19, 0, 1)]
  | 57 => [(0, 26, 1), (7, 15, -1), (8, 16, -1), (9, 17, -1), (10, 11, 1), (19, 2, 1)]
  | 58 => [(2, 23, -1), (12, 10, -1), (16, 6, 1), (17, 5, -1), (18, 7, 1), (20, 0, 1)]
  | 59 => [(0, 23, -1), (3, 15, 1), (4, 11, -1), (8, 14, -1), (9, 13, 1), (20, 2, 1)]
  | 60 => [(2, 24, -1), (13, 10, -1), (15, 6, -1), (17, 4, 1), (18, 8, 1), (21, 0, 1)]
  | 61 => [(0, 24, -1), (3, 16, 1), (5, 11, -1), (7, 14, 1), (9, 12, -1), (21, 2, 1)]
  | 62 => [(2, 25, -1), (14, 10, -1), (15, 5, 1), (16, 4, -1), (18, 9, 1), (22, 0, 1)]
  | 63 => [(0, 25, -1), (3, 17, 1), (6, 11, -1), (7, 13, -1), (8, 12, 1), (22, 2, 1)]
  | 64 => [(2, 20, -1), (11, 4, 1), (13, 9, -1), (14, 8, 1), (15, 3, -1), (23, 0, 1)]
  | 65 => [(0, 20, -1), (5, 17, 1), (6, 16, -1), (7, 18, -1), (10, 12, 1), (23, 2, 1)]
  | 66 => [(2, 21, -1), (11, 5, 1), (12, 9, 1), (14, 7, -1), (16, 3, -1), (24, 0, 1)]
  | 67 => [(0, 21, -1), (4, 17, -1), (6, 15, 1), (8, 18, -1), (10, 13, 1), (24, 2, 1)]
  | 68 => [(2, 22, -1), (11, 6, 1), (12, 8, -1), (13, 7, 1), (17, 3, -1), (25, 0, 1)]
  | 69 => [(0, 22, -1), (4, 16, 1), (5, 15, -1), (9, 18, -1), (10, 14, 1), (25, 2, 1)]
  | 70 => [(2, 19, 1), (11, 10, 1), (15, 7, -1), (16, 8, -1), (17, 9, -1), (26, 0, 1)]
  | 71 => [(0, 19, 1), (3, 18, 1), (4, 12, -1), (5, 13, -1), (6, 14, -1), (26, 2, 1)]
  | _ => []

private theorem h3zornToMatrix_four_inner (p q : Fin 27) :
    h3zornToMatrix ((4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis p) (h3ZornBasis q) :
        Module.End ℝ (H3Zorn ℝ))) =
      (sparseToMat (sparseComm (twoLData p) (twoLData q))).map Int.cast := by
  have hinner : (h3ZornJordanInnerDerivation (h3ZornBasis p) (h3ZornBasis q) :
        Module.End ℝ (H3Zorn ℝ)) =
      jordanLmul (R := ℝ) (h3ZornBasis p) * jordanLmul (R := ℝ) (h3ZornBasis q) -
        jordanLmul (R := ℝ) (h3ZornBasis q) * jordanLmul (R := ℝ) (h3ZornBasis p) := by
    apply LinearMap.ext; intro x
    simp [h3ZornJordanInnerDerivation_apply, jordanLmul_apply]
  have h4 : (4 : ℝ) • (jordanLmul (R := ℝ) (h3ZornBasis p) * jordanLmul (R := ℝ) (h3ZornBasis q) -
        jordanLmul (R := ℝ) (h3ZornBasis q) * jordanLmul (R := ℝ) (h3ZornBasis p)) =
      ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) * ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis q)) -
        ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis q)) * ((2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis p)) := by
    simp only [smul_sub, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
    norm_num
  rw [hinner, h4, map_sub, map_mul, map_mul, h3zornToMatrix_two_jordanLmul_basis p,
    h3zornToMatrix_two_jordanLmul_basis q, sparseToMat_comm]
  ext i j
  simp [Matrix.mul_apply]

private theorem two_mul_two_sgn (sgn : ℝ) : (2 : ℝ) * (2 * sgn) = sgn * 4 := by ring

private theorem h3zornToMatrix_two_rootOpFromSpec (sp : RootOpSpec) :
    h3zornToMatrix ((2 : ℝ) • (rootOpFromSpec sp : Module.End ℝ (H3Zorn ℝ))) =
      (sparseToMat (rootDoubledSparse sp)).map Int.cast := by
  cases sp with
  | d4 a b =>
    have h22 : (2 : ℝ) • ((2 : ℝ) • (h3ZornJordanInnerDerivation (h3_off₁₂ a) (h3_off₁₂ b) :
          Module.End ℝ (H3Zorn ℝ))) =
        (4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis ⟨3 + a.val, by omega⟩)
          (h3ZornBasis ⟨3 + b.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ)) := by
      have ha : h3_off₁₂ a = h3ZornBasis ⟨3 + a.val, by omega⟩ := (h3ZornBasis_12 a).symm
      have hb : h3_off₁₂ b = h3ZornBasis ⟨3 + b.val, by omega⟩ := (h3ZornBasis_12 b).symm
      rw [ha, hb, smul_smul]
      norm_num
    change h3zornToMatrix ((2 : ℝ) • ((2 : ℝ) •
      (h3ZornJordanInnerDerivation (h3_off₁₂ a) (h3_off₁₂ b) : Module.End ℝ (H3Zorn ℝ)))) = _
    rw [h22, h3zornToMatrix_four_inner]
    rfl
  | slot s i sgn =>
    fin_cases s
    · have h2mul : (2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₁₂ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ i) :
              Module.End ℝ (H3Zorn ℝ))) =
          (2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨3 + i.val, by omega⟩) +
            (sgn : ℝ) • ((4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis 0)
              (h3ZornBasis ⟨3 + i.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ))) := by
        have h0 : h3_diag₁ = h3ZornBasis 0 := h3ZornBasis_zero.symm
        have hi : h3_off₁₂ i = h3ZornBasis ⟨3 + i.val, by omega⟩ := (h3ZornBasis_12 i).symm
        rw [h0, hi, smul_add, smul_smul, smul_smul, two_mul_two_sgn]
      dsimp only [rootOpFromSpec]
      change h3zornToMatrix ((2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₁₂ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₁ (h3_off₁₂ i) :
              Module.End ℝ (H3Zorn ℝ)))) =
        (sparseToMat (sparseAdd (twoLData ⟨3 + i.val, by omega⟩)
          (sparseSmul sgn (sparseComm (twoLData 0) (twoLData ⟨3 + i.val, by omega⟩))))).map Int.cast
      rw [h2mul, map_add, h3zornToMatrix_two_jordanLmul_basis, map_smul, h3zornToMatrix_four_inner,
        sparseToMat_add, sparseToMat_smul]
      ext r c; simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
    · have h2mul : (2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₂₃ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ i) :
              Module.End ℝ (H3Zorn ℝ))) =
          (2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨11 + i.val, by omega⟩) +
            (sgn : ℝ) • ((4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis 1)
              (h3ZornBasis ⟨11 + i.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ))) := by
        have h1 : h3_diag₂ = h3ZornBasis 1 := h3ZornBasis_one.symm
        have hi : h3_off₂₃ i = h3ZornBasis ⟨11 + i.val, by omega⟩ := (h3ZornBasis_23 i).symm
        rw [h1, hi, smul_add, smul_smul, smul_smul, two_mul_two_sgn]
      dsimp only [rootOpFromSpec]
      change h3zornToMatrix ((2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₂₃ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₂ (h3_off₂₃ i) :
              Module.End ℝ (H3Zorn ℝ)))) =
        (sparseToMat (sparseAdd (twoLData ⟨11 + i.val, by omega⟩)
          (sparseSmul sgn (sparseComm (twoLData 1) (twoLData ⟨11 + i.val, by omega⟩))))).map Int.cast
      rw [h2mul, map_add, h3zornToMatrix_two_jordanLmul_basis, map_smul, h3zornToMatrix_four_inner,
        sparseToMat_add, sparseToMat_smul]
      ext r c; simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
    · have h2mul : (2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₃₁ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₃ (h3_off₃₁ i) :
              Module.End ℝ (H3Zorn ℝ))) =
          (2 : ℝ) • jordanLmul (R := ℝ) (h3ZornBasis ⟨19 + i.val, by omega⟩) +
            (sgn : ℝ) • ((4 : ℝ) • (h3ZornJordanInnerDerivation (h3ZornBasis 2)
              (h3ZornBasis ⟨19 + i.val, by omega⟩) : Module.End ℝ (H3Zorn ℝ))) := by
        have h2 : h3_diag₃ = h3ZornBasis 2 := h3ZornBasis_two.symm
        have hi : h3_off₃₁ i = h3ZornBasis ⟨19 + i.val, by omega⟩ := (h3ZornBasis_31 i).symm
        rw [h2, hi, smul_add, smul_smul, smul_smul, two_mul_two_sgn]
      dsimp only [rootOpFromSpec]
      change h3zornToMatrix ((2 : ℝ) • (jordanLmul (R := ℝ) (h3_off₃₁ i) +
            (2 * sgn : ℝ) • (h3ZornJordanInnerDerivation h3_diag₃ (h3_off₃₁ i) :
              Module.End ℝ (H3Zorn ℝ)))) =
        (sparseToMat (sparseAdd (twoLData ⟨19 + i.val, by omega⟩)
          (sparseSmul sgn (sparseComm (twoLData 2) (twoLData ⟨19 + i.val, by omega⟩))))).map Int.cast
      rw [h2mul, map_add, h3zornToMatrix_two_jordanLmul_basis, map_smul, h3zornToMatrix_four_inner,
        sparseToMat_add, sparseToMat_smul]
      ext r c; simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]

private theorem e6RootSparse_check (r : Fin 72) :
    sparseEq (sparseSmul 2 (e6RootSparse r)) (rootDoubledSparse (e6RootSpec r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseSmul 2 (e6RootSparse r)) (rootDoubledSparse (e6RootSpec r))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

theorem h3zornToMatrix_e6RootVec (r : Fin 72) :
    h3zornToMatrix (e6RootVec r : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (e6RootSparse r)).map Int.cast := by
  have h2 := h3zornToMatrix_two_rootOpFromSpec (e6RootSpec r)
  have hsp := sparseToMat_eq_of_sparseEq (e6RootSparse_check r)
  rw [← hsp, sparseToMat_smul] at h2
  have h2' : (2 : ℝ) • h3zornToMatrix (e6RootVec r : Module.End ℝ (H3Zorn ℝ)) =
      (2 : ℝ) • (sparseToMat (e6RootSparse r)).map Int.cast := by
    rw [← map_smul]
    change h3zornToMatrix ((2 : ℝ) • (rootOpFromSpec (e6RootSpec r) : Module.End ℝ (H3Zorn ℝ))) = _
    rw [h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_ofNat]
  exact smul_right_injective _ (two_ne_zero : (2 : ℝ) ≠ 0) h2'

theorem e6RootVec_sq_zero (r : Fin 72) :
    (e6RootVec r : Module.End ℝ (H3Zorn ℝ)) ^ 2 = 0 := by
  have hsq : ∀ r : Fin 72, sparseZeroCheck (sparseMul (e6RootSparse r) (e6RootSparse r)) = true := by
    have h : (List.finRange 72).all (fun r =>
        sparseZeroCheck (sparseMul (e6RootSparse r) (e6RootSparse r))) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
    exact h
  apply h3zornToMatrix.injective
  rw [map_pow, h3zornToMatrix_e6RootVec, map_zero, sq]
  have hmul : (sparseToMat (e6RootSparse r)).map (Int.cast : ℤ → ℝ) *
      (sparseToMat (e6RootSparse r)).map Int.cast =
      (sparseToMat (sparseMul (e6RootSparse r) (e6RootSparse r))).map Int.cast := by
    rw [sparseToMat_mul]
    ext a b; simp [Matrix.mul_apply]
  rw [hmul, sparseToMat_eq_zero_of_sparseZeroCheck (hsq r)]
  ext a b; simp

def eSimpleIdx (i : Fin 6) : Fin 72 :=
  match i.val with
  | 0 => 71 | 1 => 12 | 2 => 37 | 3 => 16 | 4 => 36 | 5 => 70 | _ => 71

def fSimpleIdx (i : Fin 6) : Fin 72 :=
  match i.val with
  | 0 => 56 | 1 => 8 | 2 => 30 | 3 => 13 | 4 => 31 | 5 => 57 | _ => 56

def fSimpleSign (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 1 | 1 => 1 | 2 => -1 | 3 => 1 | 4 => -1 | 5 => 1 | _ => 1

def e6HighestRootIdx : Fin 72 := 3

def e6SimpleE (i : Fin 6) : h3zornCubicStabilizer :=
  e6RootVec (eSimpleIdx i)

def e6SimpleF (i : Fin 6) : h3zornCubicStabilizer :=
  (fSimpleSign i : ℝ) • e6RootVec (fSimpleIdx i)

def e6SimpleH (i : Fin 6) : h3zornCubicStabilizer :=
  ⁅e6SimpleE i, e6SimpleF i⁆

def e6SimpleESparse (i : Fin 6) : SparseMat27 :=
  e6RootSparse (eSimpleIdx i)

def e6SimpleFSparse (i : Fin 6) : SparseMat27 :=
  sparseSmul (fSimpleSign i) (e6RootSparse (fSimpleIdx i))

def e6SimpleHSparse (i : Fin 6) : SparseMat27 :=
  sparseComm (e6SimpleESparse i) (e6SimpleFSparse i)

theorem h3zornToMatrix_e6SimpleE (i : Fin 6) :
    h3zornToMatrix (e6SimpleE i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (e6SimpleESparse i)).map Int.cast :=
  h3zornToMatrix_e6RootVec (eSimpleIdx i)

theorem h3zornToMatrix_e6SimpleF (i : Fin 6) :
    h3zornToMatrix (e6SimpleF i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (e6SimpleFSparse i)).map Int.cast := by
  change h3zornToMatrix ((fSimpleSign i : ℝ) • (e6RootVec (fSimpleIdx i) : Module.End ℝ (H3Zorn ℝ))) = _
  rw [map_smul, h3zornToMatrix_e6RootVec, e6SimpleFSparse, sparseToMat_smul]
  ext r c; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem h3zornToMatrix_lie (X Y : h3zornCubicStabilizer) :
    h3zornToMatrix (⁅X, Y⁆ : Module.End ℝ (H3Zorn ℝ)) =
      h3zornToMatrix X * h3zornToMatrix Y - h3zornToMatrix Y * h3zornToMatrix X := by
  change h3zornToMatrix ((X.1 : Module.End ℝ (H3Zorn ℝ)) * Y.1 - Y.1 * X.1) = _
  rw [map_sub, map_mul, map_mul]

private theorem h3zornToMatrix_sub_lie (X Y : h3zornCubicStabilizer) :
    h3zornToMatrix (⁅X, Y⁆.1) =
      h3zornToMatrix X.1 * h3zornToMatrix Y.1 - h3zornToMatrix Y.1 * h3zornToMatrix X.1 :=
  h3zornToMatrix_lie X Y

theorem h3zornToMatrix_e6SimpleH (i : Fin 6) :
    h3zornToMatrix (e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) =
      (sparseToMat (e6SimpleHSparse i)).map Int.cast := by
  change h3zornToMatrix (⁅e6SimpleE i, e6SimpleF i⁆ : Module.End ℝ (H3Zorn ℝ)) = _
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleF,
    e6SimpleHSparse, sparseToMat_comm]
  ext r c; simp [Matrix.mul_apply]

def h3zornWeight (k : Fin 27) (i : Fin 6) : ℤ :=
  match k.val, i.val with

  | 0, 0 => 1
  | 0, 2 => -1
  | 0, 4 => 1
  | 0, 5 => -1
  | 1, 2 => 1
  | 1, 4 => -1
  | 2, 0 => -1
  | 2, 5 => 1
  | 3, 0 => 1
  | 4, 0 => 1
  | 4, 1 => -1
  | 5, 0 => 1
  | 5, 1 => 1
  | 5, 3 => -1
  | 6, 0 => 1
  | 6, 2 => -1
  | 6, 3 => 1
  | 6, 4 => -1
  | 7, 1 => 1
  | 7, 5 => -1
  | 8, 1 => -1
  | 8, 3 => 1
  | 8, 5 => -1
  | 9, 2 => 1
  | 9, 3 => -1
  | 9, 4 => 1
  | 9, 5 => -1
  | 10, 5 => -1
  | 11, 4 => -1
  | 11, 5 => 1
  | 12, 0 => -1
  | 12, 1 => -1
  | 12, 2 => 1
  | 13, 0 => -1
  | 13, 1 => 1
  | 13, 2 => 1
  | 13, 3 => -1
  | 14, 0 => -1
  | 14, 3 => 1
  | 14, 4 => -1
  | 15, 1 => 1
  | 15, 4 => -1
  | 15, 5 => 1
  | 16, 1 => -1
  | 16, 3 => 1
  | 16, 4 => -1
  | 16, 5 => 1
  | 17, 2 => 1
  | 17, 3 => -1
  | 17, 5 => 1
  | 18, 0 => -1
  | 18, 2 => 1
  | 19, 0 => -1
  | 19, 4 => 1
  | 19, 5 => -1
  | 20, 1 => -1
  | 20, 4 => 1
  | 21, 1 => 1
  | 21, 3 => -1
  | 21, 4 => 1
  | 22, 2 => -1
  | 22, 3 => 1
  | 23, 1 => 1
  | 23, 2 => -1
  | 24, 1 => -1
  | 24, 2 => -1
  | 24, 3 => 1
  | 25, 3 => -1
  | 25, 4 => 1
  | 26, 0 => 1
  | 26, 2 => -1
  | 26, 5 => 1
  | _, _ => 0


theorem e6SimpleH_diag (i : Fin 6) (r c : Fin 27) :
    sparseToMat (e6SimpleHSparse i) r c = if r = c then h3zornWeight r i else 0 := by
  have h : (List.finRange 6).all (fun i =>
      (List.finRange 27).all (fun r =>
        (List.finRange 27).all (fun c =>
          sparseToMat (e6SimpleHSparse i) r c == if r = c then h3zornWeight r i else 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact h i r c

theorem e6SimpleH_apply_basis (i : Fin 6) (k : Fin 27) :
    (e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis k) =
      (h3zornWeight k i : ℝ) • h3ZornBasis k := by
  apply h3ZornBasis.ext_elem
  intro r
  have h1 : h3ZornBasis.repr ((e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis k)) r =
      h3zornToMatrix (e6SimpleH i : Module.End ℝ (H3Zorn ℝ)) r k := by
    rw [h3zornToMatrix_apply]; rfl
  rw [h1, h3zornToMatrix_e6SimpleH, Matrix.map_apply, e6SimpleH_diag, map_smul,
    Finsupp.smul_apply, h3ZornBasis.repr_self, Finsupp.single_apply, smul_eq_mul]
  by_cases hrk : r = k
  · subst hrk; simp
  · have hkr : k ≠ r := fun h => hrk h.symm
    simp [hrk, hkr]

theorem e6SimpleH_comm (i j : Fin 6) : ⁅e6SimpleH i, e6SimpleH j⁆ = 0 := by
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleH i, e6SimpleH j⁆ : Module.End ℝ (H3Zorn ℝ)) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleH, h3zornToMatrix_e6SimpleH, map_zero]
  ext r c
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, e6SimpleH_diag, Matrix.zero_apply]
  rw [Finset.sum_eq_single r, Finset.sum_eq_single r]
  · simp [mul_comm]
  · intro x _ hxr; simp [hxr.symm]
  · intro hr; exact absurd (Finset.mem_univ r) hr
  · intro x _ hxr; simp [hxr.symm]
  · intro hr; exact absurd (Finset.mem_univ r) hr

/-- The 6-dimensional split Cartan subalgebra of `h3zornCubicStabilizer`. -/
def h3zornCartan : LieSubalgebra ℝ h3zornCubicStabilizer where
  toSubmodule := Submodule.span ℝ (Set.range e6SimpleH)
  lie_mem' := by
    intro x y hx hy
    change x ∈ Submodule.span ℝ (Set.range e6SimpleH) at hx
    change y ∈ Submodule.span ℝ (Set.range e6SimpleH) at hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add x₁ x₂ _ _ ih₁ ih₂ => rw [add_lie]; exact Submodule.add_mem _ ih₁ ih₂
    | smul c x _ ih => rw [smul_lie]; exact Submodule.smul_mem _ c ih
    | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add y₁ y₂ _ _ ih₁ ih₂ => rw [lie_add]; exact Submodule.add_mem _ ih₁ ih₂
      | smul c y _ ih => rw [lie_smul]; exact Submodule.smul_mem _ c ih
      | mem y hy =>
        rcases hy with ⟨j, rfl⟩
        rw [e6SimpleH_comm]
        exact Submodule.zero_mem _

@[simp] theorem e6SimpleH_mem_h3zornCartan (i : Fin 6) : e6SimpleH i ∈ h3zornCartan :=
  Submodule.subset_span ⟨i, rfl⟩

instance : IsLieAbelian h3zornCartan where
  trivial x y := by
    apply Subtype.ext
    rcases x with ⟨xv, hx⟩
    rcases y with ⟨yv, hy⟩
    change ⁅xv, yv⁆ = 0
    change xv ∈ Submodule.span ℝ (Set.range e6SimpleH) at hx
    change yv ∈ Submodule.span ℝ (Set.range e6SimpleH) at hy
    induction hx using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ ih₁ ih₂ => rw [add_lie, ih₁, ih₂, add_zero]
    | smul c _ _ ih => rw [smul_lie, ih, smul_zero]
    | mem _ hx =>
      rcases hx with ⟨i, rfl⟩
      induction hy using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ ih₁ ih₂ => rw [lie_add, ih₁, ih₂, add_zero]
      | smul c _ _ ih => rw [lie_smul, ih, smul_zero]
      | mem _ hy =>
        rcases hy with ⟨j, rfl⟩
        exact e6SimpleH_comm i j

def e6RootCoord (r : Fin 72) : Fin 6 → ℤ :=
  match r.val with
  | 0 => ![1, 0, 1, 1, 1, 1]
  | 1 => ![1, 1, 1, 1, 1, 1]
  | 2 => ![1, 1, 1, 2, 1, 1]
  | 3 => ![1, 2, 2, 3, 2, 1]
  | 4 => ![1, 1, 2, 3, 2, 1]
  | 5 => ![1, 1, 2, 2, 2, 1]
  | 6 => ![0, -1, -1, -2, -1, 0]
  | 7 => ![0, -1, -1, -1, -1, 0]
  | 8 => ![0, -1, 0, 0, 0, 0]
  | 9 => ![0, -1, 0, -1, 0, 0]
  | 10 => ![-1, -2, -2, -3, -2, -1]
  | 11 => ![0, 0, -1, -1, -1, 0]
  | 12 => ![0, 1, 0, 0, 0, 0]
  | 13 => ![0, 0, 0, -1, 0, 0]
  | 14 => ![-1, -1, -2, -3, -2, -1]
  | 15 => ![0, 1, 0, 1, 0, 0]
  | 16 => ![0, 0, 0, 1, 0, 0]
  | 17 => ![-1, -1, -2, -2, -2, -1]
  | 18 => ![0, 1, 1, 2, 1, 0]
  | 19 => ![0, 1, 1, 1, 1, 0]
  | 20 => ![-1, 0, -1, -1, -1, -1]
  | 21 => ![0, 0, 1, 1, 1, 0]
  | 22 => ![-1, -1, -1, -1, -1, -1]
  | 23 => ![-1, -1, -1, -2, -1, -1]
  | 24 => ![1, 1, 1, 2, 2, 1]
  | 25 => ![1, 1, 2, 2, 1, 1]
  | 26 => ![0, -1, -1, -1, 0, 0]
  | 27 => ![0, -1, 0, -1, -1, 0]
  | 28 => ![0, 0, -1, -1, 0, 0]
  | 29 => ![0, 0, 0, -1, -1, 0]
  | 30 => ![0, 0, -1, 0, 0, 0]
  | 31 => ![0, 0, 0, 0, -1, 0]
  | 32 => ![0, 1, 0, 1, 1, 0]
  | 33 => ![0, 1, 1, 1, 0, 0]
  | 34 => ![0, 0, 0, 1, 1, 0]
  | 35 => ![0, 0, 1, 1, 0, 0]
  | 36 => ![0, 0, 0, 0, 1, 0]
  | 37 => ![0, 0, 1, 0, 0, 0]
  | 38 => ![-1, -1, -2, -2, -1, -1]
  | 39 => ![-1, -1, -1, -2, -2, -1]
  | 40 => ![0, -1, -1, -2, -2, -1]
  | 41 => ![-1, -1, -2, -2, -1, 0]
  | 42 => ![0, -1, 0, -1, -1, -1]
  | 43 => ![-1, -1, -1, -1, 0, 0]
  | 44 => ![0, 0, 0, -1, -1, -1]
  | 45 => ![-1, 0, -1, -1, 0, 0]
  | 46 => ![0, 0, 0, 0, -1, -1]
  | 47 => ![-1, 0, -1, 0, 0, 0]
  | 48 => ![1, 1, 1, 1, 0, 0]
  | 49 => ![0, 1, 0, 1, 1, 1]
  | 50 => ![1, 0, 1, 1, 0, 0]
  | 51 => ![0, 0, 0, 1, 1, 1]
  | 52 => ![1, 0, 1, 0, 0, 0]
  | 53 => ![0, 0, 0, 0, 1, 1]
  | 54 => ![1, 1, 2, 2, 1, 0]
  | 55 => ![0, 1, 1, 2, 2, 1]
  | 56 => ![-1, 0, 0, 0, 0, 0]
  | 57 => ![0, 0, 0, 0, 0, -1]
  | 58 => ![0, 0, 1, 1, 1, 1]
  | 59 => ![1, 0, 1, 1, 1, 0]
  | 60 => ![0, 1, 1, 1, 1, 1]
  | 61 => ![1, 1, 1, 1, 1, 0]
  | 62 => ![0, 1, 1, 2, 1, 1]
  | 63 => ![1, 1, 1, 2, 1, 0]
  | 64 => ![-1, 0, -1, -1, -1, 0]
  | 65 => ![0, 0, -1, -1, -1, -1]
  | 66 => ![-1, -1, -1, -1, -1, 0]
  | 67 => ![0, -1, -1, -1, -1, -1]
  | 68 => ![-1, -1, -1, -2, -1, 0]
  | 69 => ![0, -1, -1, -2, -1, -1]
  | 70 => ![0, 0, 0, 0, 0, 1]
  | 71 => ![1, 0, 0, 0, 0, 0]
  | _ => ![0, 0, 0, 0, 0, 0]

def e6RootCertIdx (r : Fin 72) : Fin 72 :=
  match r.val with
  | 0 => 40
  | 1 => 49
  | 2 => 56
  | 3 => 70
  | 4 => 68
  | 5 => 66
  | 6 => 50
  | 7 => 41
  | 8 => 8
  | 9 => 19
  | 10 => 71
  | 11 => 34
  | 12 => 1
  | 13 => 12
  | 14 => 69
  | 15 => 9
  | 16 => 3
  | 17 => 67
  | 18 => 43
  | 19 => 32
  | 20 => 47
  | 21 => 23
  | 22 => 54
  | 23 => 60
  | 24 => 62
  | 25 => 61
  | 26 => 30
  | 27 => 31
  | 28 => 22
  | 29 => 24
  | 30 => 10
  | 31 => 14
  | 32 => 21
  | 33 => 20
  | 34 => 13
  | 35 => 11
  | 36 => 4
  | 37 => 2
  | 38 => 64
  | 39 => 65
  | 40 => 63
  | 41 => 59
  | 42 => 42
  | 43 => 37
  | 44 => 36
  | 45 => 27
  | 46 => 26
  | 47 => 17
  | 48 => 28
  | 49 => 33
  | 50 => 18
  | 51 => 25
  | 52 => 7
  | 53 => 15
  | 54 => 55
  | 55 => 58
  | 56 => 6
  | 57 => 16
  | 58 => 35
  | 59 => 29
  | 60 => 44
  | 61 => 39
  | 62 => 52
  | 63 => 48
  | 64 => 38
  | 65 => 45
  | 66 => 46
  | 67 => 51
  | 68 => 53
  | 69 => 57
  | 70 => 5
  | 71 => 0
  | _ => 0

theorem e6RootCoord_eq_cert (r : Fin 72) :
    e6RootCoord r = e6Certificate.root (e6RootCertIdx r).val := by
  have h : (List.finRange 72).all (fun r =>
      List.ofFn (e6RootCoord r) == List.ofFn (e6Certificate.root (e6RootCertIdx r).val)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  exact List.ofFn_injective (h r)

private theorem e6Certificate_roots_length : e6Certificate.roots.length = 72 := by decide

theorem e6RootCoord_isRoot (r : Fin 72) : IsRoot .E6 (e6RootCoord r) := by
  rw [e6RootCoord_eq_cert r]
  exact RootCertificate.isRoot_root e6Certificate_check (e6RootCertIdx r).val
    (Nat.lt_of_lt_of_eq (e6RootCertIdx r).isLt e6Certificate_roots_length.symm)

theorem e6RootCoord_injective : Function.Injective e6RootCoord := by
  have h : (List.finRange 72).all (fun r₁ =>
      (List.finRange 72).all (fun r₂ =>
        if r₁ = r₂ then true else !(List.ofFn (e6RootCoord r₁) == List.ofFn (e6RootCoord r₂)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  intro r₁ r₂ heq
  by_contra hne
  have h12 := h r₁ r₂
  simp [hne, heq] at h12

/-- Canonical bijection between the 72 Albert root operators and `CFSGPort` `E₆` roots. -/
def e6RootEquiv : Fin 72 ≃ {v : Fin 6 → ℤ // IsRoot .E6 v} :=
  letI : Fintype {v : Fin 6 → ℤ // IsRoot .E6 v} :=
    (inferInstance : Fintype {v : Fin (Tag.rank .E6) → ℤ // IsRoot .E6 v})
  Equiv.ofBijective (fun r => ⟨e6RootCoord r, e6RootCoord_isRoot r⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun _ _ h => e6RootCoord_injective (congrArg Subtype.val h),
       by rw [Fintype.card_fin]; exact (card_isRoot .E6).symm⟩)

def rootEigenvalue (i : Fin 6) (r : Fin 72) : ℤ :=
  ∑ j : Fin 6, Tag.cartan .E6 i j * e6RootCoord r j

private theorem e6RootBracket_check_0 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 0) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 0 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 0) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 0 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem e6RootBracket_check_1 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 1) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 1 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 1) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 1 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem e6RootBracket_check_2 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 2) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 2 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 2) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 2 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem e6RootBracket_check_3 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 3) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 3 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 3) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 3 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem e6RootBracket_check_4 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 4) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 4 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 4) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 4 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

private theorem e6RootBracket_check_5 (r : Fin 72) :
    sparseEq (sparseComm (e6SimpleHSparse 5) (e6RootSparse r))
      (sparseSmul (rootEigenvalue 5 r) (e6RootSparse r)) = true := by
  have h : (List.finRange 72).all (fun r =>
      sparseEq (sparseComm (e6SimpleHSparse 5) (e6RootSparse r))
        (sparseSmul (rootEigenvalue 5 r) (e6RootSparse r))) = true := by decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  exact h r

theorem e6RootVec_bracket_H (i : Fin 6) (r : Fin 72) :
    ⁅e6SimpleH i, e6RootVec r⁆ = (rootEigenvalue i r : ℝ) • e6RootVec r := by
  have hchk : sparseEq (sparseComm (e6SimpleHSparse i) (e6RootSparse r))
      (sparseSmul (rootEigenvalue i r) (e6RootSparse r)) = true := by
    fin_cases i
    · exact e6RootBracket_check_0 r
    · exact e6RootBracket_check_1 r
    · exact e6RootBracket_check_2 r
    · exact e6RootBracket_check_3 r
    · exact e6RootBracket_check_4 r
    · exact e6RootBracket_check_5 r
  apply Subtype.ext
  apply h3zornToMatrix.injective
  rw [h3zornToMatrix_sub_lie, h3zornToMatrix_e6SimpleH, h3zornToMatrix_e6RootVec]
  have hcomm : (sparseToMat (e6SimpleHSparse i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6RootSparse r)).map Int.cast -
      (sparseToMat (e6RootSparse r)).map Int.cast *
        (sparseToMat (e6SimpleHSparse i)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleHSparse i) (e6RootSparse r))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, SetLike.val_smul, map_smul, h3zornToMatrix_e6RootVec,
    sparseToMat_eq_of_sparseEq hchk, sparseToMat_smul]
  ext a b; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

theorem e6Simple_bracket_EF_same (i : Fin 6) : ⁅e6SimpleE i, e6SimpleF i⁆ = e6SimpleH i := rfl

theorem e6Simple_bracket_EF_ne {i j : Fin 6} (hij : i ≠ j) :
    ⁅e6SimpleE i, e6SimpleF j⁆ = 0 := by
  have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if i = j then true else sparseZeroCheck (sparseComm (e6SimpleESparse i) (e6SimpleFSparse j)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h0 := hchk i j
  simp only [hij, ↓reduceIte] at h0
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (⁅e6SimpleE i, e6SimpleF j⁆ : Module.End ℝ (H3Zorn ℝ)) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [h3zornToMatrix_lie, h3zornToMatrix_e6SimpleE, h3zornToMatrix_e6SimpleF, map_zero]
  have hcomm : (sparseToMat (e6SimpleESparse i)).map (Int.cast : ℤ → ℝ) *
        (sparseToMat (e6SimpleFSparse j)).map Int.cast -
      (sparseToMat (e6SimpleFSparse j)).map Int.cast *
        (sparseToMat (e6SimpleESparse i)).map Int.cast =
      (sparseToMat (sparseComm (e6SimpleESparse i) (e6SimpleFSparse j))).map Int.cast := by
    rw [sparseToMat_comm]
    ext a b; simp [Matrix.mul_apply]
  rw [hcomm, sparseToMat_eq_zero_of_sparseZeroCheck h0]
  ext a b; simp

theorem e6Simple_bracket_HE (i j : Fin 6) :
    ⁅e6SimpleH i, e6SimpleE j⁆ = ((Tag.cartan .E6 i j : ℤ) : ℝ) • e6SimpleE j := by
  have hwt : rootEigenvalue i (eSimpleIdx j) = Tag.cartan .E6 i j := by
    have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
        rootEigenvalue i (eSimpleIdx j) == Tag.cartan .E6 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  simpa [e6SimpleE, hwt] using e6RootVec_bracket_H i (eSimpleIdx j)

theorem e6Simple_bracket_HF (i j : Fin 6) :
    ⁅e6SimpleH i, e6SimpleF j⁆ = (-(Tag.cartan .E6 i j : ℤ) : ℝ) • e6SimpleF j := by
  have hwt : rootEigenvalue i (fSimpleIdx j) = -Tag.cartan .E6 i j := by
    have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
        rootEigenvalue i (fSimpleIdx j) == -Tag.cartan .E6 i j)) = true := by
      decide
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
    exact hchk i j
  change ⁅e6SimpleH i, (fSimpleSign j : ℝ) • e6RootVec (fSimpleIdx j)⁆ = _
  rw [lie_smul, e6RootVec_bracket_H i (fSimpleIdx j), hwt]
  simp only [e6SimpleF, Int.cast_neg, smul_smul, mul_comm]

theorem e6Simple_serre_E {i j : Fin 6} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e6SimpleE i, x⁆) (1 - Tag.cartan .E6 i j).toNat) (e6SimpleE j) = 0 := by
  have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if i = j then true else
        let n := (1 - Tag.cartan .E6 i j).toNat
        sparseZeroCheck (Nat.iterate (fun s => sparseComm (e6SimpleESparse i) s) n (e6SimpleESparse j)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h0 := hchk i j
  simp only [hij, ↓reduceIte] at h0
  have hmat : ∀ (n : ℕ) (x : h3zornCubicStabilizer) (sx : SparseMat27),
      h3zornToMatrix (x : Module.End ℝ (H3Zorn ℝ)) = (sparseToMat sx).map Int.cast →
      h3zornToMatrix ((Nat.iterate (fun y => ⁅e6SimpleE i, y⁆) n x : h3zornCubicStabilizer) :
        Module.End ℝ (H3Zorn ℝ)) =
        (sparseToMat (Nat.iterate (fun s => sparseComm (e6SimpleESparse i) s) n sx)).map Int.cast := by
    intro n x sx hsx
    induction n generalizing x sx with
    | zero => exact hsx
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [h3zornToMatrix_sub_lie, h3zornToMatrix_e6SimpleE, ih x sx hsx, sparseToMat_comm]
      ext r c; simp [Matrix.mul_apply]
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (((Nat.iterate (fun x => ⁅e6SimpleE i, x⁆) (1 - Tag.cartan .E6 i j).toNat)
      (e6SimpleE j) : h3zornCubicStabilizer).1) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [hmat _ (e6SimpleE j) (e6SimpleESparse j) (h3zornToMatrix_e6SimpleE j),
    sparseToMat_eq_zero_of_sparseZeroCheck h0, map_zero]
  ext r c; simp

theorem e6Simple_serre_F {i j : Fin 6} (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e6SimpleF i, x⁆) (1 - Tag.cartan .E6 i j).toNat) (e6SimpleF j) = 0 := by
  have hchk : (List.finRange 6).all (fun i => (List.finRange 6).all (fun j =>
      if i = j then true else
        let n := (1 - Tag.cartan .E6 i j).toNat
        sparseZeroCheck (Nat.iterate (fun s => sparseComm (e6SimpleFSparse i) s) n (e6SimpleFSparse j)))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  have h0 := hchk i j
  simp only [hij, ↓reduceIte] at h0
  have hmat : ∀ (n : ℕ) (x : h3zornCubicStabilizer) (sx : SparseMat27),
      h3zornToMatrix (x : Module.End ℝ (H3Zorn ℝ)) = (sparseToMat sx).map Int.cast →
      h3zornToMatrix ((Nat.iterate (fun y => ⁅e6SimpleF i, y⁆) n x : h3zornCubicStabilizer) :
        Module.End ℝ (H3Zorn ℝ)) =
        (sparseToMat (Nat.iterate (fun s => sparseComm (e6SimpleFSparse i) s) n sx)).map Int.cast := by
    intro n x sx hsx
    induction n generalizing x sx with
    | zero => exact hsx
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [h3zornToMatrix_sub_lie, h3zornToMatrix_e6SimpleF, ih x sx hsx, sparseToMat_comm]
      ext r c; simp [Matrix.mul_apply]
  apply Subtype.ext
  apply h3zornToMatrix.injective
  change h3zornToMatrix (((Nat.iterate (fun x => ⁅e6SimpleF i, x⁆) (1 - Tag.cartan .E6 i j).toNat)
      (e6SimpleF j) : h3zornCubicStabilizer).1) =
    h3zornToMatrix (0 : Module.End ℝ (H3Zorn ℝ))
  rw [hmat _ (e6SimpleF j) (e6SimpleFSparse j) (h3zornToMatrix_e6SimpleF j),
    sparseToMat_eq_zero_of_sparseZeroCheck h0, map_zero]
  ext r c; simp

private theorem rootEigenvalue_ne_zero (r : Fin 72) : ∃ i : Fin 6, rootEigenvalue i r ≠ 0 := by
  have h : (List.finRange 72).all (fun r =>
      (List.finRange 6).any (fun i => rootEigenvalue i r != 0)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨i, _, hi⟩ := h r
  exact ⟨i, hi⟩

private theorem rootEigenvalue_eq_imp {r₁ r₂ : Fin 72}
    (h : ∀ i : Fin 6, rootEigenvalue i r₁ = rootEigenvalue i r₂) : r₁ = r₂ := by
  have hchk : (List.finRange 72).all (fun r₁ => (List.finRange 72).all (fun r₂ =>
      if r₁ = r₂ then true else
        (List.finRange 6).any (fun i => rootEigenvalue i r₁ != rootEigenvalue i r₂))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hchk
  by_contra hne
  have h12 := hchk r₁ r₂
  simp only [hne, ↓reduceIte, List.any_eq_true, List.mem_finRange, true_and, bne_iff_ne, ne_eq] at h12
  obtain ⟨i, hi⟩ := h12
  exact hi (h i)



theorem e6SimpleH_linearIndependent : LinearIndependent ℝ e6SimpleH := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hdiag : ∀ k : Fin 27, ∑ i : Fin 6, c i * (h3zornWeight k i : ℝ) = 0 := by
    intro k
    have h0 := congrArg (fun x : h3zornCubicStabilizer =>
      (x.1 : Module.End ℝ (H3Zorn ℝ)) (h3ZornBasis k)) hc
    simp only [ZeroMemClass.coe_zero, LinearMap.zero_apply] at h0
    have hl : (∑ i : Fin 6, c i • e6SimpleH i).1 (h3ZornBasis k) =
        ∑ i : Fin 6, (c i * (h3zornWeight k i : ℝ)) • h3ZornBasis k := by
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, e6SimpleH_apply_basis, smul_smul]
    rw [hl, ← Finset.sum_smul] at h0
    exact (smul_eq_zero.mp h0).resolve_right (h3ZornBasis.ne_zero k)
  have eq3 := hdiag 3
  have eq4 := hdiag 4
  have eq10 := hdiag 10
  have eq11 := hdiag 11
  have eq1 := hdiag 1
  have eq5 := hdiag 5
  simp only [Fin.sum_univ_six] at eq3 eq4 eq10 eq11 eq1 eq5
  have hc0 : c 0 = 0 := by
    have h0' : h3zornWeight 3 0 = 1 := rfl
    have h1' : h3zornWeight 3 1 = 0 := rfl
    have h2' : h3zornWeight 3 2 = 0 := rfl
    have h3' : h3zornWeight 3 3 = 0 := rfl
    have h4' : h3zornWeight 3 4 = 0 := rfl
    have h5' : h3zornWeight 3 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5'] at eq3
    simp at eq3; exact eq3
  have hc1 : c 1 = 0 := by
    have h0' : h3zornWeight 4 0 = 1 := rfl
    have h1' : h3zornWeight 4 1 = -1 := rfl
    have h2' : h3zornWeight 4 2 = 0 := rfl
    have h3' : h3zornWeight 4 3 = 0 := rfl
    have h4' : h3zornWeight 4 4 = 0 := rfl
    have h5' : h3zornWeight 4 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5', hc0] at eq4
    simp at eq4; exact eq4
  have hc3 : c 3 = 0 := by
    have h0' : h3zornWeight 5 0 = 1 := rfl
    have h1' : h3zornWeight 5 1 = 1 := rfl
    have h2' : h3zornWeight 5 2 = 0 := rfl
    have h3' : h3zornWeight 5 3 = -1 := rfl
    have h4' : h3zornWeight 5 4 = 0 := rfl
    have h5' : h3zornWeight 5 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5', hc0, hc1] at eq5
    simp at eq5; exact eq5
  have hc5 : c 5 = 0 := by
    have h0' : h3zornWeight 10 0 = 0 := rfl
    have h1' : h3zornWeight 10 1 = 0 := rfl
    have h2' : h3zornWeight 10 2 = 0 := rfl
    have h3' : h3zornWeight 10 3 = 0 := rfl
    have h4' : h3zornWeight 10 4 = 0 := rfl
    have h5' : h3zornWeight 10 5 = -1 := rfl
    rw [h0', h1', h2', h3', h4', h5'] at eq10
    simp at eq10; exact eq10
  have hc4 : c 4 = 0 := by
    have h0' : h3zornWeight 11 0 = 0 := rfl
    have h1' : h3zornWeight 11 1 = 0 := rfl
    have h2' : h3zornWeight 11 2 = 0 := rfl
    have h3' : h3zornWeight 11 3 = 0 := rfl
    have h4' : h3zornWeight 11 4 = -1 := rfl
    have h5' : h3zornWeight 11 5 = 1 := rfl
    rw [h0', h1', h2', h3', h4', h5', hc5] at eq11
    simp at eq11; exact eq11
  have hc2 : c 2 = 0 := by
    have h0' : h3zornWeight 1 0 = 0 := rfl
    have h1' : h3zornWeight 1 1 = 0 := rfl
    have h2' : h3zornWeight 1 2 = 1 := rfl
    have h3' : h3zornWeight 1 3 = 0 := rfl
    have h4' : h3zornWeight 1 4 = -1 := rfl
    have h5' : h3zornWeight 1 5 = 0 := rfl
    rw [h0', h1', h2', h3', h4', h5', hc4] at eq1
    simp at eq1; exact eq1
  intro i
  fin_cases i <;> assumption

theorem finrank_h3zornCartan : Module.finrank ℝ h3zornCartan = 6 := by
  have hli : LinearIndependent ℝ (fun i : Fin 6 =>
      (⟨e6SimpleH i, e6SimpleH_mem_h3zornCartan i⟩ : h3zornCartan)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i : Fin 6, c i • e6SimpleH i = 0 := congrArg Subtype.val hc
    exact Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent c hc'
  have hsp : Submodule.span ℝ (Set.range (fun i : Fin 6 =>
      (⟨e6SimpleH i, e6SimpleH_mem_h3zornCartan i⟩ : h3zornCartan))) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨x, hx⟩
    change x ∈ Submodule.span ℝ (Set.range e6SimpleH) at hx
    induction hx using Submodule.span_induction with
    | zero => exact Submodule.zero_mem _
    | add _ _ _ _ ih₁ ih₂ => exact Submodule.add_mem _ ih₁ ih₂
    | smul r _ _ ih => exact Submodule.smul_mem _ r ih
    | mem _ h =>
      rcases h with ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
  have hfin := finrank_span_eq_card hli
  rw [hsp, finrank_top] at hfin
  simpa using hfin

theorem e6RootVec_ne_zero (r : Fin 72) : e6RootVec r ≠ 0 := by
  have hnz : (List.finRange 72).all (fun r => !sparseZeroCheck (e6RootSparse r)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true'] at hnz
  intro h0
  have hm := congrArg (fun x : h3zornCubicStabilizer => h3zornToMatrix (x.1 : Module.End ℝ (H3Zorn ℝ))) h0
  rw [h3zornToMatrix_e6RootVec, ZeroMemClass.coe_zero, map_zero] at hm
  have hzm : sparseToMat (e6RootSparse r) = 0 := by
    ext a b
    have := congrFun (congrFun hm a) b
    simpa [Matrix.map_apply] using this
  have hzc : sparseZeroCheck (e6RootSparse r) = true := by
    simp only [sparseZeroCheck, List.all_eq_true, beq_iff_eq]
    intro p _
    exact congrFun (congrFun hzm p.1) p.2.1
  rw [hnz r] at hzc
  cases hzc

/-- Vandermonde/weight-killing lemma shared by `e6ChevalleyBasis` and `H3ZornE6Simplicity`:
for any submodule `S` of `h3zornCubicStabilizer` closed under `⁅e6SimpleH i, ·⁆`,
if `h + ∑ r ∈ A, b r • e6RootVec r ∈ S`, then `h ∈ S` and `∀ r ∈ A, b r • e6RootVec r ∈ S`. -/
theorem cartan_weight_kill_mem
    (S : Submodule ℝ h3zornCubicStabilizer)
    (hS : ∀ (i : Fin 6) (x : h3zornCubicStabilizer), x ∈ S → ⁅e6SimpleH i, x⁆ ∈ S)
    (A : Finset (Fin 72)) (h : h3zornCubicStabilizer) (hh : h ∈ h3zornCartan)
    (b : Fin 72 → ℝ) (hx : h + ∑ r ∈ A, b r • e6RootVec r ∈ S) :
    h ∈ S ∧ ∀ r ∈ A, b r • e6RootVec r ∈ S := by
  have hKillH : ∀ (u : h3zornCubicStabilizer), u ∈ h3zornCartan →
      ∀ (i : Fin 6), ⁅e6SimpleH i, u⁆ = 0 := by
    intro u hu i
    have hi : e6SimpleH i ∈ h3zornCartan := e6SimpleH_mem_h3zornCartan i
    have hc := (inferInstance : IsLieAbelian h3zornCartan).trivial ⟨e6SimpleH i, hi⟩ ⟨u, hu⟩
    exact congrArg Subtype.val hc
  suffices hMain : ∀ n : ℕ, ∀ (B : Finset (Fin 72)) (h0 : h3zornCubicStabilizer),
      h0 ∈ h3zornCartan → B.card = n →
      ∀ (c : Fin 72 → ℝ), h0 + ∑ r ∈ B, c r • e6RootVec r ∈ S →
        h0 ∈ S ∧ ∀ r ∈ B, c r • e6RootVec r ∈ S from
    hMain A.card A h hh rfl b hx
  intro n
  induction n with
  | zero =>
    intro B h0 hh0 hcard c hc
    rw [Finset.card_eq_zero.mp hcard] at hc ⊢
    simp only [Finset.sum_empty, add_zero] at hc
    exact ⟨hc, fun _ hr => absurd hr (Finset.notMem_empty _)⟩
  | succ n ih =>
    intro B h0 hh0 hcard c hc
    by_cases hn : n = 0
    · subst hn
      rw [Finset.card_eq_one] at hcard
      rcases hcard with ⟨r₀, rfl⟩
      simp only [Finset.sum_singleton] at hc
      obtain ⟨i₀, hi₀⟩ := rootEigenvalue_ne_zero r₀
      have hbr := hS i₀ _ hc
      rw [lie_add, hKillH h0 hh0 i₀, zero_add, lie_smul, e6RootVec_bracket_H, smul_smul] at hbr
      have hk₀ : (rootEigenvalue i₀ r₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hi₀
      have hroot : c r₀ • e6RootVec r₀ ∈ S := by
        have hs := S.smul_mem (rootEigenvalue i₀ r₀ : ℝ)⁻¹ hbr
        rw [smul_smul, mul_comm (c r₀), ← mul_assoc, inv_mul_cancel₀ hk₀, one_mul] at hs
        exact hs
      have hh0_mem : h0 ∈ S := by
        have hsub := S.sub_mem hc hroot
        simpa [add_sub_cancel_right] using hsub
      exact ⟨hh0_mem, fun r hr => by
        rw [Finset.mem_singleton] at hr
        subst hr
        exact hroot⟩
    · have hpos : 1 < B.card := by omega
      obtain ⟨r₀, hr₀, r₁, hr₁, hne⟩ := Finset.one_lt_card.mp hpos
      have hdiff : ∃ i₁ : Fin 6, rootEigenvalue i₁ r₀ ≠ rootEigenvalue i₁ r₁ := by
        by_contra hcon
        push Not at hcon
        exact hne (rootEigenvalue_eq_imp hcon)
      obtain ⟨i₁, hi₁⟩ := hdiff
      let lam0 : ℝ := rootEigenvalue i₁ r₀
      have hy : ⁅e6SimpleH i₁, h0 + ∑ r ∈ B, c r • e6RootVec r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • e6RootVec r) ∈ S :=
        S.sub_mem (hS i₁ _ hc) (S.smul_mem lam0 hc)
      let c' : Fin 72 → ℝ := fun r => c r * ((rootEigenvalue i₁ r : ℝ) - lam0)
      have hy_eq : ⁅e6SimpleH i₁, h0 + ∑ r ∈ B, c r • e6RootVec r⁆ -
          lam0 • (h0 + ∑ r ∈ B, c r • e6RootVec r) =
          (-lam0) • h0 + ∑ r ∈ B.erase r₀, c' r • e6RootVec r := by
        rw [lie_add, hKillH h0 hh0 i₁, zero_add, lie_sum, smul_add, Finset.smul_sum]
        have h1 : ∑ r ∈ B, ⁅e6SimpleH i₁, c r • e6RootVec r⁆ =
            ∑ r ∈ B, (c r * (rootEigenvalue i₁ r : ℝ)) • e6RootVec r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [lie_smul, e6RootVec_bracket_H, smul_smul]
        rw [h1]
        have h2 : ∑ r ∈ B, (c r * (rootEigenvalue i₁ r : ℝ)) • e6RootVec r -
            (lam0 • h0 + ∑ r ∈ B, lam0 • (c r • e6RootVec r)) =
            (-lam0) • h0 + ∑ r ∈ B, c' r • e6RootVec r := by
          rw [sub_eq_add_neg, neg_add, ← neg_smul lam0 h0,
            add_comm (-lam0 • h0) (-(∑ r ∈ B, lam0 • (c r • e6RootVec r))), ← add_assoc,
            add_comm (∑ r ∈ B, (c r * (rootEigenvalue i₁ r : ℝ)) • e6RootVec r +
              -(∑ r ∈ B, lam0 • (c r • e6RootVec r))) ((-lam0) • h0)]
          congr 1
          rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          dsimp [c']
          rw [smul_smul, ← sub_smul]
          congr 1; ring
        rw [h2, ← Finset.add_sum_erase B (fun r => c' r • e6RootVec r) hr₀]
        have hc'0 : c' r₀ = 0 := by simp [c', lam0]
        rw [hc'0, zero_smul, zero_add]
      rw [hy_eq] at hy
      have hcard0 : (B.erase r₀).card = n := by rw [Finset.card_erase_of_mem hr₀, hcard]; simp
      have ih0 := ih (B.erase r₀) ((-lam0) • h0) (h3zornCartan.smul_mem (-lam0) hh0) hcard0 c' hy
      have hr₁_erase : r₁ ∈ B.erase r₀ := Finset.mem_erase.mpr ⟨hne.symm, hr₁⟩
      have hc'r₁ := ih0.2 r₁ hr₁_erase
      have hlam_ne : ((rootEigenvalue i₁ r₁ : ℝ) - lam0) ≠ 0 := by
        intro heq
        apply hi₁
        exact (Int.cast_injective (sub_eq_zero.mp heq)).symm
      have hr₁_mem : c r₁ • e6RootVec r₁ ∈ S := by
        have hs := S.smul_mem ((rootEigenvalue i₁ r₁ : ℝ) - lam0)⁻¹ hc'r₁
        dsimp [c'] at hs
        rw [smul_smul, mul_comm (c r₁), ← mul_assoc, inv_mul_cancel₀ hlam_ne, one_mul] at hs
        exact hs
      have hx_erase : h0 + ∑ r ∈ B.erase r₁, c r • e6RootVec r ∈ S := by
        have hsub := S.sub_mem hc hr₁_mem
        have hs_eq : (h0 + ∑ r ∈ B, c r • e6RootVec r) - c r₁ • e6RootVec r₁ =
            h0 + ∑ r ∈ B.erase r₁, c r • e6RootVec r := by
          rw [← Finset.add_sum_erase B _ hr₁]
          abel
        rwa [hs_eq] at hsub
      have hcard1 : (B.erase r₁).card = n := by rw [Finset.card_erase_of_mem hr₁, hcard]; simp
      have ih1 := ih (B.erase r₁) h0 hh0 hcard1 c hx_erase
      refine ⟨ih1.1, fun r hr => ?_⟩
      by_cases heq : r = r₁
      · subst heq; exact hr₁_mem
      · exact ih1.2 r (Finset.mem_erase.mpr ⟨heq, hr⟩)

private theorem h3zornStab_coe_add (x y : h3zornCubicStabilizer) : (x + y).1 = x.1 + y.1 := rfl

/-- The 78-element Chevalley basis `(e6SimpleH ⊕ e6RootVec)` of `h3zornCubicStabilizer`. -/
theorem e6Chevalley_linearIndependent :
    LinearIndependent ℝ (Sum.elim e6SimpleH e6RootVec) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : (∑ i : Fin 6, g (Sum.inl i) • e6SimpleH i) +
      (∑ r : Fin 72, g (Sum.inr r) • e6RootVec r) = 0 := by
    apply Subtype.ext
    have hg' := congrArg (Subtype.val : h3zornCubicStabilizer → Module.End ℝ (H3Zorn ℝ)) hg
    simp only [ZeroMemClass.coe_zero, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
      h3zornStab_coe_add] at hg' ⊢
    rw [Fintype.sum_sum_type] at hg'
    simp only [Sum.elim_inl, Sum.elim_inr] at hg'
    exact hg'
  have hkill := cartan_weight_kill_mem ⊥ (fun i x hx => by
    rw [Submodule.mem_bot] at hx
    subst hx
    simp) Finset.univ (∑ i : Fin 6, g (Sum.inl i) • e6SimpleH i)
    (Submodule.sum_mem _ fun i _ => h3zornCartan.smul_mem (g (Sum.inl i)) (e6SimpleH_mem_h3zornCartan i))
    (fun r => g (Sum.inr r))
    (by rw [hsum]; exact Submodule.zero_mem _)
  have ha0 : ∀ i : Fin 6, g (Sum.inl i) = 0 := by
    have h0 : ∑ j : Fin 6, g (Sum.inl j) • e6SimpleH j = 0 := (Submodule.mem_bot ℝ).mp hkill.1
    exact Fintype.linearIndependent_iff.mp e6SimpleH_linearIndependent (fun i => g (Sum.inl i)) h0
  have hb0 : ∀ r : Fin 72, g (Sum.inr r) = 0 := by
    intro r
    have h0 : g (Sum.inr r) • e6RootVec r = 0 := (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
    exact (smul_eq_zero.mp h0).resolve_right (e6RootVec_ne_zero r)
  rintro (i | r)
  · exact ha0 i
  · exact hb0 r

def e6ChevalleyBasis : Module.Basis (Fin 6 ⊕ Fin 72) ℝ h3zornCubicStabilizer :=
  basisOfLinearIndependentOfCardEqFinrank e6Chevalley_linearIndependent
    (by rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, finrank_h3zornCubicStabilizer])

@[simp] theorem e6ChevalleyBasis_inl (i : Fin 6) :
    e6ChevalleyBasis (Sum.inl i) = e6SimpleH i := by
  simp [e6ChevalleyBasis]

@[simp] theorem e6ChevalleyBasis_inr (r : Fin 72) :
    e6ChevalleyBasis (Sum.inr r) = e6RootVec r := by
  simp [e6ChevalleyBasis]

/-- `h3zornCartan` is a genuine 6D split Cartan subalgebra of `h3zornCubicStabilizer`. -/
instance h3zornCartan_isCartanSubalgebra : h3zornCartan.IsCartanSubalgebra where
  nilpotent := inferInstance
  self_normalizing := by
    apply le_antisymm _ h3zornCartan.le_normalizer
    intro x hx
    have hrep := e6ChevalleyBasis.sum_repr x
    rw [Fintype.sum_sum_type] at hrep
    simp only [e6ChevalleyBasis_inl, e6ChevalleyBasis_inr] at hrep
    have hhpart : (∑ i : Fin 6, (e6ChevalleyBasis.repr x) (Sum.inl i) • e6SimpleH i) ∈ h3zornCartan :=
      Submodule.sum_mem _ fun i _ => h3zornCartan.smul_mem _ (e6SimpleH_mem_h3zornCartan i)
    have hb0 : ∀ r : Fin 72, (e6ChevalleyBasis.repr x) (Sum.inr r) = 0 := by
      intro r
      obtain ⟨i, hi⟩ := rootEigenvalue_ne_zero r
      have hnorm : ⁅e6SimpleH i, x⁆ ∈ h3zornCartan := by
        have hxmem := (LieSubalgebra.mem_normalizer_iff h3zornCartan x).mp hx (e6SimpleH i)
          (e6SimpleH_mem_h3zornCartan i)
        have hneg := h3zornCartan.neg_mem hxmem
        rw [← lie_skew, neg_neg] at hneg
        exact hneg
      have hKillH : ⁅e6SimpleH i, ∑ j : Fin 6, (e6ChevalleyBasis.repr x) (Sum.inl j) • e6SimpleH j⁆ = 0 := by
        have hc := (inferInstance : IsLieAbelian h3zornCartan).trivial
          ⟨e6SimpleH i, e6SimpleH_mem_h3zornCartan i⟩ ⟨_, hhpart⟩
        exact congrArg Subtype.val hc
      have hbr : ⁅e6SimpleH i, x⁆ =
          ∑ q : Fin 72, ((e6ChevalleyBasis.repr x) (Sum.inr q) * (rootEigenvalue i q : ℝ)) • e6RootVec q := by
        conv_lhs => rw [← hrep]
        rw [lie_add, hKillH, zero_add, lie_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lie_smul, e6RootVec_bracket_H, smul_smul]
      have hmem : (-⁅e6SimpleH i, x⁆) +
          ∑ q : Fin 72, ((e6ChevalleyBasis.repr x) (Sum.inr q) * (rootEigenvalue i q : ℝ)) • e6RootVec q ∈
            (⊥ : Submodule ℝ h3zornCubicStabilizer) := by
        rw [← hbr, neg_add_cancel]
        exact Submodule.zero_mem _
      have hkill := cartan_weight_kill_mem ⊥ (fun k y hy => by
        rw [Submodule.mem_bot] at hy; subst hy; simp)
        Finset.univ (-⁅e6SimpleH i, x⁆) (h3zornCartan.neg_mem hnorm)
        (fun q => (e6ChevalleyBasis.repr x) (Sum.inr q) * (rootEigenvalue i q : ℝ)) hmem
      have hr0 : ((e6ChevalleyBasis.repr x) (Sum.inr r) * (rootEigenvalue i r : ℝ)) • e6RootVec r = 0 :=
        (Submodule.mem_bot ℝ).mp (hkill.2 r (Finset.mem_univ r))
      have hmul0 := (smul_eq_zero.mp hr0).resolve_right (e6RootVec_ne_zero r)
      exact (mul_eq_zero.mp hmul0).resolve_right (Int.cast_ne_zero.mpr hi)
    have hs0 : (∑ r : Fin 72, (e6ChevalleyBasis.repr x) (Sum.inr r) • e6RootVec r) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [hb0 r, zero_smul]
    rw [← hrep, hs0, add_zero]
    exact hhpart

/-- Explicit non-commutativity witnesses on the 27D integer and real operator matrix algebras. -/
private theorem h3zornToMatrix_e6_noncomm :
    h3zornToMatrix (e6SimpleH 0).1 * h3zornToMatrix (e6SimpleE 0).1 ≠
      h3zornToMatrix (e6SimpleE 0).1 * h3zornToMatrix (e6SimpleH 0).1 := by
  intro heq
  have hsub : h3zornToMatrix (⁅e6SimpleH 0, e6SimpleE 0⁆ : Module.End ℝ (H3Zorn ℝ)) = 0 := by
    rw [h3zornToMatrix_lie, heq, sub_self]
  have h0 : (⁅e6SimpleH 0, e6SimpleE 0⁆ : h3zornCubicStabilizer) = 0 :=
    Subtype.ext (h3zornToMatrix.injective (by simpa using hsub))
  rw [e6Simple_bracket_HE] at h0
  have hc : Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) = 2 := by decide
  change ((Tag.cartan .E6 (0 : Fin 6) (0 : Fin 6) : ℤ) : ℝ) • e6RootVec (eSimpleIdx 0) = 0 at h0
  rw [hc] at h0
  norm_num at h0
  exact e6RootVec_ne_zero (eSimpleIdx 0) h0

theorem matrix27_real_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℝ, A * B ≠ B * A :=
  ⟨h3zornToMatrix (e6SimpleH 0).1, h3zornToMatrix (e6SimpleE 0).1, h3zornToMatrix_e6_noncomm⟩

theorem matrix27_int_noncomm_witness :
    ∃ A B : Matrix (Fin 27) (Fin 27) ℤ, A * B ≠ B * A := by
  refine ⟨sparseToMat (e6SimpleHSparse 0), sparseToMat (e6SimpleESparse 0), ?_⟩
  intro heq
  apply h3zornToMatrix_e6_noncomm
  rw [h3zornToMatrix_e6SimpleH, h3zornToMatrix_e6SimpleE]
  ext r c
  have hrc := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun heq r) c)
  simpa [Matrix.mul_apply] using hrc

end RootSystemAndChevalley

end InfoGeometry.Algebra
