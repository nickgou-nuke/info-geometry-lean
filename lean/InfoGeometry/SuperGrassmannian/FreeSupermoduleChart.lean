/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartBaseChange
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Native free supermodule gradings and graph coordinates

A basis vector of parity `d i` makes its coefficient in a degree-`p` vector
lie in `𝓐 (p + d i)`. We construct the native direct-sum decomposition, then
prove that homogeneous matrix coefficients define even module maps. These
results apply to arbitrary internally graded associative coefficient algebras;
supercommutativity is not needed for this chart calculation.
-/

namespace InfoGeometry.SuperGrassmannian.FreeSupermoduleChart

open DirectSum GradedGraphChart GraphChartBaseChange

variable {k A I J : Type*} [CommRing k] [Ring A] [Algebra k A]
  (𝓐 : ZMod 2 → Submodule k A) [GradedAlgebra 𝓐]

/-- The native degree-`p` submodule of a free module with specified basis parities. -/
def freeGrade (d : I → ZMod 2) (p : ZMod 2) : Submodule k (I → A) :=
  Submodule.pi Set.univ (fun i => 𝓐 (p + d i))

omit [GradedAlgebra 𝓐] in
@[simp] theorem mem_freeGrade (d : I → ZMod 2) (p : ZMod 2) (x : I → A) :
    x ∈ freeGrade 𝓐 d p ↔ ∀ i, x i ∈ 𝓐 (p + d i) := by
  simp [freeGrade, Submodule.mem_pi]

/-- Decompose every coefficient with the appropriate parity shift. -/
noncomputable def freeDecompose (d : I → ZMod 2) (x : I → A) :
    ⨁ p, freeGrade 𝓐 d p :=
  (DirectSum.linearEquivFunOnFintype k (ZMod 2) (fun p => freeGrade 𝓐 d p)).symm
    (fun p => ⟨fun i => (decompose 𝓐 (x i) (p + d i) : A),
      (mem_freeGrade 𝓐 d p _).mpr (fun i => (decompose 𝓐 (x i) (p + d i)).property)⟩)

@[simp] theorem freeDecompose_apply (d : I → ZMod 2) (x : I → A) (p : ZMod 2) (i : I) :
    (freeDecompose 𝓐 d x p : I → A) i = (decompose 𝓐 (x i) (p + d i) : A) := rfl

/-- Genuine native decomposition, not an assumption attached to a carrier. -/
noncomputable instance freeDecomposition (d : I → ZMod 2) :
    Decomposition (freeGrade 𝓐 d) where
  decompose' := freeDecompose 𝓐 d
  left_inv x := by
    rw [← DirectSum.sum_univ_of (freeDecompose 𝓐 d x), map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    funext i
    simp only [Finset.sum_apply, freeDecompose_apply]
    have hs : (∑ p : ZMod 2, (decompose 𝓐 (x i) p : A)) = x i := by
      have h := (decompose 𝓐).symm_apply_apply (x i)
      rw [← DirectSum.sum_univ_of (decompose 𝓐 (x i))] at h
      simpa only [decompose_symm_sum, decompose_symm_of] using h
    exact (Fintype.sum_equiv (Equiv.addRight (d i)) _ _ (fun p => rfl)).trans hs
  right_inv x := by
    apply DFinsupp.ext
    intro p
    apply Subtype.ext
    funext i
    rw [freeDecompose_apply]
    have hr : DirectSum.coeAddMonoidHom (freeGrade 𝓐 d) x =
        ∑ q, (x q : I → A) := by
      conv_lhs => rw [← DirectSum.sum_univ_of x, map_sum]
      simp only [DirectSum.coeAddMonoidHom_of]
    rw [hr]
    simp only [Finset.sum_apply, decompose_sum]
    have hc (q : ZMod 2) :
        (decompose 𝓐 ((x q : I → A) i) (p + d i) : A) =
          if q = p then (x p : I → A) i else 0 := by
      have hx := (mem_freeGrade 𝓐 d q _).mp (x q).property i
      by_cases h : q = p
      · subst q
        simp [decompose_of_mem_same 𝓐 hx]
      · have hn : q + d i ≠ p + d i := by simpa using h
        rw [decompose_of_mem_ne 𝓐 hx hn]
        simp [h]
    simp [DirectSum, DFinsupp.finsetSum_apply, hc]

/-- Homogeneous scalar multiplication has the native graded-module degree. -/
theorem smul_mem_freeGrade (d : I → ZMod 2) {p q : ZMod 2} {a : A} {x : I → A}
    (ha : a ∈ 𝓐 p) (hx : x ∈ freeGrade 𝓐 d q) :
    a • x ∈ freeGrade 𝓐 d (p + q) := by
  rw [mem_freeGrade] at hx ⊢
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul, add_assoc] using
    SetLike.mul_mem_graded ha (hx i)

instance freeGradedSMul (d : I → ZMod 2) :
    SetLike.GradedSMul 𝓐 (freeGrade 𝓐 d) where
  smul_mem := fun {_ _ _ _} ha hx => smul_mem_freeGrade 𝓐 d ha hx

/-- Correct parity of each coefficient is sufficient for an even linear map. -/
theorem coordinate_preservesDegree [Fintype I] (d : I → ZMod 2) (e : J → ZMod 2)
    (T : I → J → A) (hT : ∀ i j, T i j ∈ 𝓐 (d i + e j)) :
    PreservesDegree (freeGrade 𝓐 d) (freeGrade 𝓐 e) (coordinateLinearMap T) := by
  intro p x hx
  rw [mem_freeGrade] at hx ⊢
  intro j
  apply Submodule.sum_mem
  intro i _
  have h := SetLike.mul_mem_graded (hx i) (hT i j)
  have he : (p + d i) + (d i + e j) = p + e j := by
    rw [add_assoc, ← add_assoc (d i), CharTwo.add_self_eq_zero, zero_add]
  simpa only [he] using h

/-- The parity condition is necessary too, by evaluation on homogeneous basis vectors. -/
theorem coordinate_preservesDegree_iff [Fintype I] [DecidableEq I]
    (d : I → ZMod 2) (e : J → ZMod 2) (T : I → J → A) :
    PreservesDegree (freeGrade 𝓐 d) (freeGrade 𝓐 e) (coordinateLinearMap T) ↔
      ∀ i j, T i j ∈ 𝓐 (d i + e j) := by
  refine ⟨?_, coordinate_preservesDegree 𝓐 d e T⟩
  intro h i j
  have hi : Pi.single i (1 : A) ∈ freeGrade 𝓐 d (d i) := by
    rw [mem_freeGrade]
    intro l
    by_cases hl : l = i
    · subst l
      simpa [CharTwo.add_self_eq_zero] using SetLike.one_mem_graded 𝓐
    · simp [hl]
  have hh := (mem_freeGrade 𝓐 e (d i) _).mp (h (d i) _ hi) j
  simpa [Pi.single_apply] using hh

omit [GradedAlgebra 𝓐] in
/-- The coordinate formula is precisely Mathlib's native free-module equivalence. -/
theorem coordinateLinearMap_eq_piRing [Fintype I] [DecidableEq I] (T : I → J → A) :
    coordinateLinearMap T = (LinearEquiv.piRing A (J → A) I ℤ).symm T := by
  ext x j
  simp [LinearEquiv.piRing_symm_apply, Finset.sum_apply, smul_eq_mul]

/-- The full chart equivalence: homogeneous coefficient arrays classify every
transverse homogeneous submodule, not only the exhibited examples. -/
noncomputable def coefficientChartEquiv [Fintype I] [DecidableEq I]
    (d : I → ZMod 2) (e : J → ZMod 2) :
    {T : I → J → A // ∀ i j, T i j ∈ 𝓐 (d i + e j)} ≃
      Chart (A := A) (freeGrade 𝓐 d) (freeGrade 𝓐 e) :=
  ((LinearEquiv.piRing A (J → A) I ℤ).symm.toEquiv.subtypeEquiv (fun T => by
    change _ ↔ PreservesDegree (freeGrade 𝓐 d) (freeGrade 𝓐 e)
      ((LinearEquiv.piRing A (J → A) I ℤ).symm T)
    rw [← coordinateLinearMap_eq_piRing]
    exact (coordinate_preservesDegree_iff 𝓐 d e T).symm)).trans (graphChartEquiv _ _)

@[simp] theorem coefficientChartEquiv_submodule [Fintype I] [DecidableEq I]
    (d : I → ZMod 2) (e : J → ZMod 2)
    (T : {T : I → J → A // ∀ i j, T i j ∈ 𝓐 (d i + e j)}) :
    (coefficientChartEquiv 𝓐 d e T).val = (coordinateLinearMap T.val).graph := by
  change ((LinearEquiv.piRing A (J → A) I ℤ).symm T.val).graph = _
  rw [← coordinateLinearMap_eq_piRing]

/-- Naturality on actual chart submodules along any degree-preserving algebra map. -/
theorem coefficientChartEquiv_natural [Fintype I] [DecidableEq I]
    {B : Type*} [Ring B] [Algebra k B]
    (𝓑 : ZMod 2 → Submodule k B) [GradedAlgebra 𝓑]
    (φ : A →ₐ[k] B) (hφ : ∀ p, ∀ a ∈ 𝓐 p, φ a ∈ 𝓑 p)
    (d : I → ZMod 2) (e : J → ZMod 2)
    (T : {T : I → J → A // ∀ i j, T i j ∈ 𝓐 (d i + e j)}) :
    extend φ.toRingHom (coefficientChartEquiv 𝓐 d e T).val =
      (coefficientChartEquiv 𝓑 d e
        ⟨fun i j => φ (T.val i j), fun i j => hφ _ _ (T.property i j)⟩).val := by
  simp only [coefficientChartEquiv_submodule]
  exact extend_graph φ.toRingHom T.val

end InfoGeometry.SuperGrassmannian.FreeSupermoduleChart
