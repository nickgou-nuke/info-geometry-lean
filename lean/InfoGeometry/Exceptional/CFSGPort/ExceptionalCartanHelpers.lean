/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local ports of the neighboring-simple-root facts used by the external
exceptional Chevalley perfectness proofs.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCheck

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- Exponentiation sends finite sums in the exponent to finite products. -/
theorem zpow_finset_sum_local {G : Type*} [CommGroup G] {ι : Type*}
    (g : G) (s : Finset ι) (f : ι → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/-- An integral right inverse to the exponent matrix detects a tuple of
units from all of its Cartan-weight characters. This is the algebraic core
of the external adjoint-torus independence proof. -/
theorem eq_one_of_prod_zpow_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Type*} [CommGroup G] (A B : Matrix ι ι ℤ)
    (hAB : A * B = 1) {u : ι → G}
    (hu : ∀ m, ∏ j, u j ^ A j m = 1) (l : ι) : u l = 1 := by
  have key : ∏ m, (∏ j, u j ^ A j m) ^ B m l = u l := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [← zpow_finset_sum_local]
    have h : ∀ j, ∑ m, A j m * B m l = if j = l then 1 else 0 := fun j => by
      have hentry := congrFun (congrFun hAB j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at hentry
      exact hentry
    simp only [h]
    rw [Finset.prod_eq_single l]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hnot
      exact (hnot (Finset.mem_univ l)).elim
  rw [← key]
  simp [hu]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix indecomposability as used by the external Tits simplicity
criterion: the indices cannot split into two nonempty parts with a zero
off-diagonal block. -/
def IsIndecomposable (A : Matrix ι ι ℤ) : Prop :=
  ¬ ∃ I J : Finset ι, I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧
    I ∪ J = Finset.univ ∧ ∀ i ∈ I, ∀ j ∈ J, A i j = 0

theorem isIndecomposable_iff {A : Matrix ι ι ℤ} :
    IsIndecomposable A ↔
      ∀ S : Finset ι, (∀ i ∈ S, ∀ j ∉ S, A i j = 0) →
        S = ∅ ∨ S = Finset.univ := by
  constructor
  · intro h S hS
    by_contra hne
    rw [not_or] at hne
    refine h ⟨S, Sᶜ, Finset.nonempty_iff_ne_empty.2 hne.1, ?_,
      disjoint_compl_right, Finset.union_compl S, fun i hi j hj =>
        hS i hi j (Finset.mem_compl.1 hj)⟩
    rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
    exact hne.2
  · rintro h ⟨I, J, hI, hJ, hIJ, hU, h0⟩
    have hJI : ∀ j, j ∈ J ↔ j ∉ I := fun j =>
      ⟨fun hj hi => Finset.disjoint_left.1 hIJ hi hj, fun hi => by
        have := Finset.mem_univ j
        rw [← hU, Finset.mem_union] at this
        exact this.resolve_left hi⟩
    rcases h I (fun i hi j hj => h0 i hi j ((hJI j).2 hj)) with rfl | rfl
    · exact Finset.not_nonempty_empty hI
    · obtain ⟨j, hj⟩ := hJ
      exact (hJI j).1 hj (Finset.mem_univ j)

instance (A : Matrix ι ι ℤ) : Decidable (IsIndecomposable A) :=
  have : DecidablePred fun S : Finset ι =>
      (∀ i ∈ S, ∀ j ∉ S, A i j = 0) → S = ∅ ∨ S = Finset.univ := fun S =>
    have : DecidablePred fun i => ∀ j ∉ S, A i j = 0 := fun _ => inferInstance
    inferInstance
  decidable_of_iff _ isIndecomposable_iff.symm

/-- Every simple root of F₄ has a simply-laced neighboring simple root. -/
theorem exists_symmetric_simple_neighbor_F4 (i : Fin (Tag.rank .F4)) :
    ∃ l, Tag.cartan .F4 i l = -1 ∧ Tag.cartan .F4 l i = -1 := by
  fin_cases i <;> decide

/-- Every simple root of E₈ has a simply-laced neighboring simple root. -/
theorem exists_symmetric_simple_neighbor_E8 (i : Fin (Tag.rank .E8)) :
    ∃ l, Tag.cartan .E8 i l = -1 ∧ Tag.cartan .E8 l i = -1 := by
  fin_cases i <;> decide

/-- Every simple root of E₆ has a simply-laced neighboring simple root. -/
theorem exists_symmetric_simple_neighbor_E6 (i : Fin (Tag.rank .E6)) :
    ∃ l, Tag.cartan .E6 i l = -1 ∧ Tag.cartan .E6 l i = -1 := by
  fin_cases i <;> decide

/-- Every simple root of E₇ has a simply-laced neighboring simple root. -/
theorem exists_symmetric_simple_neighbor_E7 (i : Fin (Tag.rank .E7)) :
    ∃ l, Tag.cartan .E7 i l = -1 ∧ Tag.cartan .E7 l i = -1 := by
  fin_cases i <;> decide

/-- Every simple root of D₄ has a simply-laced neighboring simple root. -/
theorem exists_symmetric_simple_neighbor_D4 (i : Fin (Tag.rank .D4)) :
    ∃ l, Tag.cartan .D4 i l = -1 ∧ Tag.cartan .D4 l i = -1 := by
  fin_cases i <;> decide

/-- The inverse of the F₄ Cartan matrix, used in the external Steinberg
normalizer argument. -/
def cartanInvF4 : Matrix (Fin (Tag.rank .F4)) (Fin (Tag.rank .F4)) ℤ :=
  !![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2]

theorem cartan_mul_cartanInvF4 : Tag.cartan .F4 * cartanInvF4 = 1 := by
  decide +kernel

/-- The inverse of the E₈ Cartan matrix, used in the external Steinberg
normalizer argument. -/
def cartanInvE8 : Matrix (Fin (Tag.rank .E8)) (Fin (Tag.rank .E8)) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2;
    5, 8, 10, 15, 12, 9, 6, 3;
    7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6;
    8, 12, 16, 24, 20, 15, 10, 5;
    6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3;
    2, 3, 4, 6, 5, 4, 3, 2]

theorem cartan_mul_cartanInvE8 : Tag.cartan .E8 * cartanInvE8 = 1 := by
  decide +kernel

/-- The F₄ and E₈ Cartan matrices are indecomposable, as required by the
external Tits quasisimplicity criterion. -/
theorem isIndecomposable_cartan_F4 : IsIndecomposable (Tag.cartan .F4) := by
  decide +kernel

theorem isIndecomposable_cartan_E8 : IsIndecomposable (Tag.cartan .E8) := by
  decide +kernel

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
