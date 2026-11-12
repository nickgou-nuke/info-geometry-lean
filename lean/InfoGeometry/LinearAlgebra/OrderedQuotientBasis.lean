/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.SDiff
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Ordered selection of a basis modulo linear relations

`select` processes an explicit list from left to right. It retains a label exactly when its
candidate is outside the span of the labels already retained. The recursion fixes the priority
order, including when labels repeat. Its span tests use classical decidability, so the definition
is noncomputable; no effective linear-dependence oracle is supplied here.

The ambient module need not be finite dimensional. `quotientBasis` is a basis of the image of the
finite candidate span under the native quotient map. A basis of the entire quotient is constructed
only with the additional hypothesis that the relation and candidate spans generate the ambient
module.

`select_relations_first` identifies ordinary selection initialized with relation generators with
selection in the quotient. The relation generators need not themselves be independent. This
statement concerns a module quotient and makes no claim that multiplication descends to it.
-/

namespace InfoGeometry.LinearAlgebra.OrderedQuotientBasis

open scoped Classical

variable (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [DecidableEq ι]
variable (v : ι → V)

/-- The native linear span of the candidates carrying the specified labels. -/
def candidateSpan (s : Finset ι) : Submodule K V :=
  Submodule.span K (v '' (s : Set ι))

omit [DecidableEq ι] in
@[simp]
theorem candidateSpan_empty : candidateSpan K v ∅ = ⊥ := by
  simp [candidateSpan]

theorem candidateSpan_union (s t : Finset ι) :
    candidateSpan K v (s ∪ t) = candidateSpan K v s ⊔ candidateSpan K v t := by
  simp only [candidateSpan, Finset.coe_union, Set.image_union, Submodule.span_union]

omit [DecidableEq ι] in
theorem candidateSpan_mono {s t : Finset ι} (h : s ⊆ t) :
    candidateSpan K v s ≤ candidateSpan K v t := by
  apply Submodule.span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, h hi, rfl⟩

omit [DecidableEq ι] in
theorem mem_candidateSpan {s : Finset ι} {i : ι} (hi : i ∈ s) :
    v i ∈ candidateSpan K v s :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem candidateSpan_insert_of_mem (s : Finset ι) (i : ι)
    (hi : v i ∈ candidateSpan K v s) :
    candidateSpan K v (insert i s) = candidateSpan K v s := by
  unfold candidateSpan
  rw [Finset.coe_insert, Set.image_insert_eq]
  exact Submodule.span_insert_eq_span hi

/-- Scan in list order, retaining a candidate exactly when it enlarges the current span. -/
noncomputable def select : Finset ι → List ι → Finset ι
  | s, [] => s
  | s, i :: order =>
      if v i ∈ candidateSpan K v s then
        select s order
      else
        select (insert i s) order

@[simp]
theorem select_nil (s : Finset ι) : select K v s [] = s := rfl

theorem select_cons (s : Finset ι) (i : ι) (order : List ι) :
    select K v s (i :: order) =
      if v i ∈ candidateSpan K v s then select K v s order
      else select K v (insert i s) order := rfl

/-- The selector never removes an initially retained label. -/
theorem initial_subset_select (s : Finset ι) (order : List ι) :
    s ⊆ select K v s order := by
  induction order generalizing s with
  | nil => exact fun _ hi => hi
  | cons i order ih =>
      by_cases hi : v i ∈ candidateSpan K v s
      · rw [select_cons, ite_eq_left hi]
        exact ih s
      · rw [select_cons, ite_eq_right hi]
        exact (Finset.subset_insert i s).trans (ih (insert i s))

/-- Every retained label was present initially or occurs in the processing list. -/
theorem select_subset (s : Finset ι) (order : List ι) :
    select K v s order ⊆ s ∪ order.toFinset := by
  induction order generalizing s with
  | nil =>
      simpa only [select_nil, List.toFinset_nil, Finset.union_empty] using
        (show s ⊆ s from fun _ hi => hi)
  | cons i order ih =>
      by_cases hi : v i ∈ candidateSpan K v s
      · rw [select_cons, ite_eq_left hi, List.toFinset_cons]
        exact (ih s).trans
          (Finset.union_subset_union_right (Finset.subset_insert i order.toFinset))
      · rw [select_cons, ite_eq_right hi]
        simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using
          ih (insert i s)

/-- Native insertion outside the current span proves independence at every step. -/
theorem linearIndepOn_select (s : Finset ι) (order : List ι)
    (hs : LinearIndepOn K v (s : Set ι)) :
    LinearIndepOn K v (select K v s order : Set ι) := by
  induction order generalizing s with
  | nil => exact hs
  | cons i order ih =>
      by_cases hi : v i ∈ candidateSpan K v s
      · rw [select_cons, ite_eq_left hi]
        exact ih s hs
      · rw [select_cons, ite_eq_right hi]
        apply ih (insert i s)
        simpa only [Finset.coe_insert] using hs.insert hi

/-- Discarding a dependent candidate preserves the span of all candidates processed so far. -/
theorem candidateSpan_select (s : Finset ι) (order : List ι) :
    candidateSpan K v (select K v s order) = candidateSpan K v (s ∪ order.toFinset) := by
  induction order generalizing s with
  | nil => simp only [select_nil, List.toFinset_nil, Finset.union_empty]
  | cons i order ih =>
      by_cases hi : v i ∈ candidateSpan K v s
      · rw [select_cons, ite_eq_left hi, ih s, List.toFinset_cons, Finset.union_insert]
        exact (candidateSpan_insert_of_mem K v (s ∪ order.toFinset) i
          ((candidateSpan_mono K v Finset.subset_union_left) hi)).symm
      · rw [select_cons, ite_eq_right hi, ih (insert i s), List.toFinset_cons,
          Finset.insert_union, Finset.union_insert]

/-- Processing consecutive lists is the same as resuming from the first result. -/
theorem select_append (s : Finset ι) (front suffix : List ι) :
    select K v s (front ++ suffix) = select K v (select K v s front) suffix := by
  induction front generalizing s with
  | nil => rfl
  | cons i front ih =>
      by_cases hi : v i ∈ candidateSpan K v s
      · simp only [List.cons_append, select_cons, ite_eq_left hi]
        exact ih s
      · simp only [List.cons_append, select_cons, ite_eq_right hi]
        exact ih (insert i s)

/-- Extending the processing list preserves every previously retained label. -/
theorem select_prefix_subset (s : Finset ι) (front suffix : List ι) :
    select K v s front ⊆ select K v s (front ++ suffix) := by
  rw [select_append]
  exact initial_subset_select K v (select K v s front) suffix

/-- A label already dependent on the current span can never enter at a later occurrence. -/
theorem notMem_select_of_mem_span (s : Finset ι) (order : List ι) {i : ι}
    (hi : i ∉ s) (hspan : v i ∈ candidateSpan K v s) :
    i ∉ select K v s order := by
  induction order generalizing s with
  | nil => exact hi
  | cons j order ih =>
      by_cases hj : v j ∈ candidateSpan K v s
      · rw [select_cons, ite_eq_left hj]
        exact ih s hi hspan
      · rw [select_cons, ite_eq_right hj]
        have hij : i ≠ j := fun heq => hj (heq ▸ hspan)
        have hi' : i ∉ insert j s := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hij, hi⟩
        exact ih (insert j s) hi'
          ((candidateSpan_mono K v (Finset.subset_insert j s)) hspan)

/-- Both retention and rejection decisions on an already processed prefix are stable.

Repeated labels in the suffix cannot change a decision made on the prefix. -/
theorem select_prefix_inter (s : Finset ι) (front suffix : List ι) :
    select K v s (front ++ suffix) ∩ (s ∪ front.toFinset) = select K v s front := by
  ext i
  constructor
  · intro hi
    obtain ⟨hfinal, hseen⟩ := Finset.mem_inter.mp hi
    by_contra hnot
    have hspan : v i ∈ candidateSpan K v (select K v s front) := by
      rw [candidateSpan_select]
      exact mem_candidateSpan K v hseen
    apply notMem_select_of_mem_span K v (select K v s front) suffix hnot hspan
    simpa only [select_append] using hfinal
  · intro hi
    exact Finset.mem_inter.mpr
      ⟨select_prefix_subset K v s front suffix hi, select_subset K v s front hi⟩

/-- The retained candidates themselves form a native basis of their span.

The index set is the output of `select`; `Basis.span` supplies coordinates for this proved
independent family, without choosing a different family of basis vectors. -/
noncomputable def selectedBasis (s : Finset ι) (order : List ι)
    (hs : LinearIndepOn K v (s : Set ι)) :
    Module.Basis {i // i ∈ select K v s order} K
      (candidateSpan K v (select K v s order)) := by
  let hli : LinearIndependent K
      (fun i : {i // i ∈ select K v s order} => v i.1) :=
    linearIndepOn_select K v s order hs
  exact (Module.Basis.span hli).map
    (LinearEquiv.ofEq _ _ (by
      unfold candidateSpan
      rw [Set.image_eq_range]
      rfl))

@[simp]
theorem selectedBasis_apply (s : Finset ι) (order : List ι)
    (hs : LinearIndepOn K v (s : Set ι)) (i : {i // i ∈ select K v s order}) :
    (selectedBasis K v s order hs i : V) = v i.1 := by
  simp only [selectedBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact Module.Basis.coe_span_apply _ i

section Quotient

variable (R : Submodule K V)

omit [DecidableEq ι] in
/-- The quotient candidates span precisely the image of the original candidate span. -/
theorem candidateSpan_quotient (s : Finset ι) :
    candidateSpan K (R.mkQ ∘ v) s = (candidateSpan K v s).map R.mkQ := by
  simp only [candidateSpan, Submodule.map_span, Set.image_image, Function.comp_def]

omit [DecidableEq ι] in
/-- Dependence in the quotient is dependence modulo the relation submodule. -/
theorem quotient_mem_candidateSpan_iff (s : Finset ι) (i : ι) :
    R.mkQ (v i) ∈ candidateSpan K (R.mkQ ∘ v) s ↔
      v i ∈ R ⊔ candidateSpan K v s := by
  rw [candidateSpan_quotient]
  change v i ∈ Submodule.comap R.mkQ ((candidateSpan K v s).map R.mkQ) ↔ _
  rw [Submodule.comap_map_mkQ]

/-- The branch test with relation generators equals the branch test in the native quotient. -/
theorem mem_candidateSpan_union_iff_quotient (s : Finset ι)
    (hR : candidateSpan K v s = R) (t : Finset ι) (i : ι) :
    v i ∈ candidateSpan K v (s ∪ t) ↔
      R.mkQ (v i) ∈ candidateSpan K (R.mkQ ∘ v) t := by
  rw [candidateSpan_union, hR, quotient_mem_candidateSpan_iff]

/-- The relations-first identity with an arbitrary additional initial set. -/
theorem select_union_eq_quotient (s : Finset ι) (hR : candidateSpan K v s = R)
    (t : Finset ι) (order : List ι) :
    select K v (s ∪ t) order = s ∪ select K (R.mkQ ∘ v) t order := by
  induction order generalizing t with
  | nil => rfl
  | cons i order ih =>
      have htest := mem_candidateSpan_union_iff_quotient K v R s hR t i
      by_cases hi : R.mkQ (v i) ∈ candidateSpan K (R.mkQ ∘ v) t
      · rw [select_cons, ite_eq_left (htest.mpr hi), select_cons, Function.comp_apply, ite_eq_left hi]
        exact ih t
      · rw [select_cons, ite_eq_right (fun h => hi (htest.mp h)), select_cons,
          Function.comp_apply, ite_eq_right hi]
        simpa only [Finset.union_insert] using ih (insert i t)

/-- Starting ordinary selection with relation generators has exactly the quotient survivors. -/
theorem select_relations_first (s : Finset ι) (hR : candidateSpan K v s = R)
    (order : List ι) :
    select K v s order = s ∪ select K (R.mkQ ∘ v) ∅ order := by
  simpa only [Finset.union_empty] using
    select_union_eq_quotient K v R s hR ∅ order

/-- A raw relation prefix is itself selected from the empty set before physical candidates are
processed. Its selected span is derived from `candidateSpan_select`, so the raw relation family
need not be independent. -/
theorem select_relation_prefix (relations order : List ι)
    (hR : candidateSpan K v relations.toFinset = R) :
    select K v ∅ (relations ++ order) =
      select K v ∅ relations ∪ select K (R.mkQ ∘ v) ∅ order := by
  rw [select_append]
  have hselected : candidateSpan K v (select K v ∅ relations) = R := by
    rw [candidateSpan_select, Finset.empty_union, hR]
  exact select_relations_first K v R (select K v ∅ relations) hselected order

/-- With distinct relation and physical label sets, dropping relation labels leaves precisely
the candidates retained by selection in the quotient. -/
theorem select_sdiff_relations (s : Finset ι) (hR : candidateSpan K v s = R)
    (order : List ι) (hdisjoint : Disjoint s order.toFinset) :
    select K v s order \ s = select K (R.mkQ ∘ v) ∅ order := by
  rw [select_relations_first K v R s hR order]
  apply Finset.union_sdiff_cancel_left
  apply Finset.disjoint_left.mpr
  intro i his hiq
  have hio : i ∈ order.toFinset := by
    have h := select_subset K (R.mkQ ∘ v) ∅ order hiq
    simpa only [Finset.empty_union] using h
  exact Finset.disjoint_left.mp hdisjoint his hio

/-- For a raw relation prefix disjoint from the physical labels, removing all relation labels
after the combined scan gives exactly the quotient selector. -/
theorem select_relation_prefix_sdiff (relations order : List ι)
    (hR : candidateSpan K v relations.toFinset = R)
    (hdisjoint : Disjoint relations.toFinset order.toFinset) :
    select K v ∅ (relations ++ order) \ relations.toFinset =
      select K (R.mkQ ∘ v) ∅ order := by
  rw [select_relation_prefix K v R relations order hR]
  ext i
  constructor
  · intro hi
    obtain ⟨hiunion, hinot⟩ := Finset.mem_sdiff.mp hi
    rcases Finset.mem_union.mp hiunion with hirelation | hiquotient
    · have hiin : i ∈ relations.toFinset := by
        have h := select_subset K v ∅ relations hirelation
        simpa only [Finset.empty_union] using h
      exact (hinot hiin).elim
    · exact hiquotient
  · intro hiquotient
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_union_right _ hiquotient, ?_⟩
    intro hirelation
    have hiorder : i ∈ order.toFinset := by
      have h := select_subset K (R.mkQ ∘ v) ∅ order hiquotient
      simpa only [Finset.empty_union] using h
    exact Finset.disjoint_left.mp hdisjoint hirelation hiorder

/-- The selected quotient candidates form a native basis of the image of the finite candidate
span. No spanning assumption on the entire ambient module is used. -/
noncomputable def quotientBasis (order : List ι) :
    Module.Basis {i // i ∈ select K (R.mkQ ∘ v) ∅ order} K
      ((candidateSpan K v order.toFinset).map R.mkQ) :=
  (selectedBasis K (R.mkQ ∘ v) ∅ order
    (by simpa only [Finset.coe_empty] using linearIndepOn_empty K (R.mkQ ∘ v))).map
      (LinearEquiv.ofEq _ _ (by
        rw [candidateSpan_select, Finset.empty_union, candidateSpan_quotient]))

@[simp]
theorem quotientBasis_apply (order : List ι)
    (i : {i // i ∈ select K (R.mkQ ∘ v) ∅ order}) :
    (quotientBasis K v R order i : V ⧸ R) = R.mkQ (v i.1) := by
  simp only [quotientBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    selectedBasis_apply, Function.comp_apply]

/-- The same ordered survivors form a basis of the entire quotient when the relation and
candidate spans together generate the ambient module. -/
noncomputable def quotientBasisOfSpan (order : List ι)
    (hspan : R ⊔ candidateSpan K v order.toFinset = ⊤) :
    Module.Basis {i // i ∈ select K (R.mkQ ∘ v) ∅ order} K (V ⧸ R) :=
  (quotientBasis K v R order).map
    (LinearEquiv.ofTop _ ((Submodule.map_mkQ_eq_top R _).mpr hspan))

@[simp]
theorem quotientBasisOfSpan_apply (order : List ι)
    (hspan : R ⊔ candidateSpan K v order.toFinset = ⊤)
    (i : {i // i ∈ select K (R.mkQ ∘ v) ∅ order}) :
    quotientBasisOfSpan K v R order hspan i = R.mkQ (v i.1) := by
  simp only [quotientBasisOfSpan, Module.Basis.map_apply, LinearEquiv.ofTop_apply,
    quotientBasis_apply]

end Quotient

end InfoGeometry.LinearAlgebra.OrderedQuotientBasis
