/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Types.Yoneda
import Mathlib.CategoryTheory.Limits.ColimitLimit
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
import InfoGeometry.Canonical.FilteredDirectInverseColimit
import InfoGeometry.Canonical.FilteredDirectInverseColimitReadback

/-!
# Typed Category Inductive Colimits & Inverse Limits Poset (`𝔗ℭ₁ ≺ … ≺ 𝔗ℭ₇`)

### Audit Classification (BUCKET 1 / BUCKET 2 / BUCKET 3)
* **BUCKET 1 (Keep / Genuine Native Mathlib Owners)**:
  - `TypedCategoryLimitColimitStage` (`TC1`–`TC7` 7-stage linear order and acyclic causal DAG).
  - `typedInductiveDiagram` (`I ⥤ Type u`) and `typedInverseDiagram` (`Iᵒᵖ ⥤ Type u`) for
    preorder-indexed covariant and contravariant type families.
  - `tc1_typed_inductive_and_inverse_diagram_functoriality_and_retraction_section`: functoriality
    of preorder diagrams and retraction–section injectivity, surjectivity, and idempotence.
  - `typedFilteredColimitTypeStageInjective` and `typedFilteredColimitStageInjective`: global
    injectivity of `F.ιColimitType j` and `colimit.ι F j` for filtered type diagrams with injective
    transition maps.
  - `tc2_typed_inductive_colimit_quotient_universal_and_filtered_injectivity`: native Mathlib
    `Functor.ColimitType`, `Types.colimitEquivColimitType`, `Types.FilteredColimit.colimit_eq_iff`,
    and filtered stage injectivity.
  - `typedInverseSectionsEquivCompatibleThreads` and `typedInverseLimitEquivCompatibleThreads`:
    equivalence between `(typedInverseDiagram B π h_id h_comp).sections`, `limit (typedInverseDiagram ...)`,
    and the subtype of compatible projective threads `{ u : ∀ i : I, B i // ∀ {i j : I} (hij : i ≤ j), π hij (u j) = u i }`.
  - `tc3_typed_inverse_limit_sections_universal_and_thread_equivalence`: native Mathlib
    `Types.isLimitEquivSections`, `Types.limitEquivSections`, `Types.Limit.mk`, and thread
    equivalences.
  - `isColimitHomEquivYonedaSections` and `isLimitHomEquivCoyonedaSections`: universal Hom-duality
    identifying `(c.pt ⟶ X) ≃ (F.op ⋙ yoneda.obj X).sections` for colimit cocones and
    `(X ⟶ l.pt) ≃ (F ⋙ coyoneda.obj (Opposite.op X)).sections` for limit cones, paired with
    `limitCompYonedaIsoCocone` and `limitCompCoyonedaIsoCone`.
  - `tc4_yoneda_coyoneda_colimit_limit_hom_duality`: round-trip and stage evaluation laws for
    Yoneda/Coyoneda colimit–limit Hom-duality.
  - `tc5_typed_filtered_colimit_commutes_with_finite_limit`: native Mathlib bijectivity of
    `colimitLimitToLimitColimit F` (`colimitLimitToLimitColimit_injective`,
    `colimitLimitToLimitColimit_surjective`) and isomorphism laws of `colimitLimitIso G` in `Type u`.
  - `cantorTypedInverseDiagram`, `cantorBoundaryEquivTypedInverseSections`, and
    `cantorBoundaryEquivTypedInverseLimit`: native `ℕᵒᵖ ⥤ Type` inverse-limit realization of
    `CantorBoundary` and contravariant pullback to UHF cylinder observables.
  - `tc6_cantor_typed_inverse_limit_sections_and_uhf_cylinder_colimit` and
    `tc7_typed_category_inductive_colimit_inverse_limit_master_synthesis`.
* **BUCKET 2 (Rewrite / Eliminated custom `structure` wrappers)**:
  - Replaced custom projective-limit and retraction–section wrapper structures with native Mathlib
    `Functor.sections`, `Functor.ColimitType`, `Types.limitEquivSections`, and pure subtypes.
* **BUCKET 3 (Delete / Excluded)**:
  - Zero `sorry`, zero `admit`, zero custom `axiom`, zero `structure` wrappers, zero `_True` stubs.
-/

noncomputable section

namespace InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.Types
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

universe v u w

/-!
## Part I: 7-Stage Typed Category Colimit & Inverse-Limit Poset (`𝔗ℭ₁ ≺ … ≺ 𝔗ℭ₇`)
-/

/-- The 7 developmental stages of the typed category (`Type u`) inductive-colimit and
inverse-limit spine (`𝔗ℭ₁ ≺ … ≺ 𝔗ℭ₇`). -/
inductive TypedCategoryLimitColimitStage : Type
  | TC1_TypedInductiveAndInversePreorderDiagramsAndRetractionSection
  | TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity
  | TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence
  | TC4_YonedaCoyonedaColimitLimitHomDuality
  | TC5_TypedFilteredColimitCommutesWithFiniteLimit
  | TC6_CantorTypedInverseLimitSectionsAndUHFCylinderColimit
  | TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis
  deriving DecidableEq, Repr, Inhabited

namespace TypedCategoryLimitColimitStage

/-- Numerical topological rank (`0` through `6`) of each stage in `TypedCategoryLimitColimitStage`. -/
def rank : TypedCategoryLimitColimitStage → ℕ
  | .TC1_TypedInductiveAndInversePreorderDiagramsAndRetractionSection => 0
  | .TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity => 1
  | .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence       => 2
  | .TC4_YonedaCoyonedaColimitLimitHomDuality                         => 3
  | .TC5_TypedFilteredColimitCommutesWithFiniteLimit                  => 4
  | .TC6_CantorTypedInverseLimitSectionsAndUHFCylinderColimit         => 5
  | .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis     => 6

/-- Injectivity of the stage rank assignment `rank`. -/
theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

instance instLinearOrder : LinearOrder TypedCategoryLimitColimitStage :=
  LinearOrder.lift' rank rank_injective

/-- Direct dependency relation between stages of `TypedCategoryLimitColimitStage`. -/
def causalEdge : TypedCategoryLimitColimitStage → TypedCategoryLimitColimitStage → Prop
  | .TC1_TypedInductiveAndInversePreorderDiagramsAndRetractionSection,
    .TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity => True
  | .TC1_TypedInductiveAndInversePreorderDiagramsAndRetractionSection,
    .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence => True
  | .TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity,
    .TC4_YonedaCoyonedaColimitLimitHomDuality => True
  | .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence,
    .TC4_YonedaCoyonedaColimitLimitHomDuality => True
  | .TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity,
    .TC5_TypedFilteredColimitCommutesWithFiniteLimit => True
  | .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence,
    .TC5_TypedFilteredColimitCommutesWithFiniteLimit => True
  | .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence,
    .TC6_CantorTypedInverseLimitSectionsAndUHFCylinderColimit => True
  | .TC4_YonedaCoyonedaColimitLimitHomDuality,
    .TC6_CantorTypedInverseLimitSectionsAndUHFCylinderColimit => True
  | .TC2_TypedInductiveColimitQuotientUniversalAndFilteredInjectivity,
    .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis => True
  | .TC3_TypedInverseLimitSectionsUniversalAndThreadEquivalence,
    .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis => True
  | .TC4_YonedaCoyonedaColimitLimitHomDuality,
    .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis => True
  | .TC5_TypedFilteredColimitCommutesWithFiniteLimit,
    .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis => True
  | .TC6_CantorTypedInverseLimitSectionsAndUHFCylinderColimit,
    .TC7_TypedCategoryInductiveColimitInverseLimitMasterSynthesis => True
  | _, _ => False

/-- Every direct causal edge strictly increases the stage rank. -/
theorem causalEdge_rank_lt {a b : TypedCategoryLimitColimitStage}
    (h : causalEdge a b) : a.rank < b.rank := by
  cases a <;> cases b <;> cases h <;> decide

/-- Every non-empty transitive path strictly increases the stage rank. -/
theorem transGen_causalEdge_rank_lt {a b : TypedCategoryLimitColimitStage}
    (h : Relation.TransGen causalEdge a b) : a.rank < b.rank := by
  induction h with
  | single h1 => exact causalEdge_rank_lt h1
  | tail _ h2 ih => exact Nat.lt_trans ih (causalEdge_rank_lt h2)

/-- Strict acyclicity of the `TypedCategoryLimitColimitStage` dependency graph. -/
theorem causalEdge_acyclic (s : TypedCategoryLimitColimitStage) :
    ¬ Relation.TransGen causalEdge s s := by
  intro h
  exact Nat.lt_irrefl s.rank (transGen_causalEdge_rank_lt h)

end TypedCategoryLimitColimitStage

/-!
## Part II: Stage `𝔗ℭ₁` — Typed Inductive (`I ⥤ Type u`) and Inverse (`Iᵒᵖ ⥤ Type u`) Preorder Diagrams
-/

/-- Native `I ⥤ Type u` covariant diagram built from a preorder-indexed family `A : I → Type u`
and upward transition maps `ι : ∀ {i j : I}, i ≤ j → A i → A j`. -/
def typedInductiveDiagram {I : Type v} [Preorder I]
    (A : I → Type u)
    (ι : ∀ {i j : I}, i ≤ j → A i → A j)
    (h_id : ∀ (i : I) (x : A i), ι (le_refl i) x = x)
    (h_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
      ι hjk (ι hij x) = ι (le_trans hij hjk) x) :
    I ⥤ Type u where
  obj i := A i
  map f := ↾(ι (leOfHom f))
  map_id i := by
    ext x
    exact h_id i x
  map_comp f g := by
    ext x
    exact (h_comp (leOfHom f) (leOfHom g) x).symm

/-- Native `Iᵒᵖ ⥤ Type u` contravariant diagram built from a preorder-indexed family `B : I → Type u`
and downward restriction maps `π : ∀ {i j : I}, i ≤ j → B j → B i`. -/
def typedInverseDiagram {I : Type v} [Preorder I]
    (B : I → Type u)
    (π : ∀ {i j : I}, i ≤ j → B j → B i)
    (h_id : ∀ (i : I) (x : B i), π (le_refl i) x = x)
    (h_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : B k),
      π hij (π hjk x) = π (le_trans hij hjk) x) :
    Iᵒᵖ ⥤ Type u where
  obj i := B i.unop
  map f := ↾(π (leOfHom f.unop))
  map_id i := by
    ext x
    exact h_id i.unop x
  map_comp f g := by
    ext x
    exact (h_comp (leOfHom g.unop) (leOfHom f.unop) x).symm

/-- **Stage `𝔗ℭ₁` (`tc1_typed_inductive_and_inverse_diagram_functoriality_and_retraction_section`)**:
For any preorder `I`, family `A : I → Type u`, upward transition maps `ι`, and downward restriction
maps `π` satisfying `π hij (ι hij x) = x`:
1. `(typedInductiveDiagram A ι hι_id hι_comp).map (homOfLE hij) x = ι hij x`,
2. `(typedInverseDiagram A π hπ_id hπ_comp).map (homOfLE hij).op y = π hij y`,
3. Every upward transition map `(typedInductiveDiagram A ι hι_id hι_comp).map (homOfLE hij)` is injective,
4. Every downward restriction map `(typedInverseDiagram A π hπ_id hπ_comp).map (homOfLE hij).op` is surjective,
5. The composite coarse-graining endomap `fun y => ι hij (π hij y)` is idempotent and fixes every
   embedded coarse element `ι hij x`. -/
theorem tc1_typed_inductive_and_inverse_diagram_functoriality_and_retraction_section
    {I : Type v} [Preorder I]
    (A : I → Type u)
    (ι : ∀ {i j : I}, i ≤ j → A i → A j)
    (hι_id : ∀ (i : I) (x : A i), ι (le_refl i) x = x)
    (hι_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
      ι hjk (ι hij x) = ι (le_trans hij hjk) x)
    (π : ∀ {i j : I}, i ≤ j → A j → A i)
    (hπ_id : ∀ (i : I) (x : A i), π (le_refl i) x = x)
    (hπ_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A k),
      π hij (π hjk x) = π (le_trans hij hjk) x)
    (h_ret : ∀ {i j : I} (hij : i ≤ j) (x : A i), π hij (ι hij x) = x)
    {i j : I} (hij : i ≤ j) (x : A i) (y : A j) :
    let F_ind := typedInductiveDiagram A ι hι_id hι_comp
    let F_inv := typedInverseDiagram A π hπ_id hπ_comp
    F_ind.map (homOfLE hij) x = ι hij x ∧
    F_inv.map (homOfLE hij).op y = π hij y ∧
    Function.Injective (F_ind.map (homOfLE hij)) ∧
    Function.Surjective (F_inv.map (homOfLE hij).op) ∧
    ι hij (π hij (ι hij (π hij y))) = ι hij (π hij y) ∧
    ι hij (π hij (ι hij x)) = ι hij x := by
  intro F_ind F_inv
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : π hij (ι hij a) = π hij (ι hij b) := congrArg (π hij) hab
    rw [h_ret hij a, h_ret hij b] at h1
    exact h1
  · intro a
    exact ⟨ι hij a, h_ret hij a⟩
  · rw [h_ret hij (π hij y)]
  · rw [h_ret hij x]

/-!
## Part III: Stage `𝔗ℭ₂` — Typed Inductive Colimits (`Functor.ColimitType`, `Types.colimitEquivColimitType`, `FilteredColimit.colimit_eq_iff`, and Global Stage Injectivity)
-/

/-- In any filtered category `J`, if a type diagram `F : J ⥤ Type u` has injective transition maps
`F.map f`, then every canonical stage map `F.ιColimitType j : F.obj j → F.ColimitType` into the
concrete colimit quotient `F.ColimitType` is globally injective. -/
theorem typedFilteredColimitTypeStageInjective
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ Type u)
    (h_inj : ∀ {j k : J} (f : j ⟶ k), Function.Injective (F.map f))
    (j : J) :
    Function.Injective (F.ιColimitType j) := by
  intro x y hxy
  rw [Functor.ιColimitType_eq_iff_of_isFiltered'] at hxy
  rcases hxy with ⟨k, f, hfk⟩
  exact h_inj f hfk

/-- In any filtered category `J`, if a type diagram `F : J ⥤ Type u` (`[HasColimit F]`) has
injective transition maps `F.map f`, then every categorical colimit coprojection
`colimit.ι F j : F.obj j ⟶ colimit F` is globally injective. -/
theorem typedFilteredColimitStageInjective
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ Type u) [HasColimit F]
    (h_inj : ∀ {j k : J} (f : j ⟶ k), Function.Injective (F.map f))
    (j : J) :
    Function.Injective (colimit.ι F j) := by
  intro x y hxy
  rcases (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit F) x y).mp hxy with ⟨k, f, hfk⟩
  exact h_inj f hfk

/-- **Stage `𝔗ℭ₂` (`tc2_typed_inductive_colimit_quotient_universal_and_filtered_injectivity`)**:
For any filtered category `J` and diagram `F : J ⥤ Type u` (`[HasColimit F]`):
1. `Types.colimitEquivColimitType F : (colimit F : Type u) ≃ F.ColimitType` maps `colimit.ι F j x`
   to `F.ιColimitType j x` and its inverse maps `F.ιColimitType j x` back to `colimit.ι F j x`,
2. For any type cocone `c : F.CoconeTypes`, `F.descColimitType c (F.ιColimitType j x) = c.ι j x`,
3. Two stage elements `xi : F.obj i` and `xj : F.obj j` become equal in `colimit F` if and only if
   they become equal at a common future stage `k : J` (`Types.FilteredColimit.colimit_eq_iff`),
4. Whenever all transition maps `F.map f` are injective, both `F.ιColimitType j` and
   `colimit.ι F j` are globally injective at every stage `j : J`. -/
theorem tc2_typed_inductive_colimit_quotient_universal_and_filtered_injectivity
    {J : Type v} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ Type u) [HasColimit F]
    (c : F.CoconeTypes)
    {i j : J} (xi : F.obj i) (xj : F.obj j) :
    colimitEquivColimitType F (colimit.ι F i xi) = F.ιColimitType i xi ∧
    (colimitEquivColimitType F).symm (F.ιColimitType i xi) = colimit.ι F i xi ∧
    F.descColimitType c (F.ιColimitType i xi) = c.ι i xi ∧
    (colimit.ι F i xi = colimit.ι F j xj ↔
      ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f xi = F.map g xj) ∧
    ((∀ {a b : J} (f : a ⟶ b), Function.Injective (F.map f)) →
      Function.Injective (F.ιColimitType i) ∧ Function.Injective (colimit.ι F i)) := by
  refine ⟨colimitEquivColimitType_apply F i xi,
          colimitEquivColimitType_symm_apply F i xi,
          rfl,
          Types.FilteredColimit.colimit_eq_iff F,
          fun h_inj =>
            ⟨typedFilteredColimitTypeStageInjective F h_inj i,
             typedFilteredColimitStageInjective F h_inj i⟩⟩

/-!
## Part IV: Stage `𝔗ℭ₃` — Typed Inverse Limits (`Functor.sections`, `Types.limitEquivSections`, and Compatible Thread Equivalence)
-/

/-- The subtype of compatible projective threads `{ u : ∀ i : I, B i // ∀ {i j : I} (hij : i ≤ j), π hij (u j) = u i }`
for a contravariant preorder system `(B, π)`. -/
def CompatibleProjectiveThreads {I : Type v} [Preorder I]
    (B : I → Type u) (π : ∀ {i j : I}, i ≤ j → B j → B i) : Type (max v u) :=
  { u : ∀ i : I, B i // ∀ {i j : I} (hij : i ≤ j), π hij (u j) = u i }

/-- Canonical equivalence between native Mathlib categorical sections
`(typedInverseDiagram B π h_id h_comp).sections` and `CompatibleProjectiveThreads B π`. -/
def typedInverseSectionsEquivCompatibleThreads
    {I : Type v} [Preorder I]
    (B : I → Type u)
    (π : ∀ {i j : I}, i ≤ j → B j → B i)
    (h_id : ∀ (i : I) (x : B i), π (le_refl i) x = x)
    (h_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : B k),
      π hij (π hjk x) = π (le_trans hij hjk) x) :
    (typedInverseDiagram B π h_id h_comp).sections ≃ CompatibleProjectiveThreads B π where
  toFun s :=
    ⟨fun i => s.val (Opposite.op i),
     fun {_ _} hij => s.property (homOfLE hij).op⟩
  invFun u :=
    ⟨fun i => u.val i.unop,
     fun {_ _} f => u.property (leOfHom f.unop)⟩
  left_inv s := by
    ext i
    rfl
  right_inv u := by
    apply Subtype.ext
    funext i
    rfl

/-- Canonical equivalence between the categorical inverse limit
`limit (typedInverseDiagram B π h_id h_comp)` in `Type u` and `CompatibleProjectiveThreads B π`. -/
def typedInverseLimitEquivCompatibleThreads
    {I : Type u} [Preorder I]
    (B : I → Type u)
    (π : ∀ {i j : I}, i ≤ j → B j → B i)
    (h_id : ∀ (i : I) (x : B i), π (le_refl i) x = x)
    (h_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : B k),
      π hij (π hjk x) = π (le_trans hij hjk) x) :
    limit (typedInverseDiagram B π h_id h_comp) ≃ CompatibleProjectiveThreads B π :=
  (limitEquivSections (typedInverseDiagram B π h_id h_comp)).trans
    (typedInverseSectionsEquivCompatibleThreads B π h_id h_comp)

/-- **Stage `𝔗ℭ₃` (`tc3_typed_inverse_limit_sections_universal_and_thread_equivalence`)**:
For any preorder `I : Type u` and contravariant type system `(B, π)`:
1. `limitEquivSections F : limit F ≃ F.sections` projects at stage `Opposite.op i` as
   `limit.π F (Opposite.op i) z` and satisfies both round-trip identities,
2. `typedInverseSectionsEquivCompatibleThreads` and `typedInverseLimitEquivCompatibleThreads`
   are two-sided inverse equivalences identifying `limit (typedInverseDiagram B π h_id h_comp)`
   with `CompatibleProjectiveThreads B π`,
3. Any compatible thread `u : CompatibleProjectiveThreads B π` constructs a limit point
   `z := (typedInverseLimitEquivCompatibleThreads B π h_id h_comp).symm u` whose stage-`i`
   projection is `limit.π _ (Opposite.op i) z = u.val i` and satisfies
   `π hij (limit.π _ (Opposite.op j) z) = limit.π _ (Opposite.op i) z`. -/
theorem tc3_typed_inverse_limit_sections_universal_and_thread_equivalence
    {I : Type u} [Preorder I]
    (B : I → Type u)
    (π : ∀ {i j : I}, i ≤ j → B j → B i)
    (h_id : ∀ (i : I) (x : B i), π (le_refl i) x = x)
    (h_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : B k),
      π hij (π hjk x) = π (le_trans hij hjk) x)
    (z : limit (typedInverseDiagram B π h_id h_comp))
    (u : CompatibleProjectiveThreads B π)
    {i j : I} (hij : i ≤ j) :
    let F := typedInverseDiagram B π h_id h_comp
    let E := typedInverseLimitEquivCompatibleThreads B π h_id h_comp
    (E z).val i = limit.π F (Opposite.op i) z ∧
    E.symm (E z) = z ∧
    E (E.symm u) = u ∧
    limit.π F (Opposite.op i) (E.symm u) = u.val i ∧
    π hij (limit.π F (Opposite.op j) (E.symm u)) =
      limit.π F (Opposite.op i) (E.symm u) := by
  intro F E
  have hsymm_i : limit.π F (Opposite.op i) (E.symm u) = u.val i := by
    dsimp [E, typedInverseLimitEquivCompatibleThreads]
    exact limitEquivSections_symm_apply F
      ((typedInverseSectionsEquivCompatibleThreads B π h_id h_comp).symm u) (Opposite.op i)
  have hsymm_j : limit.π F (Opposite.op j) (E.symm u) = u.val j := by
    dsimp [E, typedInverseLimitEquivCompatibleThreads]
    exact limitEquivSections_symm_apply F
      ((typedInverseSectionsEquivCompatibleThreads B π h_id h_comp).symm u) (Opposite.op j)
  refine ⟨rfl, E.symm_apply_apply z, E.apply_symm_apply u, hsymm_i, ?_⟩
  rw [hsymm_j, hsymm_i]
  exact u.property hij

/-!
## Part V: Stage `𝔗ℭ₄` — Universal Yoneda / Coyoneda Colimit–Limit Hom Duality
`(c.pt ⟶ X) ≃ (F.op ⋙ yoneda.obj X).sections` and `(X ⟶ l.pt) ≃ (F ⋙ coyoneda.obj (op X)).sections`
-/

/-- **Universal Colimit-to-Inverse-Limit Yoneda Hom Duality (`isColimitHomEquivYonedaSections`)**:
For any functor `F : J ⥤ C`, any colimit cocone `hc : IsColimit c`, and any target object `X : C`,
morphisms `c.pt ⟶ X` out of the colimit apex are canonically equivalent (`≃`) to sections of the
contravariant Yoneda diagram `(F.op ⋙ yoneda.obj X).sections` (the concrete inverse limit of
`j ↦ (F.obj j ⟶ X)`). -/
def isColimitHomEquivYonedaSections
    {J : Type v} [Category.{w} J] {C : Type u} [Category.{v} C]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (X : C) :
    (c.pt ⟶ X) ≃ (F.op ⋙ yoneda.obj X).sections where
  toFun f :=
    ⟨fun j => c.ι.app j.unop ≫ f,
     fun {j j'} g => by
       dsimp
       rw [← Category.assoc, c.w g.unop]⟩
  invFun s :=
    hc.desc
      { pt := X
        ι := (opCompYonedaSectionsEquiv F X) s }
  left_inv f := by
    refine hc.hom_ext (fun j => ?_)
    rw [hc.fac]
    rfl
  right_inv s := by
    ext j
    dsimp
    exact hc.fac { pt := X, ι := (opCompYonedaSectionsEquiv F X) s } j.unop

/-- **Universal Limit-to-Inverse-Limit Coyoneda Hom Duality (`isLimitHomEquivCoyonedaSections`)**:
For any functor `F : J ⥤ C`, any limit cone `hl : IsLimit l`, and any source object `X : C`,
morphisms `X ⟶ l.pt` into the limit apex are canonically equivalent (`≃`) to sections of the
covariant Coyoneda diagram `(F ⋙ coyoneda.obj (Opposite.op X)).sections` (the concrete inverse
limit of `j ↦ (X ⟶ F.obj j)`). -/
def isLimitHomEquivCoyonedaSections
    {J : Type v} [Category.{w} J] {C : Type u} [Category.{v} C]
    {F : J ⥤ C} {l : Cone F} (hl : IsLimit l) (X : C) :
    (X ⟶ l.pt) ≃ (F ⋙ coyoneda.obj (Opposite.op X)).sections where
  toFun g :=
    ⟨fun j => g ≫ l.π.app j,
     fun {j j'} f => by
       dsimp
       rw [Category.assoc, l.w f]⟩
  invFun s :=
    hl.lift
      { pt := X
        π := (compCoyonedaSectionsEquiv F X) s }
  left_inv g := by
    refine hl.hom_ext (fun j => ?_)
    rw [hl.fac]
    rfl
  right_inv s := by
    ext j
    dsimp
    exact hl.fac { pt := X, π := (compCoyonedaSectionsEquiv F X) s } j

/-- **Stage `𝔗ℭ₄` (`tc4_yoneda_coyoneda_colimit_limit_hom_duality`)**:
For any small category `J : Type v`, category `C : Type u` (`[Category.{v} C]`), functor `F : J ⥤ C`,
colimit cocone `hc : IsColimit c`, limit cone `hl : IsLimit l`, and object `X : C`:
1. `isColimitHomEquivYonedaSections hc X` evaluates at `Opposite.op j` as `c.ι.app j ≫ f` and
   satisfies both two-sided inverse identities,
2. `isLimitHomEquivCoyonedaSections hl X` evaluates at `j` as `g ≫ l.π.app j` and satisfies both
   two-sided inverse identities,
3. Native Mathlib's `limitCompYonedaIsoCocone F X : limit (F.op ⋙ yoneda.obj X) ≅ (F ⟶ (Functor.const J).obj X)`
   and `limitCompCoyonedaIsoCone F X : limit (F ⋙ coyoneda.obj (Opposite.op X)) ≅ ((Functor.const J).obj X ⟶ F)`
   satisfy their two-sided isomorphism laws. -/
theorem tc4_yoneda_coyoneda_colimit_limit_hom_duality
    {J : Type v} [SmallCategory J] {C : Type u} [Category.{v} C]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    {l : Cone F} (hl : IsLimit l)
    (X : C) (j : J)
    (f : c.pt ⟶ X) (s_colim : (F.op ⋙ yoneda.obj X).sections)
    (g : X ⟶ l.pt) (s_lim : (F ⋙ coyoneda.obj (Opposite.op X)).sections) :
    (isColimitHomEquivYonedaSections hc X f).val (Opposite.op j) = c.ι.app j ≫ f ∧
    (isColimitHomEquivYonedaSections hc X).symm (isColimitHomEquivYonedaSections hc X f) = f ∧
    isColimitHomEquivYonedaSections hc X ((isColimitHomEquivYonedaSections hc X).symm s_colim) = s_colim ∧
    (isLimitHomEquivCoyonedaSections hl X g).val j = g ≫ l.π.app j ∧
    (isLimitHomEquivCoyonedaSections hl X).symm (isLimitHomEquivCoyonedaSections hl X g) = g ∧
    isLimitHomEquivCoyonedaSections hl X ((isLimitHomEquivCoyonedaSections hl X).symm s_lim) = s_lim ∧
    (limitCompYonedaIsoCocone F X).hom ≫ (limitCompYonedaIsoCocone F X).inv = 𝟙 _ ∧
    (limitCompCoyonedaIsoCone F X).hom ≫ (limitCompCoyonedaIsoCone F X).inv = 𝟙 _ := by
  have hY1 := (isColimitHomEquivYonedaSections hc X).symm_apply_apply f
  have hY2 := (isColimitHomEquivYonedaSections hc X).apply_symm_apply s_colim
  have hC1 := (isLimitHomEquivCoyonedaSections hl X).symm_apply_apply g
  have hC2 := (isLimitHomEquivCoyonedaSections hl X).apply_symm_apply s_lim
  exact ⟨rfl, hY1, hY2, rfl, hC1, hC2,
         (limitCompYonedaIsoCocone F X).hom_inv_id,
         (limitCompCoyonedaIsoCone F X).hom_inv_id⟩

/-!
## Part VI: Stage `𝔗ℭ₅` — Filtered Colimits Commute with Finite Limits in `Type u`
-/

/-- **Stage `𝔗ℭ₅` (`tc5_typed_filtered_colimit_commutes_with_finite_limit`)**:
For any finite category `J : Type u` (`[SmallCategory J] [FinCategory J]`), filtered category
`K : Type u` (`[SmallCategory K] [IsFiltered K]`), uncurried diagram `F : J × K ⥤ Type u`, and
curried diagram `G : J ⥤ K ⥤ Type u`:
1. The canonical comparison map `colimitLimitToLimitColimit F` from the filtered colimit of finite
   limits to the finite limit of filtered colimits is both injective and surjective,
2. The curried interchange `colimitLimitIso G : colimit (limit G) ≅ limit (colimit G.flip)` is a
   two-sided categorical isomorphism in `Type u`,
3. `colimitLimitIso G` satisfies the stagewise commutativity law
   `colimit.ι (limit G) k ≫ (colimitLimitIso G).hom ≫ limit.π (colimit G.flip) j = (limit.π G j).app k ≫ (colimit.ι G.flip k).app j`. -/
theorem tc5_typed_filtered_colimit_commutes_with_finite_limit
    {J : Type u} [SmallCategory J] [FinCategory J]
    {K : Type u} [SmallCategory K] [IsFiltered K]
    (F : J × K ⥤ Type u)
    (G : J ⥤ K ⥤ Type u)
    (j : J) (k : K) :
    Function.Injective (colimitLimitToLimitColimit F) ∧
    Function.Surjective (colimitLimitToLimitColimit F) ∧
    (colimitLimitIso G).hom ≫ (colimitLimitIso G).inv = 𝟙 _ ∧
    (colimitLimitIso G).inv ≫ (colimitLimitIso G).hom = 𝟙 _ ∧
    colimit.ι (limit G) k ≫ (colimitLimitIso G).hom ≫ limit.π (colimit G.flip) j =
      (limit.π G j).app k ≫ (colimit.ι G.flip k).app j := by
  have hinj := colimitLimitToLimitColimit_injective F
  have hsurj := colimitLimitToLimitColimit_surjective F
  have hcomm := ι_colimitLimitIso_limit_π G k j
  exact ⟨hinj, hsurj, (colimitLimitIso G).hom_inv_id, (colimitLimitIso G).inv_hom_id, hcomm⟩

/-!
## Part VII: Stage `𝔗ℭ₆` — Cantor Finite-Prefix Typed Inverse Limit (`ℕᵒᵖ ⥤ Type`) & UHF Diagonal Cylinder Inductive System (`ℕ ⥤ Type u`)
-/

/-- Finite prefix restriction `prefixCastLE hij : BitWord n → BitWord m` for `m ≤ n`. -/
def prefixCastLE {m n : ℕ} (hij : m ≤ n) (w : BitWord n) : BitWord m :=
  fun i => w (Fin.castLE hij i)

/-- Identity law for `prefixCastLE`. -/
theorem prefixCastLE_refl (n : ℕ) (w : BitWord n) :
    prefixCastLE (le_refl n) w = w := by
  funext i
  rfl

/-- Composition law for `prefixCastLE`. -/
theorem prefixCastLE_trans {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) (w : BitWord n) :
    prefixCastLE hlm (prefixCastLE hmn w) = prefixCastLE (le_trans hlm hmn) w := by
  funext i
  rfl

/-- The Cantor finite-prefix contravariant diagram `cantorTypedInverseDiagram : ℕᵒᵖ ⥤ Type`
built via `typedInverseDiagram BitWord prefixCastLE`. -/
def cantorTypedInverseDiagram : ℕᵒᵖ ⥤ Type :=
  typedInverseDiagram BitWord prefixCastLE prefixCastLE_refl prefixCastLE_trans

/-- Compatibility of `boundaryPrefix` with `prefixCastLE`: restricting the length-`n` prefix of
`x : CantorBoundary` to length `m ≤ n` gives the length-`m` prefix of `x`. -/
theorem boundaryPrefix_prefixCastLE {m n : ℕ} (hmn : m ≤ n) (x : CantorBoundary) :
    prefixCastLE hmn (boundaryPrefix n x) = boundaryPrefix m x := by
  funext i
  rfl

/-- Equivalence between `PrefixProjectiveLimit` (`CantorProjectiveLimit.lean`) and
`CompatibleProjectiveThreads BitWord prefixCastLE`. -/
def prefixProjectiveLimitEquivCompatibleThreads :
    PrefixProjectiveLimit ≃ CompatibleProjectiveThreads BitWord prefixCastLE where
  toFun p :=
    ⟨fun n => boundaryPrefix n (PrefixProjectiveLimit.toCantor p),
     fun {_ _} hmn => boundaryPrefix_prefixCastLE hmn (PrefixProjectiveLimit.toCantor p)⟩
  invFun u :=
    PrefixProjectiveLimit.mk u.val (fun n => u.property (Nat.le_succ n))
  left_inv p := by
    apply PrefixProjectiveLimit.ext
    funext n
    exact PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word p n
  right_inv u := by
    apply Subtype.ext
    funext n
    exact PrefixProjectiveLimit.boundaryPrefix_toCantor_eq_word
      (PrefixProjectiveLimit.mk u.val (fun k => u.property (Nat.le_succ k))) n

/-- Direct equivalence between the Cantor stream space `CantorBoundary` (`ℕ → Bool`) and
categorical sections `cantorTypedInverseDiagram.sections` of `cantorTypedInverseDiagram : ℕᵒᵖ ⥤ Type`. -/
def cantorBoundaryEquivTypedInverseSections :
    CantorBoundary ≃ cantorTypedInverseDiagram.sections :=
  PrefixProjectiveLimit.cantorEquivPrefixProjectiveLimit.trans
    (prefixProjectiveLimitEquivCompatibleThreads.trans
      (typedInverseSectionsEquivCompatibleThreads
        BitWord prefixCastLE prefixCastLE_refl prefixCastLE_trans).symm)

/-- Direct equivalence between `CantorBoundary` and the categorical limit
`limit cantorTypedInverseDiagram` in `Type`. -/
def cantorBoundaryEquivTypedInverseLimit :
    CantorBoundary ≃ limit cantorTypedInverseDiagram :=
  cantorBoundaryEquivTypedInverseSections.trans
    (limitEquivSections cantorTypedInverseDiagram).symm

/-- The covariant UHF diagonal observable diagram `uhfDiagonalTypedInductiveDiagram R : ℕ ⥤ Type u`
built by pulling back functions `BitWord n → R` along `prefixCastLE`. -/
def uhfDiagonalTypedInductiveDiagram (R : Type u) : ℕ ⥤ Type u :=
  typedInductiveDiagram
    (fun n => BitWord n → R)
    (fun {_ _} hmn f => f ∘ prefixCastLE hmn)
    (fun _ _ => rfl)
    (fun _ _ _ => rfl)

/-- **Stage `𝔗ℭ₆` (`tc6_cantor_typed_inverse_limit_sections_and_uhf_cylinder_colimit`)**:
1. `cantorBoundaryEquivTypedInverseSections : CantorBoundary ≃ cantorTypedInverseDiagram.sections`
   maps `x : CantorBoundary` to the section `(Opposite.op n) ↦ boundaryPrefix n x` and satisfies
   both round-trip identities,
2. `cantorBoundaryEquivTypedInverseLimit : CantorBoundary ≃ limit cantorTypedInverseDiagram`
   satisfies `limit.π cantorTypedInverseDiagram (Opposite.op n) (cantorBoundaryEquivTypedInverseLimit x) = boundaryPrefix n x`,
3. For `R = ℂ`, the one-step transition map `(uhfDiagonalTypedInductiveDiagram ℂ).map (homOfLE (Nat.le_succ n))`
   on `f : DiagAlg n` is identically `diagEmbedSucc n f`, and cylinder pullback to `CantorBoundary`
   satisfies `cylinder (n + 1) (diagEmbedSucc n f) = cylinder n f`. -/
theorem tc6_cantor_typed_inverse_limit_sections_and_uhf_cylinder_colimit
    (x : CantorBoundary) (s : cantorTypedInverseDiagram.sections)
    (n : ℕ) (f_diag : DiagAlg n) :
    (cantorBoundaryEquivTypedInverseSections x).val (Opposite.op n) = boundaryPrefix n x ∧
    cantorBoundaryEquivTypedInverseSections.symm (cantorBoundaryEquivTypedInverseSections x) = x ∧
    cantorBoundaryEquivTypedInverseSections (cantorBoundaryEquivTypedInverseSections.symm s) = s ∧
    limit.π cantorTypedInverseDiagram (Opposite.op n)
      (cantorBoundaryEquivTypedInverseLimit x) = boundaryPrefix n x ∧
    (uhfDiagonalTypedInductiveDiagram ℂ).map (homOfLE (Nat.le_succ n)) f_diag =
      diagEmbedSucc n f_diag ∧
    cylinder (n + 1) (diagEmbedSucc n f_diag) = cylinder n f_diag := by
  have hsec : (cantorBoundaryEquivTypedInverseSections x).val (Opposite.op n) = boundaryPrefix n x :=
    rfl
  have hlim :
      limit.π cantorTypedInverseDiagram (Opposite.op n)
        (cantorBoundaryEquivTypedInverseLimit x) = boundaryPrefix n x := by
    dsimp [cantorBoundaryEquivTypedInverseLimit]
    rw [limitEquivSections_symm_apply]
    exact hsec
  exact ⟨hsec,
         cantorBoundaryEquivTypedInverseSections.symm_apply_apply x,
         cantorBoundaryEquivTypedInverseSections.apply_symm_apply s,
         hlim,
         rfl,
         cylinder_compatible_succ n f_diag⟩

/-- The typed inverse diagram (`Iᵒᵖ ⥤ Type u`) of dual stage modules `A i →ₗ[R] R` associated to
a `FilteredColimit.DirectInductiveSystem R I A`. -/
def dualModuleTypedInverseDiagram
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : FilteredColimit.DirectInductiveSystem R I A) :
    Iᵒᵖ ⥤ Type u :=
  typedInverseDiagram
    (fun i => A i →ₗ[R] R)
    (fun {_ _} hij phi => FilteredColimit.InductiveCocone.dualInverseTransition sys hij phi)
    (fun i phi => by
      ext x
      exact congrArg phi (LinearMap.congr_fun (sys.f_id i) x))
    (fun hij hjk phi =>
      FilteredColimit.InductiveCocone.dual_inverse_comp sys hij hjk phi)

/-- Equivalence between compatible dual inverse families `{ phi // IsDualInverseFamily phi }`
and `CompatibleProjectiveThreads` of stage dual linear maps. -/
def dualInverseFamilyEquivCompatibleThreads
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : FilteredColimit.DirectInductiveSystem R I A) :
    { phi : ∀ i : I, A i →ₗ[R] R //
      FilteredColimit.InductiveCocone.IsDualInverseFamily (sys := sys) phi } ≃
      CompatibleProjectiveThreads (fun i => A i →ₗ[R] R)
        (fun {_ _} hij phi => FilteredColimit.InductiveCocone.dualInverseTransition sys hij phi) :=
  Equiv.refl _

/-- Equivalence between compatible dual inverse families `{ phi // IsDualInverseFamily phi }`
and sections `(dualModuleTypedInverseDiagram sys).sections` of the typed inverse diagram. -/
def dualInverseFamilyEquivTypedInverseSections
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : FilteredColimit.DirectInductiveSystem R I A) :
    { phi : ∀ i : I, A i →ₗ[R] R //
      FilteredColimit.InductiveCocone.IsDualInverseFamily (sys := sys) phi } ≃
      (dualModuleTypedInverseDiagram sys).sections :=
  (dualInverseFamilyEquivCompatibleThreads sys).trans
    (typedInverseSectionsEquivCompatibleThreads
      (fun i => A i →ₗ[R] R)
      (fun {_ _} hij phi => FilteredColimit.InductiveCocone.dualInverseTransition sys hij phi)
      (fun i phi => by
        ext x
        exact congrArg phi (LinearMap.congr_fun (sys.f_id i) x))
      (fun hij hjk phi =>
        FilteredColimit.InductiveCocone.dual_inverse_comp sys hij hjk phi)).symm

/-- Equivalence between the carrier of the `ModuleCat` projective limit
`limit (dualModuleDiagram sys)` and the `Type u` inverse limit `limit (dualModuleTypedInverseDiagram sys)`. -/
noncomputable def dualModuleProjectiveLimitEquivTypedInverseLimit
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : FilteredColimit.DirectInductiveSystem R I A) :
    ((CategoryTheory.Limits.limit
      (FilteredColimit.InductiveCocone.dualModuleDiagram sys) : ModuleCat R) : Type u) ≃
      limit (dualModuleTypedInverseDiagram sys) :=
  (FilteredColimit.InductiveCocone.projectiveLimitEquivDualInverseFamily (sys := sys)).trans
    ((dualInverseFamilyEquivTypedInverseSections sys).trans
      (limitEquivSections (dualModuleTypedInverseDiagram sys)).symm)

/-- **Stage `𝔗ℭ₆` Module-Dual Seam (`tc6b_module_dual_projective_limit_to_typed_inverse_sections_bridge`)**:
For any `DirectInductiveSystem R I A`:
1. `dualInverseFamilyEquivTypedInverseSections sys` identifies compatible dual families with
   sections `(dualModuleTypedInverseDiagram sys).sections` and preserves stage evaluation;
2. `dualModuleProjectiveLimitEquivTypedInverseLimit sys` identifies the `ModuleCat` projective limit
   `limit (dualModuleDiagram sys)` with `limit (dualModuleTypedInverseDiagram sys)` and intertwines
   the `ModuleCat` projection `limit.π (dualModuleDiagram sys) (Opposite.op i)` with the `Type u`
   projection `limit.π (dualModuleTypedInverseDiagram sys) (Opposite.op i)`. -/
theorem tc6b_module_dual_projective_limit_to_typed_inverse_sections_bridge
    {R : Type u} [CommRing R] {I : Type u} [Preorder I]
    {A : I → Type u} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
    (sys : FilteredColimit.DirectInductiveSystem R I A)
    (s : { phi : ∀ i : I, A i →ₗ[R] R //
      FilteredColimit.InductiveCocone.IsDualInverseFamily (sys := sys) phi })
    (z : ((CategoryTheory.Limits.limit
      (FilteredColimit.InductiveCocone.dualModuleDiagram sys) : ModuleCat R) : Type u))
    (i : I) :
    (dualInverseFamilyEquivTypedInverseSections sys s).val (Opposite.op i) = s.val i ∧
    (dualInverseFamilyEquivTypedInverseSections sys).symm
      (dualInverseFamilyEquivTypedInverseSections sys s) = s ∧
    limit.π (dualModuleTypedInverseDiagram sys) (Opposite.op i)
      (dualModuleProjectiveLimitEquivTypedInverseLimit sys z) =
      (CategoryTheory.Limits.limit.π
        (FilteredColimit.InductiveCocone.dualModuleDiagram sys) (Opposite.op i)).hom z := by
  have hsec : (dualInverseFamilyEquivTypedInverseSections sys s).val (Opposite.op i) = s.val i := rfl
  have hproj :
      limit.π (dualModuleTypedInverseDiagram sys) (Opposite.op i)
        (dualModuleProjectiveLimitEquivTypedInverseLimit sys z) =
        (CategoryTheory.Limits.limit.π
          (FilteredColimit.InductiveCocone.dualModuleDiagram sys) (Opposite.op i)).hom z := by
    dsimp [dualModuleProjectiveLimitEquivTypedInverseLimit]
    rw [limitEquivSections_symm_apply]
    rfl
  exact ⟨hsec,
         (dualInverseFamilyEquivTypedInverseSections sys).symm_apply_apply s,
         hproj⟩

/-!
## Part VIII: Stage `𝔗ℭ₇` — Master Synthesis of Typed Category Inductive Colimits & Inverse Limits
-/

/-- **Stage `𝔗ℭ₇` (`tc7_typed_category_inductive_colimit_inverse_limit_master_synthesis`)**:
Master theorem uniting the 7-stage `TypedCategoryLimitColimitStage` poset (`𝔗ℭ₁ ≺ … ≺ 𝔗ℭ₇`):
1. Acyclicity of `TypedCategoryLimitColimitStage.causalEdge`,
2. **Stage `𝔗ℭ₂`**: `Types.colimitEquivColimitType`, `Types.FilteredColimit.colimit_eq_iff`, and
   global stage injectivity `typedFilteredColimitStageInjective` when transition maps are injective,
3. **Stage `𝔗ℭ₃`**: Equivalence between `limit (typedInverseDiagram B π h_id h_comp)`,
   `(typedInverseDiagram B π h_id h_comp).sections`, and `CompatibleProjectiveThreads B π`,
4. **Stage `𝔗ℭ₄`**: Universal Yoneda/Coyoneda Hom-duality equivalences
   `isColimitHomEquivYonedaSections` and `isLimitHomEquivCoyonedaSections`,
5. **Stage `𝔗ℭ₅`**: Bijectivity of `colimitLimitToLimitColimit F_bif` and isomorphism laws of
   `colimitLimitIso G_bif` in `Type u`,
6. **Stage `𝔗ℭ₆`**: `CantorBoundary ≃ cantorTypedInverseDiagram.sections ≃ limit cantorTypedInverseDiagram`
   and compatibility with `uhfDiagonalTypedInductiveDiagram ℂ` (`diagEmbedSucc`, `cylinder_compatible_succ`). -/
theorem tc7_typed_category_inductive_colimit_inverse_limit_master_synthesis
    {I : Type u} [Preorder I] [IsFiltered I]
    (A : I → Type u)
    (ι : ∀ {i j : I}, i ≤ j → A i → A j)
    (hι_id : ∀ (i : I) (x : A i), ι (le_refl i) x = x)
    (hι_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
      ι hjk (ι hij x) = ι (le_trans hij hjk) x)
    (B : I → Type u)
    (π : ∀ {i j : I}, i ≤ j → B j → B i)
    (hπ_id : ∀ (i : I) (x : B i), π (le_refl i) x = x)
    (hπ_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : B k),
      π hij (π hjk x) = π (le_trans hij hjk) x)
    (i : I) (xi : A i) (u : CompatibleProjectiveThreads B π)
    {X : Type u}
    (f_out : colimit (typedInductiveDiagram A ι hι_id hι_comp) ⟶ X)
    (g_in : X ⟶ limit (typedInverseDiagram B π hπ_id hπ_comp))
    {J₀ : Type u} [SmallCategory J₀] [FinCategory J₀]
    {K₀ : Type u} [SmallCategory K₀] [IsFiltered K₀]
    (F_bif : J₀ × K₀ ⥤ Type u)
    (G_bif : J₀ ⥤ K₀ ⥤ Type u)
    (x_cantor : CantorBoundary) (n : ℕ) (f_diag : DiagAlg n) :
    let F_ind := typedInductiveDiagram A ι hι_id hι_comp
    let F_inv := typedInverseDiagram B π hπ_id hπ_comp
    let E_inv := typedInverseLimitEquivCompatibleThreads B π hπ_id hπ_comp
    (∀ st : TypedCategoryLimitColimitStage,
      ¬ Relation.TransGen TypedCategoryLimitColimitStage.causalEdge st st) ∧
    colimitEquivColimitType F_ind (colimit.ι F_ind i xi) = F_ind.ιColimitType i xi ∧
    ((∀ {a b : I} (f : a ⟶ b), Function.Injective (F_ind.map f)) →
      Function.Injective (colimit.ι F_ind i)) ∧
    E_inv (E_inv.symm u) = u ∧
    limit.π F_inv (Opposite.op i) (E_inv.symm u) = u.val i ∧
    (isColimitHomEquivYonedaSections (colimit.isColimit F_ind) X).symm
      (isColimitHomEquivYonedaSections (colimit.isColimit F_ind) X f_out) = f_out ∧
    (isLimitHomEquivCoyonedaSections (limit.isLimit F_inv) X).symm
      (isLimitHomEquivCoyonedaSections (limit.isLimit F_inv) X g_in) = g_in ∧
    Function.Injective (colimitLimitToLimitColimit F_bif) ∧
    Function.Surjective (colimitLimitToLimitColimit F_bif) ∧
    (colimitLimitIso G_bif).hom ≫ (colimitLimitIso G_bif).inv = 𝟙 _ ∧
    limit.π cantorTypedInverseDiagram (Opposite.op n)
      (cantorBoundaryEquivTypedInverseLimit x_cantor) = boundaryPrefix n x_cantor ∧
    cylinder (n + 1) (diagEmbedSucc n f_diag) = cylinder n f_diag := by
  intro F_ind F_inv E_inv
  have htc3 := tc3_typed_inverse_limit_sections_universal_and_thread_equivalence
    B π hπ_id hπ_comp (E_inv.symm u) u (le_refl i)
  have htc6 := tc6_cantor_typed_inverse_limit_sections_and_uhf_cylinder_colimit
    x_cantor (cantorBoundaryEquivTypedInverseSections x_cantor) n f_diag
  exact ⟨TypedCategoryLimitColimitStage.causalEdge_acyclic,
         colimitEquivColimitType_apply F_ind i xi,
         fun h_inj => typedFilteredColimitStageInjective F_ind h_inj i,
         htc3.2.2.1,
         htc3.2.2.2.1,
         (isColimitHomEquivYonedaSections (colimit.isColimit F_ind) X).symm_apply_apply f_out,
         (isLimitHomEquivCoyonedaSections (limit.isLimit F_inv) X).symm_apply_apply g_in,
         colimitLimitToLimitColimit_injective F_bif,
         colimitLimitToLimitColimit_surjective F_bif,
         (colimitLimitIso G_bif).hom_inv_id,
         htc6.2.2.2.1,
         htc6.2.2.2.2.2⟩

end InfoGeometry.Canonical.TypedCategoryInductiveColimitInverseLimitPoset
