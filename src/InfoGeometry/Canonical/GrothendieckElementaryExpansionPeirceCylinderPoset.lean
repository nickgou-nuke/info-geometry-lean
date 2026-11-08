/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Tactic.NoncommRing
import OAI.CategoryTheory.Globular.Main
import HomotopyHypothesis.Blueprint.Main
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-!
# Grothendieck's Homotopy Hypothesis, Elementary Expansion & Peirce Cylinder Poset (`𝔊ℌ₁`–`𝔊ℌ₇`)

## i. Overview
Formalizes Grothendieck globular boundary and elementary-expansion results alongside a finite
Peirce–Bruhat cylinder calculation. The `𝔊ℌ₇` theorem packages these conclusions together, but
does not define a map between the globular-model and operator-ring carriers. Its topological
realization input `C_top` is also independent of the coherator `C` used for the pushout.

## ii. Key results
- `grothendieck_globular_boundary_parallelism_and_hemisphere_equator` (`𝔊ℌ₁`)
- `pushout_retraction_injectivity_vs_surjectivity_gap` (`𝔊ℌ₂`)
- `exact_boundary_test_endpoint_section_and_retract_closure` (`𝔊ℌ₃`)
- `coskeletal_cutoff_low_square_and_tree_backtracking` (`𝔊ℌ₄`)
- `grothendieck_elementary_expansion_and_homotopy_group_iso` (`𝔊ℌ₅`)
- `grothendieck_coherator_topological_localization` (`𝔊ℌ₆`)
- `peirce_bruhat_cylinder_elementary_expansion_master_synthesis` (`𝔊ℌ₇`)

## iii. Table of contents
- Nodes `𝔊ℌ₁`–`𝔊ℌ₂`: Globular boundary parallelism, hemisphere equator, and retraction gap
- Nodes `𝔊ℌ₃`–`𝔊ℌ₄`: Exact Boundary Test closure and coskeletal cutoff low square
- Nodes `𝔊ℌ₅`–`𝔊ℌ₇`: Elementary expansion, coherator localization, and Peirce cylinder synthesis

## iv. References
- Alexander Grothendieck, *Pursuing Stacks* (1983)
- Georges Maltsiniotis, *Grothendieck ω-Groupoids* (2010)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `grothendieck_globular_boundary_parallelism_and_hemisphere_equator` (`𝔊ℌ₁`)
- `pushout_retraction_injectivity_vs_surjectivity_gap` (`𝔊ℌ₂`)
- `exact_boundary_test_endpoint_section_and_retract_closure` (`𝔊ℌ₃`)
- `coskeletal_cutoff_low_square_and_tree_backtracking` (`𝔊ℌ₄`)
- `grothendieck_elementary_expansion_and_homotopy_group_iso` (`𝔊ℌ₅`)
- `grothendieck_coherator_topological_localization` (`𝔊ℌ₆`)
- `peirce_bruhat_cylinder_elementary_expansion_master_synthesis` (`𝔊ℌ₇`)

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `grothendieck_elementary_expansion_and_homotopy_group_iso` (conditional on `hC : C.IsCoherator`,
  `hX : X.IsCellular`, and `square : CategoryTheory.IsPushout a (Model.J C n) i b`)
- `grothendieck_coherator_topological_localization` (conditional on `hC : C.IsCoherator`)
- `peirce_bruhat_cylinder_elementary_expansion_master_synthesis` (conditional on `hP : P * P = P`,
  `hC : C.IsCoherator`, `hX : X.IsCellular`, `square`, and `hC_top : C_top.IsCoherator`)

#### BUCKET 3: OPEN CLOSURE DEBT
- A typed interpretation map and compatibility theorem connecting the elementary-expansion
  morphism to the Peirce–Bruhat operator calculation are not established.
- The theorem's `C_top` realization input is not related to its `C` coherator by a map or
  compatibility hypothesis.
- Higher-categorical comparison between Grothendieck coherators and non-globular `(∞,1)`-models
  (quasi-categories, complete Segal spaces) remains external mathematical context beyond the
  globular coherator localization proved in `HomotopyHypothesis.Blueprint.main`.
-/

namespace InfoGeometry.Canonical.GrothendieckElementaryExpansionPeirceCylinderPoset

universe u v

open CategoryTheory
open InfoGeometry.OperatorAlgebra.PeirceSpine

/--
**Theorem 1 (`𝔊ℌ₁` — `grothendieck_globular_boundary_parallelism_and_hemisphere_equator`):**
In any globular set `X : OAI.Grothendieck.GlobularSet`:
1. The source and target `(n + 1)`-cells of any `(n + 2)`-cell `x` share the same outer `n`-boundary
   (`X.source_source` and `X.target_source`),
2. Any sequentially composable pair `f, g : X.Cell (n + 2)` (`X.target (n + 1) f = X.source (n + 1) g`)
   has parallel outer `n`-cell boundaries,
3. In Ara's topological globes (`HomotopyHypothesis.faceVec`), for `d1 < d2` and `‖v‖ ≤ 1`,
   the hemisphere face embedding lands on the unit sphere (`‖faceVec d1 d2 side v‖ ^ 2 = 1`) and
   any iterated face collapses to the equator (`faceVec d2 d3 side' (faceVec d1 d2 side v) = faceVec d1 d3 side v`).
-/
theorem grothendieck_globular_boundary_parallelism_and_hemisphere_equator
    (X : OAI.Grothendieck.GlobularSet.{u}) (n : ℕ)
    (x f g : X.Cell (n + 2))
    (h_seq : X.target (n + 1) f = X.source (n + 1) g)
    {d1 d2 d3 : ℕ} (h12 : d1 < d2) (side side' : Bool)
    (v : EuclideanSpace ℝ (Fin d1)) (hv : ‖v‖ ≤ 1) :
    (X.source n (X.source (n + 1) x) = X.source n (X.target (n + 1) x) ∧
     X.target n (X.source (n + 1) x) = X.target n (X.target (n + 1) x)) ∧
    (X.source n (X.source (n + 1) f) = X.source n (X.target (n + 1) g) ∧
     X.target n (X.source (n + 1) f) = X.target n (X.target (n + 1) g)) ∧
    ‖HomotopyHypothesis.faceVec d1 d2 side v‖ ^ 2 = 1 ∧
    HomotopyHypothesis.faceVec d2 d3 side' (HomotopyHypothesis.faceVec d1 d2 side v) =
      HomotopyHypothesis.faceVec d1 d3 side v := by
  have h_glob_x :
      X.source n (X.source (n + 1) x) = X.source n (X.target (n + 1) x) ∧
      X.target n (X.source (n + 1) x) = X.target n (X.target (n + 1) x) :=
    ⟨X.source_source n x, X.target_source n x⟩
  have h_seq_s : X.source n (X.source (n + 1) f) = X.source n (X.target (n + 1) g) := by
    rw [X.source_source n f, h_seq, ← X.source_source n g]
  have h_seq_t : X.target n (X.source (n + 1) f) = X.target n (X.target (n + 1) g) := by
    rw [X.target_source n f, h_seq, ← X.target_source n g]
  have h_norm : ‖HomotopyHypothesis.faceVec d1 d2 side v‖ ^ 2 = 1 :=
    HomotopyHypothesis.norm_sq_faceVec h12 side v hv
  have h_eq :
      HomotopyHypothesis.faceVec d2 d3 side' (HomotopyHypothesis.faceVec d1 d2 side v) =
        HomotopyHypothesis.faceVec d1 d3 side v :=
    HomotopyHypothesis.faceVec_faceVec h12 side side' v hv
  exact ⟨h_glob_x, ⟨h_seq_s, h_seq_t⟩, h_norm, h_eq⟩

/--
**Theorem 2 (`𝔊ℌ₂` — `pushout_retraction_injectivity_vs_surjectivity_gap`):**
1. **Injectivity from One-Way Retraction:** If `i : X → Y` admits a retraction `r : Y → X`
   (`∀ x, r (i x) = x`) preserving joining (`J_Y y₁ y₂ → J_X (r y₁) (r y₂)`), then `i` reflects
   joining (`J_Y (i x₁) (i x₂) → J_X x₁ x₂`), so no existing homotopy classes collapse.
2. **Surjectivity Obstruction Without Cylinders:** The inclusion `fun _ : Unit => false` has a
   left inverse `fun _ : Bool => ()`, yet fails to reach `true : Bool`.
-/
theorem pushout_retraction_injectivity_vs_surjectivity_gap
    {X Y : Type*}
    (i : X → Y) (r : Y → X) (h_ret : ∀ x : X, r (i x) = x)
    (J_X : X → X → Prop) (J_Y : Y → Y → Prop)
    (hr_map : ∀ y₁ y₂ : Y, J_Y y₁ y₂ → J_X (r y₁) (r y₂)) :
    (∀ x₁ x₂ : X, J_Y (i x₁) (i x₂) → J_X x₁ x₂) ∧
    ((∀ u : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) u) = u) ∧
     ¬ ∃ u : Unit, (fun _ : Unit => false) u = true) := by
  refine ⟨?_, ⟨fun _ => rfl, fun ⟨_, hu⟩ => Bool.noConfusion hu⟩⟩
  intro (x₁ : X) (x₂ : X) (hJ : J_Y (i x₁) (i x₂))
  have h : J_X (r (i x₁)) (r (i x₂)) := hr_map (i x₁) (i x₂) hJ
  rw [h_ret x₁, h_ret x₂] at h
  exact h

/--
**Theorem 3 (`𝔊ℌ₃` — `exact_boundary_test_endpoint_section_and_retract_closure`):**
Formalizes the three globular homotopy-lifting engines (Proposition 2.4 Exact Boundary Test,
Proposition 4.3 Cylinder Endpoint Section, and Retract Closure):
1. Next-dimension boundary filling reflects `J_Y`-joining on parallel cells,
2. A boundary-preserving section `h : Y → P` of cylinder endpoint `p₀` transfers `p₁`-boundary
   lifting into the Exact Boundary Test for `y ↦ p₁ (h y)`,
3. If `y ↦ u (r y)` reflects `J_Y` on parallel cells, the retracted map `i : X → Y` satisfies
   the Exact Boundary Test.
-/
theorem exact_boundary_test_endpoint_section_and_retract_closure
    {B X X₁ P Y : Type*}
    (bdX : X → B) (sX tX : X₁ → X) (f : X → Y) (J_Y : Y → Y → Prop)
    (h_fill_next : ∀ x₁ x₂ : X, bdX x₁ = bdX x₂ → J_Y (f x₁) (f x₂) → ∃ w : X₁, sX w = x₁ ∧ tX w = x₂)
    (bdP : P → B) (bdY : Y → B) (p₀ p₁ : P → Y) (h : Y → P) (J_P : P → P → Prop)
    (hp₀_bd : ∀ z : P, bdY (p₀ z) = bdP z)
    (hh_bd : ∀ y : Y, bdP (h y) = bdY y)
    (hh_sec : ∀ y : Y, p₀ (h y) = y)
    (hp₁_lift : ∀ (b : B) (y : Y), bdY y = b → ∃ z : P, bdP z = b ∧ p₁ z = y)
    (hp₀_join : ∀ z₁ z₂ : P, bdP z₁ = bdP z₂ → J_Y (p₀ z₁) (p₀ z₂) → J_P z₁ z₂)
    (hp₁_map : ∀ z₁ z₂ : P, J_P z₁ z₂ → J_Y (p₁ z₁) (p₁ z₂))
    (hJ_refl : ∀ y : Y, J_Y y y)
    (i : X → Y) (r : Y → X) (u : X → Y)
    (hir : ∀ x : X, r (i x) = x)
    (hi_bd : ∀ x : X, bdY (i x) = bdX x)
    (hr_bd : ∀ y : Y, bdX (r y) = bdY y)
    (hur_reflect : ∀ y₁ y₂ : Y, bdY y₁ = bdY y₂ → J_Y (u (r y₁)) (u (r y₂)) → J_Y y₁ y₂) :
    (∀ x₁ x₂ : X, bdX x₁ = bdX x₂ → J_Y (f x₁) (f x₂) → ∃ w : X₁, sX w = x₁ ∧ tX w = x₂) ∧
    (∀ (b : B) (y : Y), bdY y = b → ∃ x : Y, bdY x = b ∧ J_Y (p₁ (h x)) y) ∧
    (∀ (b : B) (y : Y), bdY y = b → ∃ x : X, bdX x = b ∧ J_Y (i x) y) := by
  have h_refl_fill : ∀ x₁ x₂ : X, bdX x₁ = bdX x₂ → J_Y (f x₁) (f x₂) → ∃ w : X₁, sX w = x₁ ∧ tX w = x₂ :=
    h_fill_next
  refine ⟨h_refl_fill, ?_, ?_⟩
  · intro (b : B) (y : Y) hy
    obtain ⟨z, hz_bd, hz_p₁⟩ := hp₁_lift b y hy
    let x : Y := p₀ z
    have hx_bd : bdY x = b := (hp₀_bd z).trans hz_bd
    have h_par : bdP (h x) = bdP z := (hh_bd x).trans (hx_bd.trans hz_bd.symm)
    have h_p₀_join : J_Y (p₀ (h x)) (p₀ z) := by
      rw [hh_sec x]
      exact hJ_refl x
    have h_JP : J_P (h x) z := hp₀_join (h x) z h_par h_p₀_join
    have h_JY : J_Y (p₁ (h x)) y := by
      rw [← hz_p₁]
      exact hp₁_map (h x) z h_JP
    exact ⟨x, hx_bd, h_JY⟩
  · intro (b : B) (y : Y) hy
    let x : X := r y
    have hx_bd : bdX x = b := (hr_bd y).trans hy
    have h_par : bdY (i x) = bdY y := (hi_bd x).trans (hx_bd.trans hy.symm)
    have h_ur : J_Y (u (r (i x))) (u (r y)) := by
      rw [hir x]
      exact hJ_refl (u x)
    exact ⟨x, hx_bd, hur_reflect (i x) y h_par h_ur⟩

/--
**Theorem 4 (`𝔊ℌ₄` — `coskeletal_cutoff_low_square_and_tree_backtracking`):**
1. Coskeletal ceiling `q = max (n + 1) (d + 1)` dominates `n`, `d`, and `d + 1`,
2. `OAI.Grothendieck.GlobularSet.exactBoundaryTest_at_of_low_square` transfers the Exact Boundary
   Test at dimension `d` across any commutative cutoff square `i.comp b = a.comp j` whose vertical
   cutoff units are bijective up to `d` and surjective at `d + 1`,
3. Tree-to-string walk backtracking `g₁ * (g₂ * g₂⁻¹) * g₃ = g₁ * g₃` in any group `G`.
-/
theorem coskeletal_cutoff_low_square_and_tree_backtracking
    {X Y R S : OAI.Grothendieck.GlobularSet.{v}}
    (i : X.Hom Y) (j : R.Hom S) (a : X.Hom R) (b : Y.Hom S)
    (sq : i.comp b = a.comp j) (hj : OAI.Grothendieck.GlobularSet.ExactBoundaryTest j)
    (n d : ℕ)
    (ha : ∀ k, k ≤ d → Function.Bijective (a.app k))
    (hb : Function.Injective (b.app d)) (hb₁ : Function.Surjective (b.app (d + 1)))
    (bd : X.Boundary d) (y : Y.Cell d) (hy : Y.boundary d y = i.boundaryMap d bd)
    {G : Type*} [Group G] (g₁ g₂ g₃ : G) :
    (n ≤ max (n + 1) (d + 1) ∧ d ≤ max (n + 1) (d + 1) ∧ d + 1 ≤ max (n + 1) (d + 1)) ∧
    (∃ x : X.Cell d, X.boundary d x = bd ∧ Y.Joined d (i.app d x) y) ∧
    (g₁ * (g₂ * g₂⁻¹) * g₃ = g₁ * g₃) := by
  have h_ceil : n ≤ max (n + 1) (d + 1) ∧ d ≤ max (n + 1) (d + 1) ∧ d + 1 ≤ max (n + 1) (d + 1) :=
    ⟨Nat.le_trans (Nat.le_succ n) (Nat.le_max_left (n + 1) (d + 1)),
     Nat.le_trans (Nat.le_succ d) (Nat.le_max_right (n + 1) (d + 1)),
     Nat.le_max_right (n + 1) (d + 1)⟩
  have h_low : ∃ x : X.Cell d, X.boundary d x = bd ∧ Y.Joined d (i.app d x) y :=
    OAI.Grothendieck.GlobularSet.exactBoundaryTest_at_of_low_square i j a b sq hj d ha hb hb₁ bd y hy
  have h_tree : g₁ * (g₂ * g₂⁻¹) * g₃ = g₁ * g₃ := by group
  exact ⟨h_ceil, h_low, h_tree⟩

/--
**Theorem 5 (`𝔊ℌ₅` — `grothendieck_elementary_expansion_and_homotopy_group_iso`):**
For any coherator `C`, cellular `C`-model `X`, and pushout square `square` attaching `(n + 1)`-disk
`disk C (n + 1)` along `Model.J C n : disk C n ⟶ disk C (n + 1)` via `i : X ⟶ Y`:
1. `i` is a weak equivalence of `∞`-groupoids (`Model.WeakEquivalence hC i`),
2. The elementary pushout retraction `r : Y ⟶ X` (`i ≫ r = 𝟙 X`) induces a two-sided inverse
   `componentsMap r` to `componentsMap i` on `π₀`,
3. `homotopyMap i hC x m` is bijective on `π_{m+1}` at every basepoint `x` and dimension `m`,
4. `homotopyGroupIsoOfWeakEquivalence` induces a group isomorphism `X.HomotopyGroup hC x m ≃* Y.HomotopyGroup hC ((underlyingMap i).app 0 x) m`.
-/
theorem grothendieck_elementary_expansion_and_homotopy_group_iso
    (C : OAI.Grothendieck.GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : OAI.Grothendieck.GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : OAI.Grothendieck.GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : CategoryTheory.IsPushout a (OAI.Grothendieck.GlobularTheory.Model.J C n) i b) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i ∧
    (∃ r : Y ⟶ X, i ≫ r = 𝟙 X ∧
      Function.LeftInverse (OAI.Grothendieck.GlobularTheory.Model.componentsMap r)
        (OAI.Grothendieck.GlobularTheory.Model.componentsMap i) ∧
      Function.RightInverse (OAI.Grothendieck.GlobularTheory.Model.componentsMap r)
        (OAI.Grothendieck.GlobularTheory.Model.componentsMap i)) ∧
    Function.Bijective (OAI.Grothendieck.GlobularTheory.Model.componentsMap i) ∧
    (∀ (x : X.underlying.Cell 0) (m : ℕ),
      Function.Bijective (OAI.Grothendieck.GlobularTheory.Model.homotopyMap i hC x m)) ∧
    (∀ (x : X.underlying.Cell 0) (m : ℕ),
      Nonempty (X.HomotopyGroup hC x m ≃*
        Y.HomotopyGroup hC ((OAI.Grothendieck.GlobularTheory.Model.underlyingMap i).app 0 x) m)) := by
  have hWE : OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i :=
    OAI.Grothendieck.elementary_expansion C hC X hX n a Y i b square
  obtain ⟨r, hr⟩ :=
    OAI.Grothendieck.GlobularTheory.Model.elementary_pushout_retraction hC n a i b square
  have h_left :
      Function.LeftInverse (OAI.Grothendieck.GlobularTheory.Model.componentsMap r)
        (OAI.Grothendieck.GlobularTheory.Model.componentsMap i) := by
    intro c
    induction c using Quot.inductionOn with
    | h x₀ =>
      have h_app :
          (OAI.Grothendieck.GlobularTheory.Model.underlyingMap r).app 0
            ((OAI.Grothendieck.GlobularTheory.Model.underlyingMap i).app 0 x₀) = x₀ :=
        congrFun (congrArg (fun f => (OAI.Grothendieck.GlobularTheory.Model.underlyingMap f).app 0) hr) x₀
      exact congrArg (Quot.mk (X.underlying.Joined 0)) h_app
  have h_right :
      Function.RightInverse (OAI.Grothendieck.GlobularTheory.Model.componentsMap r)
        (OAI.Grothendieck.GlobularTheory.Model.componentsMap i) := by
    intro d
    obtain ⟨c, rfl⟩ := hWE.1.surjective d
    rw [h_left c]
  refine ⟨hWE, ⟨r, hr, h_left, h_right⟩, hWE.1, hWE.2, fun x m =>
    ⟨OAI.Grothendieck.GlobularTheory.Model.homotopyGroupIsoOfWeakEquivalence i hC hWE x m⟩⟩

/--
**Theorem 6 (`𝔊ℌ₆` — `grothendieck_coherator_topological_localization`):**
Grothendieck's Homotopy Hypothesis for coherators (`HomotopyHypothesis.Blueprint.main`):
For every coherator `C`, a topological realization `TopRealization C` exists, and for every
realization `R` and every weak homotopy equivalence `f : K ⟶ L` in `TopCat.{u}`, the fundamental
`∞`-groupoid functor `fundamentalGroupoidFunctor R` sends `f` to a model weak equivalence whose
localized image is an isomorphism in `Ho(∞-Gpd_C)`.
-/
theorem grothendieck_coherator_topological_localization
    (C : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}) (hC : C.IsCoherator)
    (R : HomotopyHypothesis.TopRealization C)
    {K L : TopCat.{u}} (f : K ⟶ L)
    (hf : HomotopyHypothesis.weakHomotopyEquivalences f) :
    Nonempty (HomotopyHypothesis.TopRealization C) ∧
    HomotopyHypothesis.modelWeakEquivalences hC
      ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f) ∧
    (Function.Injective
       (HomotopyHypothesis.Grothendieck.GlobularTheory.Model.componentsMap
         ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f)) ∧
     Function.Surjective
       (HomotopyHypothesis.Grothendieck.GlobularTheory.Model.componentsMap
         ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f))) ∧
    IsIso (((HomotopyHypothesis.modelWeakEquivalences hC).Q).map
      ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f)) ∧
    (HomotopyHypothesis.fundamentalGroupoidFunctor R ⋙
        (HomotopyHypothesis.modelWeakEquivalences hC).Q).IsLocalization
      HomotopyHypothesis.weakHomotopyEquivalences := by
  have h_main := HomotopyHypothesis.Blueprint.main C hC
  have h_R := h_main.2 R
  have h_wf :
      HomotopyHypothesis.modelWeakEquivalences hC
        ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f) :=
    h_R.1 f hf
  rcases h_wf.1 with ⟨h_inj, h_surj⟩
  have h_iso :
      IsIso (((HomotopyHypothesis.modelWeakEquivalences hC).Q).map
        ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f)) :=
    Localization.inverts (HomotopyHypothesis.modelWeakEquivalences hC).Q
      (HomotopyHypothesis.modelWeakEquivalences hC)
      ((HomotopyHypothesis.fundamentalGroupoidFunctor R).map f) h_wf
  exact ⟨h_main.1, h_wf, ⟨h_inj, h_surj⟩, h_iso, h_R.2⟩

/--
**Theorem 7 (`𝔊ℌ₇` — `peirce_bruhat_cylinder_elementary_expansion_master_synthesis`):**
Jointly returns:
1. Grothendieck's elementary expansion weak equivalence (`OAI.Grothendieck.elementary_expansion`),
2. Existence of a topological realization for the separately supplied coherator `C_top`,
3. The non-commutative Peirce–Bruhat unipotent cylinder rotor `(1 + conePlus P A) * (1 - coneMinus P C)`
   and its exact division-calculus inverse `(1 + coneMinus P C) * (1 - conePlus P A)`, transporting
   the bare projectors `P` and `1 - P` to `dressedPeirceProjector P (-A) (-C)` and
   `1 - dressedPeirceProjector P (-A) (-C)` and retracting them back to `P` and `1 - P`, together
   with the Peirce grading twist `invS P * genPhi P A A = OperatorAlgebra.PeirceSpine.comm P A`.
These are conclusions in separate carriers under separate inputs: the theorem supplies neither a
map from the elementary-expansion morphism to the operator ring nor a map relating `C` and `C_top`.
-/
theorem peirce_bruhat_cylinder_elementary_expansion_master_synthesis
    {B : Type*} [Ring B] (P A C_op : B) (hP : P * P = P)
    (C : OAI.Grothendieck.GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : OAI.Grothendieck.GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : OAI.Grothendieck.GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : CategoryTheory.IsPushout a (OAI.Grothendieck.GlobularTheory.Model.J C n) i b)
    (C_top : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}) (hC_top : C_top.IsCoherator) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i ∧
    Nonempty (HomotopyHypothesis.TopRealization C_top) ∧
    (((1 + conePlus P A) * (1 - coneMinus P C_op)) *
       ((1 + coneMinus P C_op) * (1 - conePlus P A)) = 1 ∧
     ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
       ((1 + conePlus P A) * (1 - coneMinus P C_op)) = 1) ∧
    (((1 + conePlus P A) * (1 - coneMinus P C_op)) * P *
       ((1 + coneMinus P C_op) * (1 - conePlus P A)) =
       dressedPeirceProjector P (-A) (-C_op) ∧
     ((1 + conePlus P A) * (1 - coneMinus P C_op)) * (1 - P) *
       ((1 + coneMinus P C_op) * (1 - conePlus P A)) =
       1 - dressedPeirceProjector P (-A) (-C_op)) ∧
    (((1 + coneMinus P C_op) * (1 - conePlus P A)) *
       dressedPeirceProjector P (-A) (-C_op) *
       ((1 + conePlus P A) * (1 - coneMinus P C_op)) = P ∧
     ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
       (1 - dressedPeirceProjector P (-A) (-C_op)) *
       ((1 + conePlus P A) * (1 - coneMinus P C_op)) = 1 - P) ∧
    invS P * genPhi P A A = OperatorAlgebra.PeirceSpine.comm P A := by
  have hWE : OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC i :=
    OAI.Grothendieck.elementary_expansion C hC X hX n a Y i b square
  have hTop : Nonempty (HomotopyHypothesis.TopRealization C_top) :=
    (HomotopyHypothesis.Blueprint.main C_top hC_top).1
  have hG1 : ((1 + conePlus P A) * (1 - coneMinus P C_op)) *
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) = 1 := by
    peirce_nf hP
  have hG2 : ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
      ((1 + conePlus P A) * (1 - coneMinus P C_op)) = 1 := by
    peirce_nf hP
  have hFwdP : ((1 + conePlus P A) * (1 - coneMinus P C_op)) * P *
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) =
      dressedPeirceProjector P (-A) (-C_op) := by
    unfold dressedPeirceProjector
    peirce_nf hP
  have hFwdW : ((1 + conePlus P A) * (1 - coneMinus P C_op)) * (1 - P) *
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) =
      1 - dressedPeirceProjector P (-A) (-C_op) := by
    unfold dressedPeirceProjector
    peirce_nf hP
  have hRevP :
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
        dressedPeirceProjector P (-A) (-C_op) *
        ((1 + conePlus P A) * (1 - coneMinus P C_op)) = P := by
    rw [← hFwdP]
    calc
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
          (((1 + conePlus P A) * (1 - coneMinus P C_op)) * P *
            ((1 + coneMinus P C_op) * (1 - conePlus P A))) *
          ((1 + conePlus P A) * (1 - coneMinus P C_op))
        = (((1 + coneMinus P C_op) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P C_op))) * P *
          (((1 + coneMinus P C_op) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P C_op))) := by simp only [mul_assoc]
      _ = 1 * P * 1 := by rw [hG2]
      _ = P := by simp only [one_mul, mul_one]
  have hRevW :
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
        (1 - dressedPeirceProjector P (-A) (-C_op)) *
        ((1 + conePlus P A) * (1 - coneMinus P C_op)) = 1 - P := by
    rw [← hFwdW]
    calc
      ((1 + coneMinus P C_op) * (1 - conePlus P A)) *
          (((1 + conePlus P A) * (1 - coneMinus P C_op)) * (1 - P) *
            ((1 + coneMinus P C_op) * (1 - conePlus P A))) *
          ((1 + conePlus P A) * (1 - coneMinus P C_op))
        = (((1 + coneMinus P C_op) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P C_op))) * (1 - P) *
          (((1 + coneMinus P C_op) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P C_op))) := by simp only [mul_assoc]
      _ = 1 * (1 - P) * 1 := by rw [hG2]
      _ = 1 - P := by simp only [one_mul, mul_one]
  have h_comm : OperatorAlgebra.PeirceSpine.comm P A = genJ P A A := by
    dsimp [OperatorAlgebra.PeirceSpine.comm, genJ, conePlus, coneMinus]
    noncomm_ring
  have h_twist_J : invS P * genPhi P A A = genJ P A A := by
    peirce_nf hP
  have h_twist : invS P * genPhi P A A = OperatorAlgebra.PeirceSpine.comm P A :=
    h_twist_J.trans h_comm.symm
  exact ⟨hWE, hTop, ⟨hG1, hG2⟩, ⟨hFwdP, hFwdW⟩, ⟨hRevP, hRevW⟩, h_twist⟩

end InfoGeometry.Canonical.GrothendieckElementaryExpansionPeirceCylinderPoset
