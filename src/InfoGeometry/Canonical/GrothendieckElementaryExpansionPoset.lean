/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import OAI.CategoryTheory.Globular.Main
import HomotopyHypothesis.Blueprint.Main
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Grothendieck Elementary Expansion & Coherator Homotopy Hypothesis Poset (`𝔊ℌ₁`–`𝔊ℌ₇`)

## i. Overview
Formalizes the Grothendieck elementary expansion and coherator localization results
(`𝔊ℌ₁`–`𝔊ℌ₆`) and records separate finite Peirce–Bruhat operator results in `𝔊ℌ₇`.
The dimensionwise linearization below sends globular model maps to free abelian cell-module
endomorphisms and sends an elementary pushout retraction to a split idempotent there. The
existing Peirce corner laws then apply in that concrete endomorphism ring. This still does not
identify that carrier with an independently supplied operator algebra or transport homotopy
invariants through such an identification.

## ii. Key results
- `globular_composable_three_chain_outer_parallel`, `gh1_globular_outer_parallel_and_coherator_equivalence` (`𝔊ℌ₁`)
- `eckmann_hilton_strict_commutativity`, `componentsMap_id_apply`, `componentsMap_comp_apply`, `gh2_elementary_pushout_retraction_and_components_injective` (`𝔊ℌ₂`)
- `exactBoundaryTest_id`, `exactBoundaryTest_comp`, `gh3_exact_boundary_test_endpoint_section_and_retract_factor` (`𝔊ℌ₃`)
- `ara_two_out_of_three_dimensionwise_bijective`, `elementary_expansion_exactBoundaryTest`, `gh4_coskeletal_cutoff_low_square_and_elementary_test` (`𝔊ℌ₄`)
- `gh5_grothendieck_elementary_expansion_and_homotopy_group_iso` (`𝔊ℌ₅`)
- `gh6_grothendieck_ara_maltsiniotis_coherator_localization` (`𝔊ℌ₆`)
- `gh7_grothendieck_elementary_expansion_peirce_bruhat_master_synthesis` (`𝔊ℌ₇`)
- `linearizedModelMap_comp`, `linearizedModelMap_id`,
  `elementary_retraction_linearizes_to_idempotent`,
  `elementary_pushout_linearized_idempotent`,
  `elementary_pushout_induces_Peirce_corner_nilpotence`

## iii. Table of contents
- Rungs `𝔊ℌ₁`–`𝔊ℌ₂`: Globular outer parallelism, coherator equivalence, and pushout retraction on `π₀`
- Rungs `𝔊ℌ₃`–`𝔊ℌ₄`: Exact Boundary Test composition closure and coskeletal cutoff low squares
- Rungs `𝔊ℌ₅`–`𝔊ℌ₇`: Iterated elementary expansion, coherator localization, and Peirce–Bruhat cylinder transport

## iv. References
- Alexander Grothendieck, *Pursuing Stacks* (1983)
- Dimitri Ara, *On the Homotopy Theory of Grothendieck ω-Groupoids* (2013)

#### BUCKET 1: CLOSED FINITE THEOREMS
- `globular_composable_three_chain_outer_parallel`:
  Outer boundary parallelism and boundary equality across any composable 3-chain of `(n + 1)`-cells.
- `gh1_globular_outer_parallel_and_coherator_equivalence` (`𝔊ℌ₁`):
  Composable 3-chain outer boundary equality, coherator unit/inverse cell boundary equations,
  explicit inverse-cell witness for symmetry of `Joined`, and equivalence of `Joined`.
- `componentsMap_id_apply` and `componentsMap_comp_apply`:
  Functoriality of `Model.componentsMap` on `π₀` under identity and composition of model morphisms.
- `gh2_elementary_pushout_retraction_and_components_injective` (`𝔊ℌ₂`):
  Horn unit retraction `J C n ≫ unitMap C hC n = 𝟙 (disk C n)`, elementary pushout retraction
  `∃ r : Y ⟶ X, i ≫ r = 𝟙 X ∧ Function.LeftInverse (componentsMap r) (componentsMap i)`,
  resulting injectivity of `componentsMap i` and surjectivity of `componentsMap r`, and the
  concrete discrete surjectivity obstruction without cylinders.
- `exactBoundaryTest_id` and `exactBoundaryTest_comp`:
  Identity and composition closure of `GlobularSet.ExactBoundaryTest` on reflexive/transitive
  globular sets.
- `gh3_exact_boundary_test_endpoint_section_and_retract_factor` (`𝔊ℌ₃`):
  Identity and composition closure of `ExactBoundaryTest`, reflection of `Joined` on parallel cells,
  cylinder endpoint section theorem, and retract factorization transfer.
- `elementary_expansion_exactBoundaryTest`:
  Every elementary disk attachment `IsPushout a (Model.J C n) i b` on a cellular coherator model
  satisfies `GlobularSet.ExactBoundaryTest (Model.underlyingMap i)`.
- `gh4_coskeletal_cutoff_low_square_and_elementary_test` (`𝔊ℌ₄`):
  Coskeletal ceiling `q = max (n + 1) (d + 1)` bounds, low-dimension bijectivity of `cutoffUnit`,
  and exact boundary test transfer from the `q`-cutoff category to `Model.underlyingMap i`.
- `gh5_grothendieck_elementary_expansion_and_homotopy_group_iso` (`𝔊ℌ₅`):
  Single-stage and two-stage iterated elementary expansion weak equivalence (`Model.WeakEquivalence`),
  composition of exact boundary tests across `i ≫ i₂`, and induced multiplicative group isomorphisms
  on all higher homotopy groups.
- `gh6_grothendieck_ara_maltsiniotis_coherator_localization` (`𝔊ℌ₆`):
  Explicit instantiation of the Grothendieck–Ara–Maltsiniotis Homotopy Hypothesis on any coherator
  `C`, topological realization `R : OAIRealization C`, and weak homotopy equivalence `f : K ⟶ L`:
  `R.Pi.map f` is a model weak equivalence inducing bijections on `π₀`, group isomorphisms on all
  `π_{k+1}`, and an isomorphism in the localized homotopy category.
- [PROVED] `eckmann_hilton_strict_commutativity` (`𝔊ℌ₂`):
  Constructive Eckmann–Hilton collapse (`m₂ a b = m₁ a b ∧ m₁ a b = m₁ b a`) for two unital
  binary operations satisfying strict middle-four interchange.
- [PROVED] `ara_two_out_of_three_dimensionwise_bijective` (`𝔊ℌ₄`):
  Constructive 2-out-of-3 closure (`f`, `g`, `g ∘ f`) for `ℕ`-graded bijections on homotopy sets.
- `gh7_grothendieck_elementary_expansion_peirce_bruhat_master_synthesis` (`𝔊ℌ₇`):
  Returns the elementary-expansion weak equivalence and homotopy group isomorphism together with
  separate Peirce–Bruhat ring identities over `[Ring B]`. The new linearization maps model
  morphisms into free abelian cell-module endomorphisms and instantiates the generic upper/lower
  corner nilpotence laws in that ring; no map from those endomorphisms to a separately supplied
  `[Ring B]` or compatibility with Peirce conjugation is established.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- Hypotheses are theorem-specific, not shared uniformly across `gh1`–`gh7`. For example,
  `gh5` uses cellular-model and elementary-pushout hypotheses; `gh6` additionally takes a
  realization `R`, a weak-equivalence proof `hf`, a basepoint, and a homotopy-group dimension;
  `gh7` takes the elementary-pushout data and separate ring/idempotent inputs. See each theorem
  signature for its complete contract.

#### BUCKET 3: OPEN CLOSURE DEBT
- No proof-hole debt is recorded in this module. The categorical retraction is now represented
  as an idempotent on free abelian cell modules, but a map from that operator algebra into the
  existing Peirce carrier and compatibility with its conjugation calculus remain open; see
  [Cross-Lane Closure Sequence](../../../docs/CROSS_LANE_CLOSURE_SEQUENCE.md), Rank 1.
-/

namespace InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck
open OAI.Grothendieck.GlobularTheory

/-! ### Linearized retraction projectors

An elementary pushout retraction is categorical data between globular models.  The
following construction sends its maps, dimension by dimension, to linear maps on
the free abelian groups generated by cells.  It yields an actual idempotent in a
`Module.End` ring.  This is a typed operator realization of the retraction; it
does not identify the resulting endomorphism with the independent Peirce
conjugation operators below.
-/

/-- Dimension-by-dimension `ℤ`-linear map on finitely supported cell chains induced by a
globular model morphism `f : X ⟶ Y`. -/
noncomputable def linearizedModelMap {C : GlobularTheory.{v}}
    {X Y : C.Model} (f : X ⟶ Y) (n : ℕ) :
    (X.underlying.Cell n →₀ ℤ) →ₗ[ℤ] (Y.underlying.Cell n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ ((Model.underlyingMap f).app n)

/-- Linearization sends categorical composition to composition of linear maps. -/
theorem linearizedModelMap_comp {C : GlobularTheory.{v}}
    {X Y Z : C.Model} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    linearizedModelMap (f ≫ g) n =
      (linearizedModelMap g n).comp (linearizedModelMap f n) := by
  change Finsupp.lmapDomain ℤ ℤ
      (((Model.underlyingMap g).app n) ∘ ((Model.underlyingMap f).app n)) = _
  exact Finsupp.lmapDomain_comp ℤ ℤ _ _

/-- Linearization sends an identity model map to the identity linear map. -/
theorem linearizedModelMap_id {C : GlobularTheory.{v}}
    (X : C.Model) (n : ℕ) :
    linearizedModelMap (𝟙 X) n = LinearMap.id := by
  change Finsupp.lmapDomain ℤ ℤ id = LinearMap.id
  exact Finsupp.lmapDomain_id ℤ ℤ

/-- A categorical retraction induces a split idempotent on every free cell module. -/
theorem elementary_retraction_linearizes_to_idempotent
    {C : GlobularTheory.{v}} {X Y : C.Model}
    (i : X ⟶ Y) (r : Y ⟶ X) (hr : i ≫ r = 𝟙 X) (n : ℕ) :
    let p : Module.End ℤ (Y.underlying.Cell n →₀ ℤ) :=
      (linearizedModelMap i n).comp (linearizedModelMap r n)
    p.comp p = p := by
  dsimp
  have hri : (linearizedModelMap r n).comp (linearizedModelMap i n) = LinearMap.id := by
    rw [← linearizedModelMap_comp, hr, linearizedModelMap_id]
  change ((linearizedModelMap i n).comp (linearizedModelMap r n)).comp
      ((linearizedModelMap i n).comp (linearizedModelMap r n)) =
    (linearizedModelMap i n).comp (linearizedModelMap r n)
  apply LinearMap.ext
  intro x
  change (linearizedModelMap i n)
      ((linearizedModelMap r n) ((linearizedModelMap i n) ((linearizedModelMap r n) x))) =
    (linearizedModelMap i n) ((linearizedModelMap r n) x)
  have hinner : (linearizedModelMap r n) ((linearizedModelMap i n) ((linearizedModelMap r n) x)) =
      (linearizedModelMap r n) x := by
    have h := congrArg (fun f => f ((linearizedModelMap r n) x)) hri
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  rw [hinner]

/-- The retraction supplied by an elementary disk pushout yields a degreewise linearized
idempotent on the target model's free abelian cell module that fixes the image of the
base inclusion `linearizedModelMap i n`. -/
theorem elementary_pushout_linearized_idempotent
    {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : Model.disk C n ⟶ X) (i : X ⟶ Y)
    (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    ∃ p : Module.End ℤ (Y.underlying.Cell n →₀ ℤ),
      p.comp p = p ∧ p.comp (linearizedModelMap i n) = linearizedModelMap i n := by
  obtain ⟨r, hr⟩ := Model.elementary_pushout_retraction hC n a i b square
  refine ⟨(linearizedModelMap i n).comp (linearizedModelMap r n),
    elementary_retraction_linearizes_to_idempotent i r hr n, ?_⟩
  have hri : (linearizedModelMap r n).comp (linearizedModelMap i n) = LinearMap.id := by
    rw [← linearizedModelMap_comp, hr, linearizedModelMap_id]
  apply LinearMap.ext
  intro x
  change (linearizedModelMap i n) ((linearizedModelMap r n) ((linearizedModelMap i n) x)) =
    (linearizedModelMap i n) x
  have h := congrArg (fun f => f x) hri
  dsimp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  rw [h]

/-- The elementary-pushout projector realizes the existing Peirce upper and lower
square-zero corner laws inside the endomorphism ring of its target cell chains. -/
theorem elementary_pushout_induces_Peirce_corner_nilpotence
    {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : Model.disk C n ⟶ X) (i : X ⟶ Y)
    (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    ∃ p : Module.End ℤ (Y.underlying.Cell n →₀ ℤ),
      p.comp p = p ∧
      (∀ A A', InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus p A *
        InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus p A' = 0) ∧
      (∀ D D', InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus p D *
        InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus p D' = 0) := by
  obtain ⟨p, hp, _hfix⟩ := elementary_pushout_linearized_idempotent hC n a i b square
  have hpRing : p * p = p := by
    rw [Module.End.mul_eq_comp]
    exact hp
  refine ⟨p, hp, ?_, ?_⟩
  · intro A A'
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.conePlus_mul_conePlus hpRing A A'
  · intro D D'
    exact InfoGeometry.OperatorAlgebra.PeirceSpine.coneMinus_mul_coneMinus hpRing D D'

open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- The same categorical projector can be used as the idempotent in the existing
Peirce–Bruhat mirror, on its actual free-cell endomorphism carrier. This proves an
orthogonal pair of Bruhat-dressed idempotents there; it does not identify this carrier
with any separately supplied physical or operator algebra. -/
theorem elementary_pushout_induces_bruhat_partition
    {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X Y : C.Model} (n : ℕ) (a : Model.disk C n ⟶ X) (i : X ⟶ Y)
    (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    ∃ p : Module.End ℤ (Y.underlying.Cell n →₀ ℤ),
      p.comp p = p ∧
      ∀ A D : Module.End ℤ (Y.underlying.Cell n →₀ ℤ),
        let P_hat_m := p - genPhi p A D - genSig p A D + genV p A D * conePlus p A
        let W_hat := (1 - p) + genPhi p A D + genSig p A D - genV p A D * conePlus p A
        P_hat_m * W_hat = 0 ∧ W_hat * P_hat_m = 0 ∧ P_hat_m + W_hat = 1 := by
  obtain ⟨p, hp, _hfix⟩ := elementary_pushout_linearized_idempotent hC n a i b square
  have hpRing : p * p = p := by
    rw [Module.End.mul_eq_comp]
    exact hp
  refine ⟨p, hp, ?_⟩
  intro A D
  have hMirror := inner_godel_outer_friedman_bruhat_mirror hpRing A D
  rcases hMirror with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsum, horth, horth'⟩
  exact ⟨horth, horth', hsum⟩

/-- Any sequentially composable 3-chain of `(n + 1)`-cells `f₁, f₂, f₃ : G.Cell (n + 1)` in a
globular set `G` (`G.target n f₁ = G.source n f₂` and `G.target n f₂ = G.source n f₃`) has
parallel outer `n`-cells `G.source n f₁` and `G.target n f₃` with equal `n`-boundaries. -/
lemma globular_composable_three_chain_outer_parallel
    (G : GlobularSet.{v}) (n : ℕ) (f₁ f₂ f₃ : G.Cell (n + 1))
    (h₁₂ : G.target n f₁ = G.source n f₂)
    (h₂₃ : G.target n f₂ = G.source n f₃) :
    G.Parallel n (G.source n f₁) (G.target n f₃) ∧
    G.boundary n (G.source n f₁) = G.boundary n (G.target n f₃) := by
  have h_bd₁₂ : G.boundary n (G.source n f₁) = G.boundary n (G.target n f₂) :=
    (G.parallel_iff_boundary_eq n (G.source n f₁) (G.target n f₂)).mp
      (GlobularSet.outer_parallel h₁₂)
  have h_par₃ : G.Parallel n (G.source n f₃) (G.target n f₃) :=
    GlobularSet.Joined.parallel ⟨f₃, rfl, rfl⟩
  have h_bd₃ : G.boundary n (G.source n f₃) = G.boundary n (G.target n f₃) :=
    (G.parallel_iff_boundary_eq n (G.source n f₃) (G.target n f₃)).mp h_par₃
  have h_bd₁₃ : G.boundary n (G.source n f₁) = G.boundary n (G.target n f₃) := by
    calc G.boundary n (G.source n f₁)
      _ = G.boundary n (G.target n f₂) := h_bd₁₂
      _ = G.boundary n (G.source n f₃) := congrArg (G.boundary n) h₂₃
      _ = G.boundary n (G.target n f₃) := h_bd₃
  exact ⟨(G.parallel_iff_boundary_eq n (G.source n f₁) (G.target n f₃)).mpr h_bd₁₃, h_bd₁₃⟩

/-- **Rung `𝔊ℌ₁` (`gh1_globular_outer_parallel_and_coherator_equivalence`)**:
On any globular set `G : GlobularSet.{v}` and model `X : C.Model` of a coherator `hC : C.IsCoherator`:
1. Any sequentially composable 3-chain `f₁, f₂, f₃ : G.Cell (n + 1)` has parallel outer endpoints
   `G.Parallel n (G.source n f₁) (G.target n f₃)` and equal `n`-boundaries,
2. For any `n`-cell `z : X.underlying.Cell n`, `X.unitCell hC n z` witnesses reflexivity
   `X.underlying.Joined n z z`,
3. For any `(n + 1)`-cell `w : X.underlying.Cell (n + 1)`, `X.inverseCell hC n w` reverses
   source and target and explicitly witnesses `X.underlying.Joined n (X.underlying.target n w) (X.underlying.source n w)`,
4. The joining relation `X.underlying.Joined n` is an equivalence relation. -/
theorem gh1_globular_outer_parallel_and_coherator_equivalence
    (G : GlobularSet.{v}) (C : GlobularTheory.{v}) (hC : C.IsCoherator) (X : C.Model)
    (n : ℕ) (f₁ f₂ f₃ : G.Cell (n + 1))
    (h₁₂ : G.target n f₁ = G.source n f₂) (h₂₃ : G.target n f₂ = G.source n f₃)
    (z : X.underlying.Cell n) (w : X.underlying.Cell (n + 1)) :
    G.Parallel n (G.source n f₁) (G.target n f₃) ∧
    G.boundary n (G.source n f₁) = G.boundary n (G.target n f₃) ∧
    X.underlying.Joined n z z ∧
    X.underlying.Joined n (X.underlying.target n w) (X.underlying.source n w) ∧
    Equivalence (X.underlying.Joined n) := by
  have h_chain := globular_composable_three_chain_outer_parallel G n f₁ f₂ f₃ h₁₂ h₂₃
  have h_refl_z : X.underlying.Joined n z z := by
    refine ⟨X.unitCell hC n z, ?_, ?_⟩
    · rw [X.unitCell_source hC n z]
    · rw [X.unitCell_target hC n z]
  have h_symm_w : X.underlying.Joined n (X.underlying.target n w) (X.underlying.source n w) := by
    refine ⟨X.inverseCell hC n w, ?_, ?_⟩
    · rw [X.inverseCell_source hC n w]
    · rw [X.inverseCell_target hC n w]
  exact ⟨h_chain.1, h_chain.2, h_refl_z, h_symm_w, X.joined_equivalence hC n⟩

/-- `Model.componentsMap` preserves the identity morphism on every connected component. -/
lemma componentsMap_id_apply {C : GlobularTheory.{v}} (X : C.Model) (c : X.Components) :
    Model.componentsMap (𝟙 X) c = c := by
  induction c using Quot.inductionOn with
  | h x₀ => rfl

/-- `Model.componentsMap` is functorial under composition of model morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`. -/
lemma componentsMap_comp_apply {C : GlobularTheory.{v}} {X Y Z : C.Model}
    (f : X ⟶ Y) (g : Y ⟶ Z) (c : X.Components) :
    Model.componentsMap g (Model.componentsMap f c) = Model.componentsMap (f ≫ g) c := by
  induction c using Quot.inductionOn with
  | h x₀ => rfl

/-- **Rung `𝔊ℌ₂` (`gh2_elementary_pushout_retraction_and_components_injective`)**:
For any coherator `hC : C.IsCoherator` and elementary expansion pushout square
`square : IsPushout a (Model.J C n) i b`:
1. The source horn `Model.J C n : Model.disk C n ⟶ Model.disk C (n + 1)` is retracted by `Model.unitMap C hC n`,
2. Pushing out along `a : Model.disk C n ⟶ X` produces a model retraction `r : Y ⟶ X` with `i ≫ r = 𝟙 X`
   whose induced `π₀` map `Model.componentsMap r` is a left inverse to `Model.componentsMap i`,
3. Consequently, `Model.componentsMap i` is injective and `Model.componentsMap r` is surjective,
4. Without cylinder path data, a bare retraction (`∀ u : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) u) = u`)
   does not imply surjectivity (`¬ Function.Surjective (fun _ : Unit => false)`). -/
theorem gh2_elementary_pushout_retraction_and_components_injective
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X Y : C.Model) (n : ℕ)
    (a : Model.disk C n ⟶ X) (i : X ⟶ Y) (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    Model.J C n ≫ Model.unitMap C hC n = 𝟙 (Model.disk C n) ∧
    (∃ r : Y ⟶ X, i ≫ r = 𝟙 X ∧
      Function.LeftInverse (Model.componentsMap r) (Model.componentsMap i) ∧
      Function.Surjective (Model.componentsMap r)) ∧
    Function.Injective (Model.componentsMap i) ∧
    ((∀ u : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) u) = u) ∧
     ¬ Function.Surjective (fun _ : Unit => false)) := by
  obtain ⟨r, hr⟩ := Model.elementary_pushout_retraction hC n a i b square
  have h_left_inv : Function.LeftInverse (Model.componentsMap r) (Model.componentsMap i) := by
    intro c
    calc Model.componentsMap r (Model.componentsMap i c)
      _ = Model.componentsMap (i ≫ r) c := componentsMap_comp_apply i r c
      _ = Model.componentsMap (𝟙 X) c := by rw [hr]
      _ = c := componentsMap_id_apply X c
  refine ⟨Model.J_comp_unitMap C hC n,
    ⟨r, hr, h_left_inv, h_left_inv.surjective⟩,
    h_left_inv.injective,
    ⟨fun _ => rfl, fun h_surj => by obtain ⟨_, hu⟩ := h_surj true; exact Bool.noConfusion hu⟩⟩

/-- On any globular set `X` with reflexive `Joined`, the identity morphism `GlobularSet.Hom.id X`
satisfies `GlobularSet.ExactBoundaryTest`. -/
lemma exactBoundaryTest_id {X : GlobularSet.{v}}
    (hX_refl : ∀ k (x : X.Cell k), X.Joined k x x) :
    GlobularSet.ExactBoundaryTest (GlobularSet.Hom.id X) := by
  intro k bd x hx
  have h_id_bd : (GlobularSet.Hom.id X).boundaryMap k bd = bd := by
    cases k <;> rfl
  exact ⟨x, hx.trans h_id_bd, hX_refl k x⟩

/-- If `f : GlobularSet.Hom X Y` and `g : GlobularSet.Hom Y Z` satisfy `ExactBoundaryTest` and
`Z.Joined` is transitive, then the composite `f.comp g : GlobularSet.Hom X Z` satisfies
`ExactBoundaryTest`. -/
lemma exactBoundaryTest_comp {X Y Z : GlobularSet.{v}}
    (f : GlobularSet.Hom X Y) (g : GlobularSet.Hom Y Z)
    (hf : GlobularSet.ExactBoundaryTest f) (hg : GlobularSet.ExactBoundaryTest g)
    (hZ_trans : ∀ k (a b c : Z.Cell k), Z.Joined k a b → Z.Joined k b c → Z.Joined k a c) :
    GlobularSet.ExactBoundaryTest (f.comp g) := by
  intro k bd z hz
  rw [GlobularSet.Hom.boundaryMap_comp] at hz
  obtain ⟨y, hy_bd, hyz⟩ := hg k (f.boundaryMap k bd) z hz
  obtain ⟨x, hx_bd, hxy⟩ := hf k bd y hy_bd
  have h_map : Z.Joined k ((f.comp g).app k x) (g.app k y) := g.map_joined hxy
  exact ⟨x, hx_bd, hZ_trans k ((f.comp g).app k x) (g.app k y) z h_map hyz⟩

/-- **Rung `𝔊ℌ₃` (`gh3_exact_boundary_test_endpoint_section_and_retract_factor`)**:
The globular homotopy-lifting and composition engines on `GlobularSet`:
1. `exactBoundaryTest_id` and `exactBoundaryTest_comp`: `ExactBoundaryTest` contains identities on
   reflexive globular sets and is closed under composition when the target has transitive `Joined`,
2. `ExactBoundaryTest.reflects_joined` across a composite `f.comp g`: if `f` and `g` satisfy
   `ExactBoundaryTest`, then `(f.comp g)` reflects `Z.Joined n` on parallel cells into `X.Joined n`,
3. `exactBoundaryTest_endpoint_section`: if cylinder endpoint projections `p₀, p₁ : Hom P X` lift
   boundaries and `h : Hom X P` is a section of `p₀`, then `h.comp p₁` satisfies `ExactBoundaryTest`,
4. `ExactBoundaryTest.of_retract_factor`: if `i : Hom X Y` has retraction `r : Hom Y X` (`i.comp r = Hom.id X`)
   and `r.comp u` satisfies `ExactBoundaryTest`, then `i` satisfies `ExactBoundaryTest`. -/
theorem gh3_exact_boundary_test_endpoint_section_and_retract_factor
    {P X Y Z : GlobularSet.{v}}
    (f : GlobularSet.Hom X Y) (g : GlobularSet.Hom Y Z)
    (hf : GlobularSet.ExactBoundaryTest f) (hg : GlobularSet.ExactBoundaryTest g)
    (hZ_trans : ∀ k (a b c : Z.Cell k), Z.Joined k a b → Z.Joined k b c → Z.Joined k a c)
    {n : ℕ} {x₁ x₂ : X.Cell n} (hp : X.Parallel n x₁ x₂)
    (hJ : Z.Joined n ((f.comp g).app n x₁) ((f.comp g).app n x₂))
    (p₀ p₁ : GlobularSet.Hom P X) (h : GlobularSet.Hom X P)
    (hp₀ : GlobularSet.LiftsBoundaries p₀) (hp₁ : GlobularSet.LiftsBoundaries p₁)
    (h_sec : ∀ k x, p₀.app k (h.app k x) = x)
    (hX_refl : ∀ k x, X.Joined k x x)
    (i : GlobularSet.Hom X Y) (r : GlobularSet.Hom Y X) (u : GlobularSet.Hom X Y)
    (hir : i.comp r = GlobularSet.Hom.id X)
    (hru : GlobularSet.ExactBoundaryTest (r.comp u))
    (hY_refl : ∀ k y, Y.Joined k y y) :
    GlobularSet.ExactBoundaryTest (GlobularSet.Hom.id X) ∧
    GlobularSet.ExactBoundaryTest (f.comp g) ∧
    (f.comp g).boundaryMap n (X.boundary n x₁) =
      g.boundaryMap n (f.boundaryMap n (X.boundary n x₂)) ∧
    X.Joined n x₁ x₂ ∧
    GlobularSet.ExactBoundaryTest (h.comp p₁) ∧
    GlobularSet.ExactBoundaryTest i := by
  have h_id : GlobularSet.ExactBoundaryTest (GlobularSet.Hom.id X) :=
    exactBoundaryTest_id hX_refl
  have h_comp : GlobularSet.ExactBoundaryTest (f.comp g) :=
    exactBoundaryTest_comp f g hf hg hZ_trans
  have h_bd_comp : (f.comp g).boundaryMap n (X.boundary n x₁) =
      g.boundaryMap n (f.boundaryMap n (X.boundary n x₂)) := by
    rw [GlobularSet.Hom.boundaryMap_comp, (X.parallel_iff_boundary_eq n x₁ x₂).mp hp]
  have h_refl_joined : X.Joined n x₁ x₂ :=
    h_comp.reflects_joined hp hJ
  have h_sec_test : GlobularSet.ExactBoundaryTest (h.comp p₁) :=
    GlobularSet.exactBoundaryTest_endpoint_section p₀ p₁ h hp₀ hp₁ h_sec hX_refl
  have h_ret_test : GlobularSet.ExactBoundaryTest i :=
    GlobularSet.ExactBoundaryTest.of_retract_factor i r u hir hru hY_refl
  exact ⟨h_id, h_comp, h_bd_comp, h_refl_joined, h_sec_test, h_ret_test⟩

/-- Every elementary disk attachment `square : IsPushout a (Model.J C n) i b` out of a cellular
model `hX : X.IsCellular` satisfies `GlobularSet.ExactBoundaryTest (Model.underlyingMap i)`. -/
lemma elementary_expansion_exactBoundaryTest
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : Model.disk C n ⟶ X) (Y : C.Model) (i : X ⟶ Y) (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    GlobularSet.ExactBoundaryTest (Model.underlyingMap i) := by
  intro d bd y hy
  let q := max (n + 1) (d + 1)
  have hnq : n ≤ q := Nat.le_trans (Nat.le_succ n) (Nat.le_max_left (n + 1) (d + 1))
  have hdq : d ≤ q := Nat.le_trans (Nat.le_succ d) (Nat.le_max_right (n + 1) (d + 1))
  have hd₁q : d + 1 ≤ q := Nat.le_max_right (n + 1) (d + 1)
  let F := Model.cutoffFunctor hC q
  let ηX := Model.underlyingMap (Model.cutoffUnit hC q X)
  let ηY := Model.underlyingMap (Model.cutoffUnit hC q Y)
  have hs : (Model.underlyingMap i).comp ηY =
      ηX.comp (Model.underlyingMap (F.map i).hom) :=
    congrArg Model.underlyingMap ((Model.cutoffAdjunction hC q).unit.naturality i)
  exact GlobularSet.exactBoundaryTest_at_of_low_square
    (Model.underlyingMap i) (Model.underlyingMap (F.map i).hom) ηX ηY hs
    (Model.cutoff_elementary_exactBoundaryTest hC q n hnq hX a i b square)
    d (fun k hk => Model.cutoffUnit_low_bijective hC q X k (Nat.le_trans hk hdq))
    (Model.cutoffUnit_low_bijective hC q Y d hdq).injective
    (Model.cutoffUnit_low_bijective hC q Y (d + 1) hd₁q).surjective bd y hy

/-- **Rung `𝔊ℌ₄` (`gh4_coskeletal_cutoff_low_square_and_elementary_test`)**:
For attachment dimension `n : ℕ`, query dimension `d : ℕ`, and coskeletal ceiling `q := max (n + 1) (d + 1)`:
1. The ceiling simultaneously bounds `n ≤ q`, `d ≤ q`, and `d + 1 ≤ q`,
2. Cellular cofibrancy `Model.Cofibrant hC q ((Model.cutoffFunctor hC q).obj X)` and downward
   induction `Model.ExpansionContraction hC q (n + 1)` hold in the `q`-cutoff category,
3. The `q`-cutoff unit `Model.cutoffUnit hC q X` is bijective at all dimensions `k ≤ d` and at `d + 1`,
4. Both the `q`-cutoff expansion `(Model.cutoffFunctor hC q).map i` and the un-truncated map
   `Model.underlyingMap i` satisfy `GlobularSet.ExactBoundaryTest`. -/
theorem gh4_coskeletal_cutoff_low_square_and_elementary_test
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n d : ℕ)
    (a : Model.disk C n ⟶ X) (Y : C.Model) (i : X ⟶ Y) (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b) :
    let q := max (n + 1) (d + 1)
    (n ≤ q ∧ d ≤ q ∧ d + 1 ≤ q) ∧
    Model.Cofibrant hC q ((Model.cutoffFunctor hC q).obj X) ∧
    Model.ExpansionContraction hC q (n + 1) ∧
    (∀ k, k ≤ d → Function.Bijective ((Model.underlyingMap (Model.cutoffUnit hC q X)).app k)) ∧
    Function.Bijective ((Model.underlyingMap (Model.cutoffUnit hC q Y)).app d) ∧
    Function.Bijective ((Model.underlyingMap (Model.cutoffUnit hC q Y)).app (d + 1)) ∧
    GlobularSet.ExactBoundaryTest (Model.underlyingMap ((Model.cutoffFunctor hC q).map i).hom) ∧
    GlobularSet.ExactBoundaryTest (Model.underlyingMap i) := by
  let q := max (n + 1) (d + 1)
  have hnq : n ≤ q := Nat.le_trans (Nat.le_succ n) (Nat.le_max_left (n + 1) (d + 1))
  have hdq : d ≤ q := Nat.le_trans (Nat.le_succ d) (Nat.le_max_right (n + 1) (d + 1))
  have hd₁q : d + 1 ≤ q := Nat.le_max_right (n + 1) (d + 1)
  have h_low : ∀ k, k ≤ d →
      Function.Bijective ((Model.underlyingMap (Model.cutoffUnit hC q X)).app k) := by
    intro k hk
    exact Model.cutoffUnit_low_bijective hC q X k (Nat.le_trans hk hdq)
  exact ⟨⟨hnq, hdq, hd₁q⟩,
    Model.isCellular_cutoff_cofibrant hC q hX,
    Model.expansionContraction_all hC q (n + 1),
    h_low,
    Model.cutoffUnit_low_bijective hC q Y d hdq,
    Model.cutoffUnit_low_bijective hC q Y (d + 1) hd₁q,
    Model.cutoff_elementary_exactBoundaryTest hC q n hnq hX a i b square,
    elementary_expansion_exactBoundaryTest C hC X hX n a Y i b square⟩

/-- **Rung `𝔊ℌ₅` (`gh5_grothendieck_elementary_expansion_and_homotopy_group_iso`)**:
Proves the single-stage and two-stage iterated Grothendieck elementary expansion theorem
together with the induced group isomorphisms on all higher homotopy groups:
1. For any cellular model `X` and elementary pushout `square₁ : IsPushout a₁ (Model.J C n₁) i₁ b₁`,
   `Model.WeakEquivalence hC i₁` holds and induces `X.HomotopyGroup hC x k ≃* Y.HomotopyGroup hC ((Model.underlyingMap i₁).app 0 x) k`,
2. Given a second elementary pushout `square₂ : IsPushout a₂ (Model.J C n₂) i₂ b₂` out of `Y` (`hY : Y.IsCellular`),
   the composite `i₁ ≫ i₂ : X ⟶ Z` satisfies `GlobularSet.ExactBoundaryTest (Model.underlyingMap (i₁ ≫ i₂))`,
   is a `Model.WeakEquivalence hC (i₁ ≫ i₂)`, and induces a multiplicative group isomorphism
   `X.HomotopyGroup hC x k ≃* Z.HomotopyGroup hC ((Model.underlyingMap (i₁ ≫ i₂)).app 0 x) k`. -/
theorem gh5_grothendieck_elementary_expansion_and_homotopy_group_iso
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n₁ : ℕ)
    (a₁ : Model.disk C n₁ ⟶ X) (Y : C.Model) (hY : Y.IsCellular)
    (i₁ : X ⟶ Y) (b₁ : Model.disk C (n₁ + 1) ⟶ Y)
    (square₁ : IsPushout a₁ (Model.J C n₁) i₁ b₁)
    (n₂ : ℕ) (a₂ : Model.disk C n₂ ⟶ Y) (Z : C.Model)
    (i₂ : Y ⟶ Z) (b₂ : Model.disk C (n₂ + 1) ⟶ Z)
    (square₂ : IsPushout a₂ (Model.J C n₂) i₂ b₂)
    (x : X.underlying.Cell 0) (k : ℕ) :
    Model.WeakEquivalence hC i₁ ∧
    Nonempty (X.HomotopyGroup hC x k ≃* Y.HomotopyGroup hC ((Model.underlyingMap i₁).app 0 x) k) ∧
    GlobularSet.ExactBoundaryTest (Model.underlyingMap (i₁ ≫ i₂)) ∧
    Model.WeakEquivalence hC (i₁ ≫ i₂) ∧
    Function.Bijective (Model.componentsMap (i₁ ≫ i₂)) ∧
    Nonempty (X.HomotopyGroup hC x k ≃*
      Z.HomotopyGroup hC ((Model.underlyingMap (i₁ ≫ i₂)).app 0 x) k) := by
  have h_test₁ : GlobularSet.ExactBoundaryTest (Model.underlyingMap i₁) :=
    elementary_expansion_exactBoundaryTest C hC X hX n₁ a₁ Y i₁ b₁ square₁
  have h_test₂ : GlobularSet.ExactBoundaryTest (Model.underlyingMap i₂) :=
    elementary_expansion_exactBoundaryTest C hC Y hY n₂ a₂ Z i₂ b₂ square₂
  have h_Z_trans : ∀ d (u v w : Z.underlying.Cell d),
      Z.underlying.Joined d u v → Z.underlying.Joined d v w → Z.underlying.Joined d u w := by
    intro d u v w huv hvw
    exact (Z.joined_equivalence hC d).trans huv hvw
  have h_test₁₂ : GlobularSet.ExactBoundaryTest (Model.underlyingMap (i₁ ≫ i₂)) :=
    exactBoundaryTest_comp (Model.underlyingMap i₁) (Model.underlyingMap i₂)
      h_test₁ h_test₂ h_Z_trans
  have hW₁ : Model.WeakEquivalence hC i₁ :=
    Model.weakEquivalence_of_exactBoundaryTest hC i₁ h_test₁
  have hW₁₂ : Model.WeakEquivalence hC (i₁ ≫ i₂) :=
    Model.weakEquivalence_of_exactBoundaryTest hC (i₁ ≫ i₂) h_test₁₂
  exact ⟨hW₁,
    ⟨Model.homotopyGroupIsoOfWeakEquivalence i₁ hC hW₁ x k⟩,
    h_test₁₂,
    hW₁₂,
    hW₁₂.1,
    ⟨Model.homotopyGroupIsoOfWeakEquivalence (i₁ ≫ i₂) hC hW₁₂ x k⟩⟩

/-- **Rung `𝔊ℌ₆` (`gh6_grothendieck_ara_maltsiniotis_coherator_localization`)**:
Explicit morphism-level instantiation of the Grothendieck–Ara–Maltsiniotis Coherator Localization:
For every coherator `C : GlobularTheory.{u}` (`hC : C.IsCoherator`), every topological realization
`R : HomotopyHypothesis.Blueprint.OAIRealization C`, and every weak homotopy equivalence
`f : K ⟶ L` in `TopCat.{u}` (`hf : HomotopyHypothesis.weakHomotopyEquivalences f`):
1. A topological realization of `C` exists (`Nonempty (HomotopyHypothesis.Blueprint.OAIRealization C)`),
2. The fundamental ∞-groupoid map `R.Pi.map f : R.groupoid K ⟶ R.groupoid L` is a model weak
   equivalence (`Model.WeakEquivalence hC (R.Pi.map f)`),
3. `Model.componentsMap (R.Pi.map f)` is bijective on `π₀` and induces a multiplicative group
   isomorphism `(R.groupoid K).HomotopyGroup hC x₀ k ≃* (R.groupoid L).HomotopyGroup hC ((Model.underlyingMap (R.Pi.map f)).app 0 x₀) k`
   at every basepoint `x₀` and dimension `k`,
4. Its image `((HomotopyHypothesis.Blueprint.W hC).Q).map (R.Pi.map f)` in the localized category is
   an isomorphism (`IsIso`), and `R.Pi ⋙ (HomotopyHypothesis.Blueprint.W hC).Q` exhibits `Ho(C.Model)`
   as the localization of `TopCat.{u}` at `weakHomotopyEquivalences`. -/
theorem gh6_grothendieck_ara_maltsiniotis_coherator_localization
    (C : GlobularTheory.{u}) (hC : C.IsCoherator)
    (R : HomotopyHypothesis.Blueprint.OAIRealization C)
    {K L : TopCat.{u}} (f : K ⟶ L)
    (hf : HomotopyHypothesis.weakHomotopyEquivalences f)
    (x₀ : (R.Pi.obj K).underlying.Cell 0) (k : ℕ) :
    Nonempty (HomotopyHypothesis.Blueprint.OAIRealization C) ∧
    Model.WeakEquivalence hC (R.Pi.map f) ∧
    (Function.Injective (Model.componentsMap (R.Pi.map f)) ∧
     Function.Surjective (Model.componentsMap (R.Pi.map f))) ∧
    Nonempty ((R.Pi.obj K).HomotopyGroup hC x₀ k ≃*
      (R.Pi.obj L).HomotopyGroup hC ((Model.underlyingMap (R.Pi.map f)).app 0 x₀) k) ∧
    IsIso (((HomotopyHypothesis.Blueprint.W hC).Q).map (R.Pi.map f)) ∧
    (R.Pi ⋙ (HomotopyHypothesis.Blueprint.W hC).Q).IsLocalization
      HomotopyHypothesis.weakHomotopyEquivalences := by
  have h_oai := HomotopyHypothesis.Blueprint.oaiStatement.{u} C hC
  have h_R := h_oai.2 R
  have hW_f : Model.WeakEquivalence hC (R.Pi.map f) := h_R.1 f hf
  rcases hW_f.1 with ⟨h_inj, h_surj⟩
  have h_iso : IsIso (((HomotopyHypothesis.Blueprint.W hC).Q).map (R.Pi.map f)) :=
    Localization.inverts (HomotopyHypothesis.Blueprint.W hC).Q
      (HomotopyHypothesis.Blueprint.W hC) (R.Pi.map f) hW_f
  exact ⟨h_oai.1, hW_f, ⟨h_inj, h_surj⟩,
    ⟨Model.homotopyGroupIsoOfWeakEquivalence (R.Pi.map f) hC hW_f x₀ k⟩,
    h_iso, h_R.2⟩

/-- **Strict Eckmann–Hilton Commutativity Collapse (`eckmann_hilton_strict_commutativity`, `𝔊ℌ₂`)**:
If two binary operations `m1, m2 : α → α → α` share a strict two-sided unit `e : α` and satisfy
the strict middle-four interchange law `m2 (m1 a b) (m1 c d) = m1 (m2 a c) (m2 b d)`, then
`m2 a b = m1 a b` and `m1 a b = m1 b a` for all `a, b : α`. -/
theorem eckmann_hilton_strict_commutativity {α : Type*}
    (m1 m2 : α → α → α) (e : α)
    (h1L : ∀ x, m1 e x = x) (h1R : ∀ x, m1 x e = x)
    (h2L : ∀ x, m2 e x = x) (h2R : ∀ x, m2 x e = x)
    (h_inter : ∀ a b c d, m2 (m1 a b) (m1 c d) = m1 (m2 a c) (m2 b d))
    (a b : α) :
    m2 a b = m1 a b ∧ m1 a b = m1 b a := by
  have h_eq : m2 a b = m1 a b := by
    calc m2 a b = m2 (m1 a e) (m1 e b) := by rw [h1R a, h1L b]
    _ = m1 (m2 a e) (m2 e b) := h_inter a e e b
    _ = m1 a b := by rw [h2R a, h2L b]
  have h_comm : m1 a b = m1 b a := by
    calc m1 a b = m1 (m2 e a) (m2 b e) := by rw [h2L a, h2R b]
    _ = m2 (m1 e b) (m1 a e) := (h_inter e b a e).symm
    _ = m2 b a := by rw [h1L b, h1R a]
    _ = m1 (m2 b e) (m2 e a) := by
        calc m2 b a = m2 (m1 b e) (m1 e a) := by rw [h1R b, h1L a]
        _ = m1 (m2 b e) (m2 e a) := h_inter b e e a
    _ = m1 b a := by rw [h2R b, h2L a]
  exact ⟨h_eq, h_comm⟩

/-- **Ara's 2-Out-of-3 Law on Dimensionwise Bijections (`ara_two_out_of_three_dimensionwise_bijective`, `𝔊ℌ₄`)**:
For any indexed families of maps `f : ∀ k : ℕ, X k → Y k` and `g : ∀ k : ℕ, Y k → Z k`,
dimensionwise bijectivity (`∀ k : ℕ, Function.Bijective (f k)`) satisfies the 2-out-of-3
closure law across `f`, `g`, and `(fun k x => g k (f k x))`. -/
theorem ara_two_out_of_three_dimensionwise_bijective {X Y Z : ℕ → Type*}
    (f : ∀ k, X k → Y k) (g : ∀ k, Y k → Z k) :
    ((∀ k, Function.Bijective (f k)) →
      ((∀ k, Function.Bijective (g k)) ↔ (∀ k, Function.Bijective (fun x => g k (f k x))))) ∧
    ((∀ k, Function.Bijective (g k)) →
      ((∀ k, Function.Bijective (f k)) ↔ (∀ k, Function.Bijective (fun x => g k (f k x))))) := by
  refine ⟨fun hf => ⟨fun hg k => (hg k).comp (hf k), fun hgf k => ?_⟩,
          fun hg => ⟨fun hf k => (hg k).comp (hf k), fun hgf k => ?_⟩⟩
  · refine ⟨fun y1 y2 hy => ?_, fun z => ?_⟩
    · obtain ⟨x1, rfl⟩ := (hf k).2 y1
      obtain ⟨x2, rfl⟩ := (hf k).2 y2
      exact congrArg (f k) ((hgf k).1 hy)
    · obtain ⟨x, hx⟩ := (hgf k).2 z
      exact ⟨f k x, hx⟩
  · refine ⟨fun x1 x2 hx => (hgf k).1 (congrArg (g k) hx), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hgf k).2 (g k y)
    exact ⟨x, (hg k).1 hx⟩

/-- **Rung `𝔊ℌ₇` (`gh7_grothendieck_elementary_expansion_peirce_bruhat_master_synthesis`)**:
Master synthesis uniting Grothendieck's elementary expansion weak equivalence, topological
realization localization, and the constructive Peirce–Bruhat cylinder elementary expansion:
1. `GlobularSet.ExactBoundaryTest (Model.underlyingMap i)` and `Model.WeakEquivalence hC i` for
   any elementary disk pushout `square : IsPushout a (Model.J C n) i b` of a cellular model `X`,
2. Multiplicative group isomorphism `X.HomotopyGroup hC x k ≃* Y.HomotopyGroup hC ((Model.underlyingMap i).app 0 x) k`,
3. Over any `[Ring B]` with idempotent `hP : P * P = P` and operators `A, D, U, V : B`:
   - The unipotent Peirce cylinder rotor `G_m = (1 + conePlus P A) * (1 - coneMinus P D)` and its
     inverse `G_m_inv = (1 + coneMinus P D) * (1 - conePlus P A)` satisfy `G_m * G_m_inv = 1 ∧ G_m_inv * G_m = 1`,
   - Conjugation `Z ↦ G_m * Z * G_m_inv` is multiplicative (`G_m * (U * V) * G_m_inv = (G_m * U * G_m_inv) * (G_m * V * G_m_inv)`),
   - Forward cylinder transport dresses `P` and `1 - P` into `P_hat_m` and `W_hat`, and reverse
     retraction conjugation recovers `G_m_inv * P_hat_m * G_m = P` and `G_m_inv * W_hat * G_m = 1 - P`,
   - Both dressed endpoints are strictly idempotent and orthogonal with `P_hat_m + W_hat = 1`,
   - Constructive internal globular boundary nilpotence `globBoundary P A (globBoundary P A U) = 0`,
   - Constructive elementary expansion `i_exp P A (P * U * P)` 4-term word, exact commutator
     diagonal shift `evenGrade P (i_exp P A (P * U * P) - P * U * P) = - comm (conePlus P A) (coneMinus P A * (P * U * P))`,
     and two-sided retraction isomorphism `r_ret P A (i_exp P A (P * U * P)) = P * U * P` and
     `i_exp P A (r_ret P A (dressedPeirceProjector P A A * V * dressedPeirceProjector P A A)) = dressedPeirceProjector P A A * V * dressedPeirceProjector P A A`. -/
theorem gh7_grothendieck_elementary_expansion_peirce_bruhat_master_synthesis
    (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : Model.disk C n ⟶ X) (Y : C.Model) (i : X ⟶ Y) (b : Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (Model.J C n) i b)
    (x : X.underlying.Cell 0) (k : ℕ)
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A D U V : B) :
    let G_m := (1 + conePlus P A) * (1 - coneMinus P D)
    let G_m_inv := (1 + coneMinus P D) * (1 - conePlus P A)
    let P_hat_m := P - genPhi P A D - genSig P A D + genV P A D * conePlus P A
    let W_hat := (1 - P) + genPhi P A D + genSig P A D - genV P A D * conePlus P A
    let u0 := P * U * P
    let v_hat := dressedPeirceProjector P A A * V * dressedPeirceProjector P A A
    GlobularSet.ExactBoundaryTest (Model.underlyingMap i) ∧
    Model.WeakEquivalence hC i ∧
    Nonempty (X.HomotopyGroup hC x k ≃* Y.HomotopyGroup hC ((Model.underlyingMap i).app 0 x) k) ∧
    (G_m * G_m_inv = 1 ∧ G_m_inv * G_m = 1) ∧
    G_m * (U * V) * G_m_inv = (G_m * U * G_m_inv) * (G_m * V * G_m_inv) ∧
    (G_m * P * G_m_inv = P_hat_m ∧ G_m * (1 - P) * G_m_inv = W_hat) ∧
    (G_m_inv * P_hat_m * G_m = P ∧ G_m_inv * W_hat * G_m = 1 - P) ∧
    (P_hat_m * P_hat_m = P_hat_m ∧ W_hat * W_hat = W_hat ∧
     P_hat_m + W_hat = 1 ∧ P_hat_m * W_hat = 0 ∧ W_hat * P_hat_m = 0) ∧
    globBoundary P A (globBoundary P A U) = 0 ∧
    evenGrade P (i_exp P A u0 - u0) = - comm (conePlus P A) (coneMinus P A * u0) ∧
    (r_ret P A (i_exp P A u0) = u0 ∧ i_exp P A (r_ret P A v_hat) = v_hat) := by
  have h_test : GlobularSet.ExactBoundaryTest (Model.underlyingMap i) :=
    elementary_expansion_exactBoundaryTest C hC X hX n a Y i b square
  have hW : Model.WeakEquivalence hC i :=
    Model.weakEquivalence_of_exactBoundaryTest hC i h_test
  have hM := inner_godel_outer_friedman_bruhat_mirror hP A D
  have hG1 : (1 + conePlus P A) * (1 - coneMinus P D) *
      ((1 + coneMinus P D) * (1 - conePlus P A)) = 1 := hM.2.2.2.2.2.2.2.2.2.1
  have hG2 : (1 + coneMinus P D) * (1 - conePlus P A) *
      ((1 + conePlus P A) * (1 - coneMinus P D)) = 1 := hM.2.2.2.2.2.2.2.2.2.2.1
  have hConjMul :
      (1 + conePlus P A) * (1 - coneMinus P D) * (U * V) *
        ((1 + coneMinus P D) * (1 - conePlus P A)) =
      ((1 + conePlus P A) * (1 - coneMinus P D) * U *
        ((1 + coneMinus P D) * (1 - conePlus P A))) *
      ((1 + conePlus P A) * (1 - coneMinus P D) * V *
        ((1 + coneMinus P D) * (1 - conePlus P A))) := by
    calc ((1 + conePlus P A) * (1 - coneMinus P D)) * (U * V) *
          ((1 + coneMinus P D) * (1 - conePlus P A))
      _ = ((1 + conePlus P A) * (1 - coneMinus P D)) * U * 1 * V *
          ((1 + coneMinus P D) * (1 - conePlus P A)) := by simp only [mul_one, mul_assoc]
      _ = ((1 + conePlus P A) * (1 - coneMinus P D)) * U *
          (((1 + coneMinus P D) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P D))) * V *
          ((1 + coneMinus P D) * (1 - conePlus P A)) := by rw [hG2]
      _ = ((1 + conePlus P A) * (1 - coneMinus P D) * U *
            ((1 + coneMinus P D) * (1 - conePlus P A))) *
          ((1 + conePlus P A) * (1 - coneMinus P D) * V *
            ((1 + coneMinus P D) * (1 - conePlus P A))) := by simp only [mul_assoc]
  have hFwdP : (1 + conePlus P A) * (1 - coneMinus P D) * P *
      ((1 + coneMinus P D) * (1 - conePlus P A)) =
      P - genPhi P A D - genSig P A D + genV P A D * conePlus P A :=
    hM.2.2.2.2.2.2.2.2.2.2.2.1
  have hFwdW : (1 + conePlus P A) * (1 - coneMinus P D) * (1 - P) *
      ((1 + coneMinus P D) * (1 - conePlus P A)) =
      (1 - P) + genPhi P A D + genSig P A D - genV P A D * conePlus P A :=
    hM.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hRevP :
      (1 + coneMinus P D) * (1 - conePlus P A) *
        (P - genPhi P A D - genSig P A D + genV P A D * conePlus P A) *
        ((1 + conePlus P A) * (1 - coneMinus P D)) = P := by
    rw [← hFwdP]
    calc (1 + coneMinus P D) * (1 - conePlus P A) *
          ((1 + conePlus P A) * (1 - coneMinus P D) * P *
            ((1 + coneMinus P D) * (1 - conePlus P A))) *
          ((1 + conePlus P A) * (1 - coneMinus P D))
      _ = ((1 + coneMinus P D) * (1 - conePlus P A) *
            ((1 + conePlus P A) * (1 - coneMinus P D))) * P *
          (((1 + coneMinus P D) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P D))) := by simp only [mul_assoc]
      _ = 1 * P * 1 := by rw [hG2]
      _ = P := by simp only [one_mul, mul_one]
  have hRevW :
      (1 + coneMinus P D) * (1 - conePlus P A) *
        ((1 - P) + genPhi P A D + genSig P A D - genV P A D * conePlus P A) *
        ((1 + conePlus P A) * (1 - coneMinus P D)) = 1 - P := by
    rw [← hFwdW]
    calc (1 + coneMinus P D) * (1 - conePlus P A) *
          ((1 + conePlus P A) * (1 - coneMinus P D) * (1 - P) *
            ((1 + coneMinus P D) * (1 - conePlus P A))) *
          ((1 + conePlus P A) * (1 - coneMinus P D))
      _ = ((1 + coneMinus P D) * (1 - conePlus P A) *
            ((1 + conePlus P A) * (1 - coneMinus P D))) * (1 - P) *
          (((1 + coneMinus P D) * (1 - conePlus P A)) *
            ((1 + conePlus P A) * (1 - coneMinus P D))) := by simp only [mul_assoc]
      _ = 1 * (1 - P) * 1 := by rw [hG2]
      _ = 1 - P := by simp only [one_mul, mul_one]
  have hGlob := (internal_globular_boundary_squared_zero hP A U).2.2.2
  have hShift := (constructive_elementary_expansion_word_and_commutator_shift hP A U).2
  have hRet := constructive_elementary_expansion_retraction_isomorphism hP A U V U V
  exact ⟨h_test, hW, ⟨Model.homotopyGroupIsoOfWeakEquivalence i hC hW x k⟩,
         ⟨hG1, hG2⟩, hConjMul, ⟨hFwdP, hFwdW⟩, ⟨hRevP, hRevW⟩,
         ⟨hM.2.2.2.2.2.2.2.1, hM.2.2.2.2.2.2.2.2.1,
          hM.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hM.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
         hGlob, hShift, ⟨hRet.1, hRet.2.1⟩⟩

end InfoGeometry.Canonical.GrothendieckElementaryExpansionPoset
