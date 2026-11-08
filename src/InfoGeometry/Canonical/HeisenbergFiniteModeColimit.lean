/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HeisenbergFiniteModeStages
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The filtered finite-mode `ModuleCat` colimit & `LieEquiv` for the Heisenberg algebra

Finite subsets of the standard `Jₖ, K` basis form a filtered diagram of
submodules in `ModuleCat 𝕜`. The canonical cocone into the full central
extension induces a bijective `ModuleCat 𝕜` comparison map, across which we
transport the Heisenberg `LieRing` and `LieAlgebra` structures to obtain a
canonical `LieEquiv`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeStages`:
    `heisenbergFiniteModeStage`, `heisenberg_mem_finiteModeStage`,
    `heisenberg_mode_stage_contains_jgen`, `heisenberg_mode_stage_contains_kgen`.
- BUCKET 2 (Deconfabulation):
  * Finite subsets of Heisenberg modes do not form closed Lie subalgebras unless
    the central mode `none` is included, so the filtered colimit is formed in
    `ModuleCat 𝕜` and its Lie bracket is transported across
    `heisenbergFiniteModeColimitEquiv` using explicit `change` exposures and
    `LinearEquiv.apply_symm_apply` to avoid `simp` recursion.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergFiniteModeDiagram`, `heisenbergFiniteModeCocone`,
    `heisenbergFiniteModeColimit`, `heisenbergFiniteModeColimitMap`:
    filtered `ModuleCat 𝕜` colimit and comparison morphism.
  * `heisenbergFiniteModeColimitMap_stage`,
    `heisenbergFiniteModeColimitMap_surjective`,
    `heisenbergFiniteModeColimitMap_injective`,
    `heisenbergFiniteModeColimitMap_bijective`,
    `heisenbergFiniteModeColimitEquiv`: linear isomorphism with `HeisenbergAlgebra 𝕜`.
  * `heisenbergColimitLieRing`, `heisenbergColimitLieAlgebra`,
    `heisenbergFiniteModeColimitLieEquiv`, `heisenbergFiniteModeColimitMap_map_lie`,
    `heisenbergCentralColimitMode`, `heisenbergFiniteModeColimitMap_central`:
    full `LieEquiv` between `heisenbergFiniteModeColimit` and `HeisenbergAlgebra 𝕜`.
-/

noncomputable section

namespace InfoGeometry.Canonical

open CategoryTheory CategoryTheory.Limits
open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Filtered diagram of finite-support Heisenberg submodules in `ModuleCat 𝕜`
indexed by `Finset (Option ℤ)`. -/
noncomputable def heisenbergFiniteModeDiagram :
    Finset (Option ℤ) ⥤ ModuleCat 𝕜 where
  obj s := ModuleCat.of 𝕜 (heisenbergFiniteModeStage (𝕜 := 𝕜) s)
  map := by
    intro s t f
    have hst : s ≤ t := f.down.down
    exact ModuleCat.ofHom <|
      Submodule.inclusion (by
        apply Submodule.span_mono
        rintro x ⟨i, hi, rfl⟩
        exact ⟨i, ⟨hst hi, rfl⟩⟩)
  map_id s := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- Canonical cocone from `heisenbergFiniteModeDiagram` into `HeisenbergAlgebra 𝕜`. -/
noncomputable def heisenbergFiniteModeCocone :
    Cocone (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) where
  pt := ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜)
  ι := {
    app := fun s => ModuleCat.ofHom (Submodule.subtype _)
    naturality := by
      intro s t f
      ext x
      rfl }

/-- Categorical finite-mode colimit of the Heisenberg algebra in `ModuleCat 𝕜`. -/
abbrev heisenbergFiniteModeColimit : ModuleCat 𝕜 :=
  colimit (heisenbergFiniteModeDiagram (𝕜 := 𝕜))

/-- Comparison morphism in `ModuleCat 𝕜` from `heisenbergFiniteModeColimit`
to `HeisenbergAlgebra 𝕜`. -/
noncomputable def heisenbergFiniteModeColimitMap :
    heisenbergFiniteModeColimit (𝕜 := 𝕜) ⟶
      ModuleCat.of 𝕜 (HeisenbergAlgebra 𝕜) :=
  colimit.desc _ (heisenbergFiniteModeCocone (𝕜 := 𝕜))

/-- Stage factorization law for `heisenbergFiniteModeColimitMap`. -/
theorem heisenbergFiniteModeColimitMap_stage (s : Finset (Option ℤ)) :
    colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s ≫
        heisenbergFiniteModeColimitMap (𝕜 := 𝕜) =
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s := by
  dsimp [heisenbergFiniteModeColimitMap]
  exact colimit.ι_desc _ _

/-- Surjectivity of `(heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom`, proved from
finite-support basis exhaustion `heisenberg_mem_finiteModeStage`. -/
theorem heisenbergFiniteModeColimitMap_surjective :
    Function.Surjective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  intro X
  rcases heisenberg_mem_finiteModeStage (𝕜 := 𝕜) X with ⟨s, hX⟩
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s := ⟨X, hX⟩
  refine ⟨(colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x, ?_⟩
  have hstage := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have hstage' := congrArg (fun f => f.hom) hstage
  exact congrArg (fun f => f x) hstage'

/-- Injectivity of `(heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom`, proved via
filtered colimit preservation in `ModuleCat 𝕜`. -/
theorem heisenbergFiniteModeColimitMap_injective :
    Function.Injective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  let F := heisenbergFiniteModeDiagram (𝕜 := 𝕜)
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat 𝕜)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits
      (forget (ModuleCat 𝕜))
  have : PreservesColimit F (forget (ModuleCat 𝕜)) :=
    PreservesColimitsOfShape.preservesColimit
  intro x y hxy
  obtain ⟨s, a, hxa⟩ := Concrete.colimit_exists_rep F x
  obtain ⟨t, b, hby⟩ := Concrete.colimit_exists_rep F y
  rw [← hxa, ← hby] at hxy
  have hxy' :
      (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app s a =
        (heisenbergFiniteModeCocone (𝕜 := 𝕜)).ι.app t b := by
    have hs := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
    have ht := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) t
    have hs' := congrArg (fun f => f.hom a) hs
    have ht' := congrArg (fun f => f.hom b) ht
    exact hs'.symm.trans (hxy.trans ht')
  let k := s ∪ t
  let f : s ⟶ k := ⟨PLift.up Finset.subset_union_left⟩
  let g : t ⟶ k := ⟨PLift.up Finset.subset_union_right⟩
  have hfg : F.map f a = F.map g b := by
    apply Subtype.ext
    exact hxy'
  have hcol :
      colimit.ι F s a = colimit.ι F t b :=
    Concrete.colimit_rep_eq_of_exists F a b ⟨k, f, g, hfg⟩
  exact hxa.symm.trans (hcol.trans hby)

/-- Bijectivity of `(heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom`. -/
theorem heisenbergFiniteModeColimitMap_bijective :
    Function.Bijective
      (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom := by
  rw [Function.Bijective]
  exact ⟨heisenbergFiniteModeColimitMap_injective (𝕜 := 𝕜),
    heisenbergFiniteModeColimitMap_surjective (𝕜 := 𝕜)⟩

/-- Canonical `𝕜`-linear equivalence between the `ModuleCat 𝕜` colimit
`heisenbergFiniteModeColimit` and `HeisenbergAlgebra 𝕜`. -/
noncomputable def heisenbergFiniteModeColimitEquiv :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) ≃ₗ[𝕜]
      HeisenbergAlgebra 𝕜 :=
  LinearEquiv.ofBijective
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
    (heisenbergFiniteModeColimitMap_bijective (𝕜 := 𝕜))

/-- Transported `LieRing` instance on `heisenbergFiniteModeColimit` across
`heisenbergFiniteModeColimitEquiv`, using explicit `change` steps and
`LinearEquiv.apply_symm_apply` to avoid `simp` recursion. -/
noncomputable instance heisenbergColimitLieRing :
    LieRing (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) where
  bracket x y :=
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)).symm
      ⁅heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) x,
        heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) y⁆
  add_lie x y z := by
    let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
    change eqv.symm ⁅eqv (x + y), eqv z⁆ = eqv.symm ⁅eqv x, eqv z⁆ + eqv.symm ⁅eqv y, eqv z⁆
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
    change eqv.symm ⁅eqv x, eqv (y + z)⁆ = eqv.symm ⁅eqv x, eqv y⁆ + eqv.symm ⁅eqv x, eqv z⁆
    rw [map_add, lie_add, map_add]
  lie_self x := by
    let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
    change eqv.symm ⁅eqv x, eqv x⁆ = 0
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
    change eqv.symm ⁅eqv x, eqv (eqv.symm ⁅eqv y, eqv z⁆)⁆ =
      eqv.symm ⁅eqv (eqv.symm ⁅eqv x, eqv y⁆), eqv z⁆ +
        eqv.symm ⁅eqv y, eqv (eqv.symm ⁅eqv x, eqv z⁆)⁆
    simp only [LinearEquiv.apply_symm_apply]
    rw [leibniz_lie, map_add]

/-- Transported `LieAlgebra 𝕜` instance on `heisenbergFiniteModeColimit`. -/
noncomputable instance heisenbergColimitLieAlgebra :
    LieAlgebra 𝕜 (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) where
  lie_smul r x y := by
    let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
    change eqv.symm ⁅eqv x, eqv (r • y)⁆ = r • eqv.symm ⁅eqv x, eqv y⁆
    rw [map_smul, lie_smul, map_smul]

/-- Canonical `LieEquiv` between the categorical `ModuleCat 𝕜` colimit
`heisenbergFiniteModeColimit` and `HeisenbergAlgebra 𝕜`. -/
noncomputable def heisenbergFiniteModeColimitLieEquiv :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) ≃ₗ⁅𝕜⁆
      HeisenbergAlgebra 𝕜 :=
  { heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) with
    map_lie' := by
      intro x y
      let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
      change eqv (eqv.symm ⁅eqv x, eqv y⁆) = ⁅eqv x, eqv y⁆
      exact eqv.apply_symm_apply _ }

/-- The comparison map `(heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom` preserves
the transported Lie bracket on `heisenbergFiniteModeColimit`. -/
theorem heisenbergFiniteModeColimitMap_map_lie
    (u v : (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _)) :
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom ⁅u, v⁆ =
      ⁅(heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom u,
        (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom v⁆ := by
  let eqv := heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
  change eqv (eqv.symm ⁅eqv u, eqv v⁆) = ⁅eqv u, eqv v⁆
  exact eqv.apply_symm_apply _

/-- Canonical singleton colimit representative of the central generator `K` in
stage `{none}`. -/
noncomputable def heisenbergCentralColimitMode :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  let s : Finset (Option ℤ) := {none}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.kgen 𝕜, heisenberg_mode_stage_contains_kgen (𝕜 := 𝕜)⟩
  (colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x

/-- The central colimit representative `heisenbergCentralColimitMode` maps to
`HeisenbergAlgebra.kgen 𝕜` under `heisenbergFiniteModeColimitMap`. -/
theorem heisenbergFiniteModeColimitMap_central :
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        (heisenbergCentralColimitMode (𝕜 := 𝕜)) =
      HeisenbergAlgebra.kgen 𝕜 := by
  let s : Finset (Option ℤ) := {none}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.kgen 𝕜, heisenberg_mode_stage_contains_kgen (𝕜 := 𝕜)⟩
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = _
  have h := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have hstage := congrArg (fun f => f.hom) h
  exact congrArg (fun g => g x) hstage

end InfoGeometry.Canonical

end noncomputable section
