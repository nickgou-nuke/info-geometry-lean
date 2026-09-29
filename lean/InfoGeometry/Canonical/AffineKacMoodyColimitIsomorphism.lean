import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit
import InfoGeometry.Canonical.AffineKacMoodyColimitBracket

open CategoryTheory CategoryTheory.Limits
open VirasoroProject InfoGeometry.Canonical.AffineKacMoodyFiniteModeColimit

universe u
variable {𝕜 : Type u} [Field 𝕜] [CharZero 𝕜]
variable {𝓰 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
variable (Φ : LinearMap.BilinForm 𝕜 𝓰)
variable (hΦ : Φ.lieInvariant 𝓰) (hΦs : Φ.IsSymm)

noncomputable def isoColimit : (colimit (affineFiniteModeDiagram Φ hΦ hΦs)) ≅ 
  (ModuleCat.FilteredColimits.colimitCocone (affineFiniteModeDiagram Φ hΦ hΦs)).pt :=
  (colimit.isColimit (affineFiniteModeDiagram Φ hΦ hΦs)).coconePointUniqueUpToIso 
  (ModuleCat.FilteredColimits.colimitCoconeIsColimit (affineFiniteModeDiagram Φ hΦ hΦs))

lemma colimit_exists_rep_hack (x : ↑(colimit (affineFiniteModeDiagram Φ hΦ hΦs))) : 
    ∃ (N : ℕ) (z : (affineFiniteModeDiagram Φ hΦ hΦs).obj N), 
      x = (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom z := by
  let y := (isoColimit Φ hΦ hΦs).hom x
  have hrep := ModuleCat.FilteredColimits.M.mk_surjective (affineFiniteModeDiagram Φ hΦ hΦs) y
  rcases hrep with ⟨N, z, hz⟩
  use N, z
  have hx : x = (isoColimit Φ hΦ hΦs).inv y := by
    dsimp [y]
    have h_id : (isoColimit Φ hΦ hΦs).hom ≫ (isoColimit Φ hΦ hΦs).inv = 𝟙 _ := (isoColimit Φ hΦ hΦs).hom_inv_id
    have h_eval : (ModuleCat.Hom.hom ((isoColimit Φ hΦ hΦs).hom ≫ (isoColimit Φ hΦ hΦs).inv)) x = x := by
      exact congrArg (fun F => ModuleCat.Hom.hom F x) h_id
    exact h_eval.symm
  rw [hx, ← hz]
  have h_mk : ModuleCat.FilteredColimits.M.mk (affineFiniteModeDiagram Φ hΦ hΦs) ⟨N, z⟩ = 
    ((ModuleCat.FilteredColimits.colimitCocone (affineFiniteModeDiagram Φ hΦ hΦs)).ι.app N).hom z := rfl
  rw [h_mk]
  have h_fac := (ModuleCat.FilteredColimits.colimitCoconeIsColimit (affineFiniteModeDiagram Φ hΦ hΦs)).fac (colimit.cocone (affineFiniteModeDiagram Φ hΦ hΦs)) N
  have h_fac2 : ((ModuleCat.FilteredColimits.colimitCocone (affineFiniteModeDiagram Φ hΦ hΦs)).ι.app N) ≫ (isoColimit Φ hΦ hΦs).inv = (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N) := h_fac
  have h_eval : (isoColimit Φ hΦ hΦs).inv.hom (((ModuleCat.FilteredColimits.colimitCocone (affineFiniteModeDiagram Φ hΦ hΦs)).ι.app N).hom z) = 
                (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom z := by
    exact congrArg (fun F => ModuleCat.Hom.hom F z) h_fac2
  exact h_eval

theorem colimitMap_injective : 
    Function.Injective (affineFiniteModeColimitMap Φ hΦ hΦs).hom := by
  intro x y hxy
  have h_diff : (affineFiniteModeColimitMap Φ hΦ hΦs).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hrep := colimit_exists_rep_hack Φ hΦ hΦs (x - y)
  rcases hrep with ⟨N, z, hz⟩
  have h_stage := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
  have h_eval : (affineFiniteModeColimitMap Φ hΦ hΦs).hom ((colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom z) = z.1 := by
    exact congrArg (fun F => ModuleCat.Hom.hom F z) h_stage
  rw [← hz, h_diff] at h_eval
  have hz_zero : z = 0 := Subtype.ext h_eval.symm
  have hx_sub_y : x - y = 0 := by
    rw [hz, hz_zero, map_zero]
  exact sub_eq_zero.mp hx_sub_y

noncomputable def unionCocone : Cocone (affineFiniteModeDiagram Φ hΦ hΦs) where
  pt := ModuleCat.of 𝕜 (affineFiniteModeUnion Φ hΦ hΦs)
  ι := {
    app := fun N => 
      let inc := Submodule.inclusion (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) N)
      ModuleCat.ofHom inc
    naturality := fun N M h => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  }

theorem colimitMap_range_eq_union :
    LinearMap.range (affineFiniteModeColimitMap Φ hΦ hΦs).hom = 
      affineFiniteModeUnion Φ hΦ hΦs := by
  apply le_antisymm
  · let f := colimit.desc (affineFiniteModeDiagram Φ hΦ hΦs) (unionCocone Φ hΦ hΦs)
    have h_fac : f ≫ ModuleCat.ofHom (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) = (affineFiniteModeColimitMap Φ hΦ hΦs) := by
      apply colimit.hom_ext
      intro j
      have h1 : (unionCocone Φ hΦ hΦs).ι.app j ≫ ModuleCat.ofHom (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) = (affineFiniteModeCocone Φ hΦ hΦs).ι.app j := by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
      have h2 : colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫ (affineFiniteModeColimitMap Φ hΦ hΦs) = (affineFiniteModeCocone Φ hΦ hΦs).ι.app j := affineFiniteModeColimitMap_stage Φ hΦ hΦs j
      rw [← Category.assoc, colimit.ι_desc, h1, h2]
    intro x hx
    rcases hx with ⟨y, rfl⟩
    have h_eval : (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) (f.hom y) = (affineFiniteModeColimitMap Φ hΦ hΦs).hom y := by
      exact congrArg (fun F => ModuleCat.Hom.hom F y) h_fac
    rw [← h_eval]
    exact Subtype.mem (f.hom y)
  · apply iSup_le
    intro N X hX
    have hstage := affineFiniteModeColimitMap_stage Φ hΦ hΦs N
    let y : affineFiniteModeStage Φ hΦ hΦs N := ⟨X, hX⟩
    use (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) N).hom y
    exact congrArg (fun F => ModuleCat.Hom.hom F y) hstage

noncomputable def colimitEquivUnion :
    (affineFiniteModeColimit Φ hΦ hΦs) ≃ₗ[𝕜] (affineFiniteModeUnion Φ hΦ hΦs) :=
  LinearEquiv.ofBijective 
    (LinearMap.codRestrict (affineFiniteModeUnion Φ hΦ hΦs) (affineFiniteModeColimitMap Φ hΦ hΦs).hom 
      (fun x => by 
        have h := colimitMap_range_eq_union Φ hΦ hΦs
        rw [← h]
        exact LinearMap.mem_range_self _ _))
    ⟨fun x y h => colimitMap_injective Φ hΦ hΦs (Subtype.ext_iff.mp h),
     fun ⟨y, hy⟩ => by
       have h := colimitMap_range_eq_union Φ hΦ hΦs
       rw [← h] at hy
       rcases hy with ⟨x, rfl⟩
       use x
       rfl⟩

noncomputable def colimitEquivLieSubalgebra :
    (affineFiniteModeColimit Φ hΦ hΦs) ≃ₗ[𝕜] (affineFiniteModeColimitLieSubalgebra Φ hΦ hΦs) :=
  colimitEquivUnion Φ hΦ hΦs

noncomputable instance colimitLieRing : LieRing (affineFiniteModeColimit Φ hΦ hΦs) where
  bracket x y := (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅colimitEquivLieSubalgebra Φ hΦ hΦs x, colimitEquivLieSubalgebra Φ hΦ hΦs y⁆
  add_lie x y z := by
    change (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅colimitEquivLieSubalgebra Φ hΦ hΦs (x + y), colimitEquivLieSubalgebra Φ hΦ hΦs z⁆ = _
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    change (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅colimitEquivLieSubalgebra Φ hΦ hΦs x, colimitEquivLieSubalgebra Φ hΦ hΦs (y + z)⁆ = _
    rw [map_add, lie_add, map_add]
  lie_self x := by
    change (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅colimitEquivLieSubalgebra Φ hΦ hΦs x, colimitEquivLieSubalgebra Φ hΦ hΦs x⁆ = _
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    change (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅_, _⁆ = (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅_, _⁆ + (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅_, _⁆
    simp only [LinearEquiv.apply_symm_apply]
    rw [leibniz_lie, map_add]

noncomputable instance colimitLieAlgebra : LieAlgebra 𝕜 (affineFiniteModeColimit Φ hΦ hΦs) where
  lie_smul r x y := by
    change (colimitEquivLieSubalgebra Φ hΦ hΦs).symm ⁅_, _⁆ = r • _
    have h_symm_apply := (colimitEquivLieSubalgebra Φ hΦ hΦs).apply_symm_apply
    rw [map_smul, lie_smul, map_smul]

noncomputable def colimitLieEquiv :
    (affineFiniteModeColimit Φ hΦ hΦs) ≃ₗ⁅𝕜⁆ (affineFiniteModeColimitLieSubalgebra Φ hΦ hΦs) :=
  { colimitEquivLieSubalgebra Φ hΦ hΦs with
    map_lie' := by
      intro x y
      change (colimitEquivLieSubalgebra Φ hΦ hΦs) ((colimitEquivLieSubalgebra Φ hΦ hΦs).symm _) = _
      exact (colimitEquivLieSubalgebra Φ hΦ hΦs).apply_symm_apply _
  }
