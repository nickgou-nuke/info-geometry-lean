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
  · let f : colimit (affineFiniteModeDiagram Φ hΦ hΦs) ⟶
        ModuleCat.of 𝕜 (affineFiniteModeUnion Φ hΦ hΦs) :=
      colimit.desc (affineFiniteModeDiagram Φ hΦ hΦs) (unionCocone Φ hΦ hΦs)
    have h_fac : f ≫ ModuleCat.ofHom (Submodule.subtype (affineFiniteModeUnion Φ hΦ hΦs)) = (affineFiniteModeColimitMap Φ hΦ hΦs) := by
      apply colimit.hom_ext
      intro j
      have h1 : ModuleCat.ofHom (Submodule.inclusion
          (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j)) ≫
          ModuleCat.ofHom (Submodule.subtype
            (⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N)) =
          (affineFiniteModeCocone Φ hΦ hΦs).ι.app j := by
        apply ModuleCat.hom_ext
        change (Submodule.subtype
              (⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N)).comp
            (Submodule.inclusion
              (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j)) =
          (Submodule.subtype (affineFiniteModeStage Φ hΦ hΦs j))
        exact Submodule.subtype_comp_inclusion
          (affineFiniteModeStage Φ hΦ hΦs j)
          (⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N)
          (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j)
      have h2 : colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫
          (affineFiniteModeColimitMap Φ hΦ hΦs) =
          (affineFiniteModeCocone Φ hΦ hΦs).ι.app j :=
        affineFiniteModeColimitMap_stage Φ hΦ hΦs j
      have hdesc : colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫ f =
          ModuleCat.ofHom (Submodule.inclusion
            (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j)) := by
        change colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫
          colimit.desc (affineFiniteModeDiagram Φ hΦ hΦs)
            (unionCocone Φ hΦ hΦs) = ModuleCat.ofHom (Submodule.inclusion
              (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j))
        exact colimit.ι_desc (unionCocone Φ hΦ hΦs) j
      change (colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫ f) ≫
          ModuleCat.ofHom (Submodule.subtype
            (⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N)) =
        colimit.ι (affineFiniteModeDiagram Φ hΦ hΦs) j ≫ affineFiniteModeColimitMap Φ hΦ hΦs
      rw [hdesc, h2]
      change ModuleCat.ofHom (Submodule.inclusion
          (le_iSup (fun N => affineFiniteModeStage Φ hΦ hΦs N) j)) ≫
          ModuleCat.ofHom (Submodule.subtype
            (⨆ N : ℕ, affineFiniteModeStage Φ hΦ hΦs N)) =
        ModuleCat.ofHom (Submodule.subtype (affineFiniteModeStage Φ hΦ hΦs j))
      exact h1
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

/-- Every element of the affine Kac--Moody carrier is a finite linear
combination of the central generator and current modes.  The loop-algebra
component is finitely supported in its mode index, so it lies in one cutoff;
the central component already lies in every cutoff. -/
theorem affineFiniteModeUnion_eq_top :
    affineFiniteModeUnion Φ hΦ hΦs = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro Z
  let loopLift :
      LieAlgebra.loopAlgebra 𝕜 ℤ 𝓰 →ₗ[𝕜] KM Φ hΦ hΦs :=
    { toFun := fun X => ⟨X, 0⟩
      map_add' := by
        intro X Y
        ext <;> simp [LieTwoCocycle.CentralExtension.add_def]
      map_smul' := by
        intro c X
        ext <;> simp [LieTwoCocycle.CentralExtension.smul_def] }
  let coordinateLift : (ℤ →₀ 𝓰) →ₗ[𝕜] KM Φ hΦ hΦs :=
    loopLift.comp (LieAlgebra.LoopAlgebra.toFinsupp 𝕜 ℤ 𝓰).symm.toLinearMap
  have hcoordinate (f : ℤ →₀ 𝓰) : coordinateLift f ∈
      affineFiniteModeUnion Φ hΦ hΦs := by
    induction f using Finsupp.induction_linear with
    | zero =>
        simp [coordinateLift]
    | add f g hf hg =>
        rw [map_add]
        exact (affineFiniteModeUnion Φ hΦ hΦs).add_mem hf hg
    | single n x =>
        have hmode :
            affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (-n) x ∈
              affineFiniteModeStage Φ hΦ hΦs (Int.natAbs (-n)) :=
          affineCurrentGen_mem_stage Φ hΦ hΦs (Int.natAbs (-n)) (-n) x le_rfl
        have hmodeUnion := Submodule.mem_iSup_of_mem
          (Int.natAbs (-n)) hmode
        simpa [coordinateLift, loopLift, affineCurrentGen, affineLoopMode,
          affineFiniteModeUnion] using hmodeUnion
  have hloop : (⟨Z.fst, 0⟩ : KM Φ hΦ hΦs) ∈
      affineFiniteModeUnion Φ hΦ hΦs := by
    have h := hcoordinate
      (LieAlgebra.LoopAlgebra.toFinsupp 𝕜 ℤ 𝓰 Z.fst)
    simpa [coordinateLift, loopLift] using h
  have hcentral : (⟨0, Z.snd⟩ : KM Φ hΦ hΦs) ∈
      affineFiniteModeUnion Φ hΦ hΦs := by
    have hgen : affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs ∈
        affineFiniteModeUnion Φ hΦ hΦs :=
      Submodule.mem_iSup_of_mem 0 (affineCentralGen_mem_stage Φ hΦ hΦs 0)
    have hscaled := (affineFiniteModeUnion Φ hΦ hΦs).smul_mem Z.snd hgen
    simpa [affineCentralGen, LieTwoCocycle.CentralExtension.smul_def] using hscaled
  have hdecomp : (⟨Z.fst, 0⟩ : KM Φ hΦ hΦs) + ⟨0, Z.snd⟩ = Z := by
    rw [LieTwoCocycle.CentralExtension.add_def]
    cases Z
    simp
  rw [← hdecomp]
  exact (affineFiniteModeUnion Φ hΦ hΦs).add_mem hloop hcentral

/-- The Lie subalgebra carried by the finite-mode union is the full affine
Kac--Moody algebra. -/
theorem affineFiniteModeColimitLieSubalgebra_eq_top :
    affineFiniteModeColimitLieSubalgebra Φ hΦ hΦs = ⊤ := by
  apply LieSubalgebra.ext
  intro X
  simp [affineFiniteModeColimitLieSubalgebra,
    affineFiniteModeUnion_eq_top Φ hΦ hΦs]

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
    let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
    change eqv.symm ⁅eqv (x + y), eqv z⁆ = eqv.symm ⁅eqv x, eqv z⁆ + eqv.symm ⁅eqv y, eqv z⁆
    rw [map_add, add_lie, map_add]
  lie_add x y z := by
    let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
    change eqv.symm ⁅eqv x, eqv (y + z)⁆ = eqv.symm ⁅eqv x, eqv y⁆ + eqv.symm ⁅eqv x, eqv z⁆
    rw [map_add, lie_add, map_add]
  lie_self x := by
    let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
    change eqv.symm ⁅eqv x, eqv x⁆ = 0
    rw [lie_self, map_zero]
  leibniz_lie x y z := by
    let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
    change eqv.symm ⁅eqv x, eqv (eqv.symm ⁅eqv y, eqv z⁆)⁆ = eqv.symm ⁅eqv (eqv.symm ⁅eqv x, eqv y⁆), eqv z⁆ + eqv.symm ⁅eqv y, eqv (eqv.symm ⁅eqv x, eqv z⁆)⁆
    simp only [LinearEquiv.apply_symm_apply]
    rw [leibniz_lie, map_add]

noncomputable instance colimitLieAlgebra : LieAlgebra 𝕜 (affineFiniteModeColimit Φ hΦ hΦs) where
  lie_smul r x y := by
    let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
    change eqv.symm ⁅eqv x, eqv (r • y)⁆ = r • eqv.symm ⁅eqv x, eqv y⁆
    rw [map_smul, lie_smul, map_smul]

noncomputable def colimitLieEquiv :
    (affineFiniteModeColimit Φ hΦ hΦs) ≃ₗ⁅𝕜⁆ (affineFiniteModeColimitLieSubalgebra Φ hΦ hΦs) :=
  { colimitEquivLieSubalgebra Φ hΦ hΦs with
    map_lie' := by
      intro x y
      let eqv := colimitEquivLieSubalgebra Φ hΦ hΦs
      change eqv (eqv.symm ⁅eqv x, eqv y⁆) = ⁅eqv x, eqv y⁆
      exact eqv.apply_symm_apply _
  }

/-- The finite-mode module colimit is Lie-equivalent to the full affine
Kac--Moody carrier.  This uses the finite-support spanning theorem above. -/
noncomputable def colimitLieEquivAmbient :
    (affineFiniteModeColimit Φ hΦ hΦs) ≃ₗ⁅𝕜⁆ KM Φ hΦ hΦs :=
  (colimitLieEquiv Φ hΦ hΦs).trans
    ((LieEquiv.ofEq
      (affineFiniteModeColimitLieSubalgebra Φ hΦ hΦs)
      (⊤ : LieSubalgebra 𝕜 (KM Φ hΦ hΦs))
      (by rw [affineFiniteModeColimitLieSubalgebra_eq_top Φ hΦ hΦs])).trans
      LieSubalgebra.topEquiv)

/-- The Lie equivalence on the categorical colimit is the canonical
ModuleCat comparison map after forgetting its Lie structure. -/
theorem colimitLieEquivAmbient_apply (x : affineFiniteModeColimit Φ hΦ hΦs) :
    colimitLieEquivAmbient Φ hΦ hΦs x =
      (affineFiniteModeColimitMap Φ hΦ hΦs).hom x := by
  change ((colimitEquivUnion Φ hΦ hΦs x :
    affineFiniteModeUnion Φ hΦ hΦs) : KM Φ hΦ hΦs) = _
  rfl
