import InfoGeometry.Canonical.CuntzStageModularFlow

/-!
# Categorical descent of the Cuntz stagewise modular flow

The stagewise naturality equation is converted into a native `ModuleCat ℂ`
natural transformation.  `colim.map` then supplies the induced linear map on
the categorical colimit.  The construction is algebraic and makes no claim
about analytic generators or boundedness.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlowColimit

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlow.CuntzStageModularFlowLemmas

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage T)

/-- The underlying complex-linear diagram of the supplied star-inductive
system. -/
def stageModuleDiagram : ℕ ⥤ ModuleCat ℂ where
  obj n := ModuleCat.of ℂ (Stage n)
  map f := ModuleCat.ofHom
    ((T.map (leOfHom f)).toAlgHom.toLinearMap)
  map_id n := by
    apply ModuleCat.hom_ext
    ext x
    simp [T.map_id]
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    exact congr_fun (congrArg DFunLike.coe (T.map_comp (leOfHom f) (leOfHom g)).symm) x

/-- The stagewise flow is a natural transformation of complex module
diagrams. -/
def modularFlowNatTrans (t : ℝ) :
    stageModuleDiagram Stage T ⟶ stageModuleDiagram Stage T where
  app n := ModuleCat.ofHom
    ((Φ.flow n t).toAlgEquiv.toLinearMap)
  naturality := by
    intro m n f
    dsimp [stageModuleDiagram]
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    ext a
    exact (Φ.map_naturality (leOfHom f) t a).symm

/-- The induced complex-linear modular-flow map on the categorical colimit. -/
def modularFlowColimitMap (t : ℝ) :
    (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ⟶
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
  colim.map (modularFlowNatTrans Stage T Φ t)

@[simp] theorem modularFlowColimitMap_inclusion
    (t : ℝ) (n : ℕ) (a : Stage n) :
    (modularFlowColimitMap Stage T Φ t).hom
        ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
      (colimit.ι (stageModuleDiagram Stage T) n).hom (Φ.flow n t a) := by
  have hι := colimit.ι_map (modularFlowNatTrans Stage T Φ t) n
  have h_hom : (colimit.ι (stageModuleDiagram Stage T) n ≫ modularFlowColimitMap Stage T Φ t).hom =
      ((modularFlowNatTrans Stage T Φ t).app n ≫ colimit.ι (stageModuleDiagram Stage T) n).hom :=
    congrArg ModuleCat.Hom.hom hι
  have h_app := LinearMap.congr_fun h_hom a
  exact h_app

theorem modularFlowColimitMap_zero :
    modularFlowColimitMap Stage T Φ 0 = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  dsimp [stageModuleDiagram]
  ext a
  change (modularFlowColimitMap Stage T Φ 0).hom ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
    (colimit.ι (stageModuleDiagram Stage T) n).hom a
  rw [modularFlowColimitMap_inclusion]
  rw [Φ.flow_zero n a]

theorem modularFlowColimitMap_add (t s : ℝ) :
    modularFlowColimitMap Stage T Φ (t + s) =
      modularFlowColimitMap Stage T Φ s ≫
        modularFlowColimitMap Stage T Φ t := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  dsimp [stageModuleDiagram]
  ext a
  change (modularFlowColimitMap Stage T Φ (t + s)).hom ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
    (modularFlowColimitMap Stage T Φ t).hom ((modularFlowColimitMap Stage T Φ s).hom ((colimit.ι (stageModuleDiagram Stage T) n).hom a))
  rw [modularFlowColimitMap_inclusion]
  rw [Φ.flow_add n t s a]
  rw [modularFlowColimitMap_inclusion, modularFlowColimitMap_inclusion]

end InfoGeometry.Canonical.CuntzStageModularFlowColimit
