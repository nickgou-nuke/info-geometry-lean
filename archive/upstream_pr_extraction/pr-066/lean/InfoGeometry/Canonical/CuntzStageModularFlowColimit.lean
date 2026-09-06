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

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.CuntzStageModularFlow.CuntzStageModularFlowLemmas

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage)

/-- The underlying complex-linear diagram of the supplied star-inductive
system. -/
def stageModuleDiagram : ℕ ⥤ ModuleCat ℂ where
  obj n := ModuleCat.of ℂ (Stage n)
  map f := ModuleCat.ofHom
    ((T.map (leOfHom f)).toAlgHom.toLinearMap)
  map_id n := by
    apply ModuleCat.hom_ext
    change (T.map (le_refl n)).toAlgHom.toLinearMap = LinearMap.id
    rw [T.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change
      (T.map (le_trans (leOfHom f) (leOfHom g))).toAlgHom.toLinearMap =
        ((T.map (leOfHom g)).toAlgHom.toLinearMap).comp
          ((T.map (leOfHom f)).toAlgHom.toLinearMap)
    have h := congrArg
      (fun e : Stage _ →⋆ₐ[ℂ] Stage _ => e.toAlgHom.toLinearMap)
      (T.map_comp (leOfHom f) (leOfHom g)).symm
    simpa [StarAlgHom.comp_apply, AlgHom.comp_apply, LinearMap.comp_apply] using h

/-- The stagewise flow is a natural transformation of complex module
diagrams. -/
def modularFlowNatTrans
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    stageModuleDiagram Stage T ⟶ stageModuleDiagram Stage T where
  app n := ModuleCat.ofHom
    ((Φ.flow n t).toAlgEquiv.toLinearMap)
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext a
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    simpa [stageModuleDiagram] using
      (hmap_naturality (leOfHom f) t a).symm

/-- The induced complex-linear modular-flow map on the categorical colimit. -/
def modularFlowColimitMap
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ⟶
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
  colim.map (modularFlowNatTrans Stage T Φ hmap_naturality t)

@[simp] theorem modularFlowColimitMap_inclusion
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) (n : ℕ) (a : Stage n) :
    modularFlowColimitMap Stage T Φ hmap_naturality t
        ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
      (colimit.ι (stageModuleDiagram Stage T) n).hom (Φ.flow n t a) := by
  have hι := colimit.ι_map (modularFlowNatTrans Stage T Φ hmap_naturality t) n
  exact congrArg (fun f => f a) hι

theorem modularFlowColimitMap_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a)) :
    modularFlowColimitMap Stage T Φ hmap_naturality 0 = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  change modularFlowColimitMap Stage T Φ hmap_naturality 0
      ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
    (colimit.ι (stageModuleDiagram Stage T) n).hom a
  rw [modularFlowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (CuntzStageModularFlowLemmas.flow_zero
      (Stage := Stage) Φ hflow_add n a)

theorem modularFlowColimitMap_add
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t s : ℝ) :
    modularFlowColimitMap Stage T Φ hmap_naturality (t + s) =
      modularFlowColimitMap Stage T Φ hmap_naturality s ≫
        modularFlowColimitMap Stage T Φ hmap_naturality t := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  simp only [ModuleCat.comp_apply]
  rw [modularFlowColimitMap_inclusion, modularFlowColimitMap_inclusion,
    modularFlowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (hflow_add n t s a)

end InfoGeometry.Canonical.CuntzStageModularFlowColimit
