import InfoGeometry.Canonical.FixedIndexCuntzStarTower

/-!
# Modular-flow descent for fixed-index Cuntz towers

This is the categorical part of a modular-flow construction.  A family of
stagewise `StarAlgEquiv`s is supplied together with its transition naturality;
`colim.map` then descends it to the complex module colimit.  No analytic
Tomita generator is asserted by this file.
-/

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open FilteredColimit.Native

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)

abbrev stageModuleDiagram : ℕ ⥤ ModuleCat ℂ :=
  FilteredColimit.Native.moduleDiagram
    ((FixedIndexCuntzStarTower.Data.toContinuousStarInductiveSystem
      (Stage := Stage) T).toDirectInductiveSystem)

/-- A natural stagewise star flow compatible with the fixed-index tower. -/
structure FlowData where
  flow : ∀ n, ℝ → Stage n ≃⋆ₐ[ℂ] Stage n
  flow_add : ∀ n t s a, flow n (t + s) a = flow n t (flow n s a)
  map_naturality : ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
    T.map hmn (flow m t a) = flow n t (T.map hmn a)

variable (Φ : FlowData Stage T)

theorem flow_zero (n : ℕ) (a : Stage n) :
    Φ.flow n 0 a = a := by
  have h := Φ.flow_add n (1 : ℝ) 0 a
  have h' : Φ.flow n 1 a = Φ.flow n 1 (Φ.flow n 0 a) := by
    simpa using h
  exact (Φ.flow n 1).injective h'.symm

def flowNatTrans (t : ℝ) :
    stageModuleDiagram Stage T ⟶ stageModuleDiagram Stage T where
  app n := ModuleCat.ofHom ((Φ.flow n t).toAlgEquiv.toLinearMap)
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext a
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    simpa [stageModuleDiagram] using
      (Φ.map_naturality (leOfHom f) t a).symm

def flowColimitMap (t : ℝ) :
    (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ⟶
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
  colim.map (flowNatTrans Stage T Φ t)

@[simp] theorem flowColimitMap_inclusion (t : ℝ) (n : ℕ) (a : Stage n) :
    flowColimitMap Stage T Φ t
        ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
      (colimit.ι (stageModuleDiagram Stage T) n).hom (Φ.flow n t a) := by
  have hι := colimit.ι_map (flowNatTrans Stage T Φ t) n
  exact congrArg (fun f => f a) hι

theorem flowColimitMap_zero :
    flowColimitMap Stage T Φ 0 = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  change flowColimitMap Stage T Φ 0
      ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
    (colimit.ι (stageModuleDiagram Stage T) n).hom a
  rw [flowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (flow_zero (Stage := Stage) (T := T) Φ n a)

theorem flowColimitMap_add (t s : ℝ) :
    flowColimitMap Stage T Φ (t + s) =
      flowColimitMap Stage T Φ s ≫ flowColimitMap Stage T Φ t := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  simp only [ModuleCat.comp_apply]
  rw [flowColimitMap_inclusion, flowColimitMap_inclusion,
    flowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (Φ.flow_add n t s a)

theorem flowColimitMap_right_inverse (t : ℝ) :
    flowColimitMap Stage T Φ t ≫ flowColimitMap Stage T Φ (-t) = 𝟙 _ := by
  rw [← flowColimitMap_add Stage T Φ (-t) t]
  simpa using flowColimitMap_zero Stage T Φ

theorem flowColimitMap_left_inverse (t : ℝ) :
    flowColimitMap Stage T Φ (-t) ≫ flowColimitMap Stage T Φ t = 𝟙 _ := by
  rw [← flowColimitMap_add Stage T Φ t (-t)]
  simpa using flowColimitMap_zero Stage T Φ

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
