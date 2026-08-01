import InfoGeometry.Canonical.FixedIndexCuntzStarTower

/-!
# Modular-flow descent for fixed-index Cuntz towers

A family of stagewise `StarAlgEquiv`s is supplied together with its transition
naturality and additive-time law as explicit theorem arguments.  `colim.map`
then descends the family to the complex module colimit.
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

/-- A stagewise star flow.  Its time and transition laws are explicit
hypotheses of the descent theorems below. -/
abbrev FlowData := ∀ n, ℝ → Stage n ≃⋆ₐ[ℂ] Stage n

variable (Φ : FlowData Stage)

 theorem flow_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (n : ℕ) (a : Stage n) :
    Φ n 0 a = a := by
  have h := hflow_add n (1 : ℝ) 0 a
  have h' : Φ n 1 a = Φ n 1 (Φ n 0 a) := by
    simpa using h
  exact (Φ n 1).injective h'.symm

def flowNatTrans
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    stageModuleDiagram Stage T ⟶ stageModuleDiagram Stage T where
  app n := ModuleCat.ofHom ((Φ n t).toAlgEquiv.toLinearMap)
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext a
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    simpa [stageModuleDiagram] using
      (hmap_naturality (leOfHom f) t a).symm

def flowColimitMap
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) ⟶
      (colimit (stageModuleDiagram Stage T) : ModuleCat ℂ) :=
  colim.map (flowNatTrans Stage T Φ hmap_naturality t)

@[simp] theorem flowColimitMap_inclusion
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) (n : ℕ) (a : Stage n) :
    flowColimitMap Stage T Φ hmap_naturality t
        ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
      (colimit.ι (stageModuleDiagram Stage T) n).hom (Φ n t a) := by
  have hι := colimit.ι_map (flowNatTrans Stage T Φ hmap_naturality t) n
  exact congrArg (fun f => f a) hι

theorem flowColimitMap_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a)) :
    flowColimitMap Stage T Φ hmap_naturality 0 = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  change flowColimitMap Stage T Φ hmap_naturality 0
      ((colimit.ι (stageModuleDiagram Stage T) n).hom a) =
    (colimit.ι (stageModuleDiagram Stage T) n).hom a
  rw [flowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (flow_zero (Stage := Stage) Φ hflow_add n a)

theorem flowColimitMap_add
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t s : ℝ) :
    flowColimitMap Stage T Φ hmap_naturality (t + s) =
      flowColimitMap Stage T Φ hmap_naturality s ≫
        flowColimitMap Stage T Φ hmap_naturality t := by
  apply colimit.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  simp only [ModuleCat.comp_apply]
  rw [flowColimitMap_inclusion, flowColimitMap_inclusion,
    flowColimitMap_inclusion]
  exact congrArg (fun f => (colimit.ι (stageModuleDiagram Stage T) n).hom f)
    (hflow_add n t s a)

theorem flowColimitMap_right_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    flowColimitMap Stage T Φ hmap_naturality t ≫
        flowColimitMap Stage T Φ hmap_naturality (-t) = 𝟙 _ := by
  rw [← flowColimitMap_add Stage T Φ hflow_add hmap_naturality (-t) t]
  simpa using flowColimitMap_zero Stage T Φ hflow_add hmap_naturality

theorem flowColimitMap_left_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    flowColimitMap Stage T Φ hmap_naturality (-t) ≫
        flowColimitMap Stage T Φ hmap_naturality t = 𝟙 _ := by
  rw [← flowColimitMap_add Stage T Φ hflow_add hmap_naturality t (-t)]
  simpa using flowColimitMap_zero Stage T Φ hflow_add hmap_naturality

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
