import InfoGeometry.Canonical.CuntzStageModularFlow
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
import InfoGeometry.Canonical.FilteredStarInductiveCoconeTopCat

/-!
# Topological descent of a stagewise Cuntz modular flow

The existing stagewise flow is a family of star-algebra equivalences with a
proved transition naturality law.  This file forgets only the algebraic
structure needed for continuity, packages the same family as a natural
transformation in `TopCat`, and descends it through the categorical
topological colimit.  No analytic generator or infinite-dimensional object is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzStageModularFlow
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)
variable (Φ : CuntzStageModularFlowData Stage)
variable {Ainf : Type}
variable [CStarAlgebra Ainf] [PartialOrder Ainf] [StarOrderedRing Ainf]

abbrev system : ContinuousStarInductiveSystem Stage :=
  T.toContinuousStarInductiveSystem

def flowStarAlgHom (n : ℕ) (t : ℝ) : Stage n →⋆ₐ[ℂ] Stage n :=
  { toAlgHom := (Φ.flow n t).toAlgEquiv
    map_star' := fun a => map_star (Φ.flow n t) a }

def flowContinuousMap (n : ℕ) (t : ℝ) :
    ContinuousMap (Stage n) (Stage n) :=
  { toFun := Φ.flow n t
    continuous_toFun :=
      (starAlgHomToContinuousLinearMap (flowStarAlgHom Stage Φ n t)).continuous }

@[simp] theorem flowContinuousMap_apply (n : ℕ) (t : ℝ) (a : Stage n) :
    flowContinuousMap Stage Φ n t a = Φ.flow n t a :=
  rfl

def modularFlowTopCatNatTrans
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    topologicalDiagram Stage (system Stage T) ⟶
      topologicalDiagram Stage (system Stage T) where
  app n := TopCat.ofHom (flowContinuousMap Stage Φ n t)
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change Φ.flow n t (T.map (leOfHom f) a) =
      T.map (leOfHom f) (Φ.flow m t a)
    exact (hmap_naturality (leOfHom f) t a).symm

noncomputable def modularFlowTopologicalColimitMap
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    topologicalColimit Stage (system Stage T) ⟶
      topologicalColimit Stage (system Stage T) :=
  colim.map (modularFlowTopCatNatTrans Stage T Φ hmap_naturality t)

@[simp] theorem modularFlowTopologicalColimitMap_inclusion
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) (n : ℕ) (a : Stage n) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  have hι := colimit.ι_map (modularFlowTopCatNatTrans Stage T Φ hmap_naturality t) n
  exact congrArg (fun f => f a) hι

@[reassoc]
theorem modularFlowTopologicalColimitMap_comp_stateTopologicalColimitMap
    (cocone :
      CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
        (Ainf := Ainf) Stage (system Stage T))
    (ω : CStarStateColimit.Native.State Ainf)
    (h_invariant :
      ∀ (n : ℕ) (t : ℝ) (a : Stage n),
        ω.functional (ContinuousStarInductiveSystem.StarInductiveCocone.leg
          (Stage := Stage) (sys := system Stage T) cocone n (Φ.flow n t a)) =
          ω.functional (ContinuousStarInductiveSystem.StarInductiveCocone.leg
            (Stage := Stage) (sys := system Stage T) cocone n a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t ≫
        CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap
          (Stage := Stage) (sys := system Stage T) cocone ω =
      CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap
        (Stage := Stage) (sys := system Stage T) cocone ω := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app]
  change CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap
      (Stage := Stage) (sys := system Stage T) cocone ω
      (modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
        (topologicalInjection Stage (system Stage T) n a)) =
    CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap
      (Stage := Stage) (sys := system Stage T) cocone ω
      (topologicalInjection Stage (system Stage T) n a)
  rw [modularFlowTopologicalColimitMap_inclusion,
    CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap_inclusion,
    CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.stateTopologicalColimitMap_inclusion]
  exact congrArg ULift.up (h_invariant n t a)

theorem modularFlowTopologicalColimitMap_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a)) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality 0 =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app]
  change modularFlowTopologicalColimitMap Stage T Φ hmap_naturality 0
      (topologicalInjection Stage (system Stage T) n a) = _
  rw [modularFlowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (CuntzStageModularFlowLemmas.flow_zero
      (Stage := Stage) Φ hflow_add n a)

theorem modularFlowTopologicalColimitMap_add
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t s : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (t + s) =
      modularFlowTopologicalColimitMap Stage T Φ hmap_naturality s ≫
        modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (t + s)
      (topologicalInjection Stage (system Stage T) n a) =
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
      (modularFlowTopologicalColimitMap Stage T Φ hmap_naturality s
        (topologicalInjection Stage (system Stage T) n a))
  rw [modularFlowTopologicalColimitMap_inclusion,
    modularFlowTopologicalColimitMap_inclusion,
    modularFlowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (hflow_add n t s a)

theorem modularFlowTopologicalColimitMap_right_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t ≫
        modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t) =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← modularFlowTopologicalColimitMap_add Stage T Φ hflow_add hmap_naturality (-t) t]
  simpa using modularFlowTopologicalColimitMap_zero Stage T Φ hflow_add hmap_naturality

theorem modularFlowTopologicalColimitMap_left_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t) ≫
        modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← modularFlowTopologicalColimitMap_add Stage T Φ hflow_add hmap_naturality t (-t)]
  simpa using modularFlowTopologicalColimitMap_zero Stage T Φ hflow_add hmap_naturality

/-- The descended modular flow is a genuine `TopCat` isomorphism at every
    time.  Its inverse is the descended flow at the opposite time. -/
def modularFlowTopologicalColimitIso
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t
  inv := modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t)
  hom_inv_id := modularFlowTopologicalColimitMap_right_inverse
    Stage T Φ hflow_add hmap_naturality t
  inv_hom_id := modularFlowTopologicalColimitMap_left_inverse
    Stage T Φ hflow_add hmap_naturality t

@[simp]
theorem modularFlowTopologicalColimitIso_hom
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    (modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).hom =
      modularFlowTopologicalColimitMap Stage T Φ hmap_naturality t :=
  rfl

@[simp]
theorem modularFlowTopologicalColimitIso_inv
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ.flow n (t + s) a = Φ.flow n t (Φ.flow n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ.flow m t a) = Φ.flow n t (T.map hmn a))
    (t : ℝ) :
    (modularFlowTopologicalColimitIso Stage T Φ hflow_add hmap_naturality t).inv =
      modularFlowTopologicalColimitMap Stage T Φ hmap_naturality (-t) :=
  rfl

end InfoGeometry.Canonical.CuntzStageModularFlowTopologicalColimit
