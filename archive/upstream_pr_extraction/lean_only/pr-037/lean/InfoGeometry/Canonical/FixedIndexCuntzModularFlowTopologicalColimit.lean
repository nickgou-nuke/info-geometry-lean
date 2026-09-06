import InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Topological descent for the fixed-index Cuntz modular flow

The fixed-index tower is an explicit finite C*-algebraic input.  Continuity,
time composition, and transition compatibility are supplied by native
Mathlib maps and explicit theorem hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
open InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)
variable (Φ : FlowData Stage)

variable (hmap_naturality :
  ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
    T.map hmn (Φ m t a) = Φ n t (T.map hmn a))

abbrev system : ContinuousStarInductiveSystem Stage :=
  FixedIndexCuntzStarTower.Data.toContinuousStarInductiveSystem
    (Stage := Stage) T

def flowStarAlgHom (n : ℕ) (t : ℝ) : Stage n →⋆ₐ[ℂ] Stage n :=
  { toAlgHom := (Φ n t).toAlgEquiv
    map_star' := fun a => map_star (Φ n t) a }

def flowContinuousMap (n : ℕ) (t : ℝ) :
    ContinuousMap (Stage n) (Stage n) :=
  { toFun := Φ n t
    continuous_toFun :=
      (starAlgHomToContinuousLinearMap (flowStarAlgHom Stage Φ n t)).continuous }

@[simp] theorem flowContinuousMap_apply (n : ℕ) (t : ℝ) (a : Stage n) :
    flowContinuousMap Stage Φ n t a = Φ n t a :=
  rfl

def flowTopCatNatTrans
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    topologicalDiagram Stage (system Stage T) ⟶
      topologicalDiagram Stage (system Stage T) where
  app n := TopCat.ofHom (flowContinuousMap Stage Φ n t)
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change Φ n t (T.map (leOfHom f) a) =
      T.map (leOfHom f) (Φ m t a)
    exact (hmap_naturality (leOfHom f) t a).symm

noncomputable def flowTopologicalColimitMap
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    topologicalColimit Stage (system Stage T) ⟶
      topologicalColimit Stage (system Stage T) :=
  colim.map (flowTopCatNatTrans Stage T Φ hmap_naturality t)

@[simp] theorem flowTopologicalColimitMap_inclusion
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) (n : ℕ) (a : Stage n) :
    flowTopologicalColimitMap Stage T Φ hmap_naturality t
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ n t a) := by
  have hι := colimit.ι_map (flowTopCatNatTrans Stage T Φ hmap_naturality t) n
  exact congrArg (fun f => f a) hι

theorem flowTopologicalColimitMap_zero
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a)) :
    flowTopologicalColimitMap Stage T Φ hmap_naturality 0 =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app]
  change flowTopologicalColimitMap Stage T Φ hmap_naturality 0
      (topologicalInjection Stage (system Stage T) n a) = _
  rw [flowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (FixedIndexCuntzModularFlowColimit.flow_zero
      (Stage := Stage) Φ hflow_add n a)

theorem flowTopologicalColimitMap_add
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t s : ℝ) :
    flowTopologicalColimitMap Stage T Φ hmap_naturality (t + s) =
      flowTopologicalColimitMap Stage T Φ hmap_naturality s ≫
        flowTopologicalColimitMap Stage T Φ hmap_naturality t := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change flowTopologicalColimitMap Stage T Φ hmap_naturality (t + s)
      (topologicalInjection Stage (system Stage T) n a) =
    flowTopologicalColimitMap Stage T Φ hmap_naturality t
      (flowTopologicalColimitMap Stage T Φ hmap_naturality s
        (topologicalInjection Stage (system Stage T) n a))
  rw [flowTopologicalColimitMap_inclusion,
    flowTopologicalColimitMap_inclusion,
    flowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (hflow_add n t s a)

theorem flowTopologicalColimitMap_right_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    flowTopologicalColimitMap Stage T Φ hmap_naturality t ≫
        flowTopologicalColimitMap Stage T Φ hmap_naturality (-t) =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← flowTopologicalColimitMap_add Stage T Φ hflow_add hmap_naturality (-t) t]
  simpa using flowTopologicalColimitMap_zero Stage T Φ hflow_add hmap_naturality

theorem flowTopologicalColimitMap_left_inverse
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    flowTopologicalColimitMap Stage T Φ hmap_naturality (-t) ≫
        flowTopologicalColimitMap Stage T Φ hmap_naturality t =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← flowTopologicalColimitMap_add Stage T Φ hflow_add hmap_naturality t (-t)]
  simpa using flowTopologicalColimitMap_zero Stage T Φ hflow_add hmap_naturality

/-- The fixed-index descended flow is a `TopCat` isomorphism. -/
def flowTopologicalColimitIso
    (hflow_add :
      ∀ (n : ℕ) (t s : ℝ) (a : Stage n),
        Φ n (t + s) a = Φ n t (Φ n s a))
    (hmap_naturality :
      ∀ {m n : ℕ} (hmn : m ≤ n) (t : ℝ) (a : Stage m),
        T.map hmn (Φ m t a) = Φ n t (T.map hmn a))
    (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := flowTopologicalColimitMap Stage T Φ hmap_naturality t
  inv := flowTopologicalColimitMap Stage T Φ hmap_naturality (-t)
  hom_inv_id := flowTopologicalColimitMap_right_inverse
    Stage T Φ hflow_add hmap_naturality t
  inv_hom_id := flowTopologicalColimitMap_left_inverse
    Stage T Φ hflow_add hmap_naturality t

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit
