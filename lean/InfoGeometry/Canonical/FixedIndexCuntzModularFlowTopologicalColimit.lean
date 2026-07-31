import InfoGeometry.Canonical.FixedIndexCuntzModularFlowColimit
import InfoGeometry.Canonical.FilteredStarAlgebraTopologicalColimit

/-!
# Topological descent for the fixed-index Cuntz modular flow

This is the `TopCat` counterpart of the existing `ModuleCat` descent.  The
fixed-index tower remains an explicit finite C*-algebraic input; only its
continuous maps and categorical colimit are added here.
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
variable (Φ : FlowData Stage T)

abbrev system : ContinuousStarInductiveSystem Stage :=
  FixedIndexCuntzStarTower.Data.toContinuousStarInductiveSystem
    (Stage := Stage) T

def flowStarAlgHom (n : ℕ) (t : ℝ) : Stage n →⋆ₐ[ℂ] Stage n :=
  { toAlgHom := (Φ.flow n t).toAlgEquiv
    map_star' := fun a => map_star (Φ.flow n t) a }

def flowContinuousMap (n : ℕ) (t : ℝ) :
    ContinuousMap (Stage n) (Stage n) :=
  { toFun := Φ.flow n t
    continuous_toFun :=
      (starAlgHomToContinuousLinearMap (flowStarAlgHom Stage T Φ n t)).continuous }

@[simp] theorem flowContinuousMap_apply (n : ℕ) (t : ℝ) (a : Stage n) :
    flowContinuousMap Stage T Φ n t a = Φ.flow n t a :=
  rfl

def flowTopCatNatTrans (t : ℝ) :
    topologicalDiagram Stage (system Stage T) ⟶
      topologicalDiagram Stage (system Stage T) where
  app n := TopCat.ofHom (flowContinuousMap Stage T Φ n t)
  naturality := by
    intro m n f
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change Φ.flow n t (T.map (leOfHom f) a) =
      T.map (leOfHom f) (Φ.flow m t a)
    exact (Φ.map_naturality (leOfHom f) t a).symm

noncomputable def flowTopologicalColimitMap (t : ℝ) :
    topologicalColimit Stage (system Stage T) ⟶
      topologicalColimit Stage (system Stage T) :=
  colim.map (flowTopCatNatTrans Stage T Φ t)

@[simp] theorem flowTopologicalColimitMap_inclusion
    (t : ℝ) (n : ℕ) (a : Stage n) :
    flowTopologicalColimitMap Stage T Φ t
        (topologicalInjection Stage (system Stage T) n a) =
      topologicalInjection Stage (system Stage T) n (Φ.flow n t a) := by
  have hι := colimit.ι_map (flowTopCatNatTrans Stage T Φ t) n
  exact congrArg (fun f => f a) hι

theorem flowTopologicalColimitMap_zero :
    flowTopologicalColimitMap Stage T Φ 0 =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app]
  change flowTopologicalColimitMap Stage T Φ 0
      (topologicalInjection Stage (system Stage T) n a) = _
  rw [flowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (Φ.flow_zero n a)

theorem flowTopologicalColimitMap_add (t s : ℝ) :
    flowTopologicalColimitMap Stage T Φ (t + s) =
      flowTopologicalColimitMap Stage T Φ s ≫
        flowTopologicalColimitMap Stage T Φ t := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  change flowTopologicalColimitMap Stage T Φ (t + s)
      (topologicalInjection Stage (system Stage T) n a) =
    flowTopologicalColimitMap Stage T Φ t
      (flowTopologicalColimitMap Stage T Φ s
        (topologicalInjection Stage (system Stage T) n a))
  rw [flowTopologicalColimitMap_inclusion,
    flowTopologicalColimitMap_inclusion,
    flowTopologicalColimitMap_inclusion]
  exact congrArg (topologicalInjection Stage (system Stage T) n)
    (Φ.flow_add n t s a)

theorem flowTopologicalColimitMap_right_inverse (t : ℝ) :
    flowTopologicalColimitMap Stage T Φ t ≫
        flowTopologicalColimitMap Stage T Φ (-t) =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← flowTopologicalColimitMap_add Stage T Φ (-t) t]
  simpa using flowTopologicalColimitMap_zero Stage T Φ

theorem flowTopologicalColimitMap_left_inverse (t : ℝ) :
    flowTopologicalColimitMap Stage T Φ (-t) ≫
        flowTopologicalColimitMap Stage T Φ t =
      𝟙 (topologicalColimit Stage (system Stage T)) := by
  rw [← flowTopologicalColimitMap_add Stage T Φ t (-t)]
  simpa using flowTopologicalColimitMap_zero Stage T Φ

/-- The fixed-index descended flow is a `TopCat` isomorphism, with inverse
    given by the opposite-time map. -/
def flowTopologicalColimitIso (t : ℝ) :
    topologicalColimit Stage (system Stage T) ≅
      topologicalColimit Stage (system Stage T) where
  hom := flowTopologicalColimitMap Stage T Φ t
  inv := flowTopologicalColimitMap Stage T Φ (-t)
  hom_inv_id := flowTopologicalColimitMap_right_inverse Stage T Φ t
  inv_hom_id := flowTopologicalColimitMap_left_inverse Stage T Φ t

@[simp]
theorem flowTopologicalColimitIso_hom (t : ℝ) :
    (flowTopologicalColimitIso Stage T Φ t).hom =
      flowTopologicalColimitMap Stage T Φ t :=
  rfl

@[simp]
theorem flowTopologicalColimitIso_inv (t : ℝ) :
    (flowTopologicalColimitIso Stage T Φ t).inv =
      flowTopologicalColimitMap Stage T Φ (-t) :=
  rfl

end InfoGeometry.Canonical.FixedIndexCuntzModularFlowTopologicalColimit
