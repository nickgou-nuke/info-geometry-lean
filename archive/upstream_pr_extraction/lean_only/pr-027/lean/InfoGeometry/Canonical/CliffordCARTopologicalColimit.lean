import InfoGeometry.Clifford.Cl11TensorTower
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Topological Clifford/CAR tower colimit

The Jordan--Wigner CAR tower already has honest finite matrix stages and
algebra-hom bonding maps.  This owner exposes the same filtered system in
`TopCat`, using Mathlib's finite-dimensional continuous-linear-map conversion.
It records only the topological colimit injections and generator transport;
no completed CAR representation is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordCARTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open FilteredColimit.Native.Topological

abbrev Stage (n : ℕ) : Type := MatStage n

/-- Iterated algebra-hom transition from stage `m` to stage `n`. -/
def bondAlgHom (m n : ℕ) (h : m ≤ n) :
    Stage m →ₐ[ℝ] Stage n :=
  Nat.leRecOn h
    (C := fun n => Stage m →ₐ[ℝ] Stage n)
    (fun {k} ih => (stageEmbed k).comp ih)
    (AlgHom.id ℝ (Stage m))

@[simp] theorem bondAlgHom_refl (m : ℕ) :
    bondAlgHom m m le_rfl = AlgHom.id ℝ (Stage m) := by
  simpa [bondAlgHom] using
    (Nat.leRecOn_self
      (C := fun n => Stage m →ₐ[ℝ] Stage n)
      (next := fun {k} ih => (stageEmbed k).comp ih)
      (x := AlgHom.id ℝ (Stage m)))

@[simp] theorem bondAlgHom_succ (m n : ℕ) (h : m ≤ n) :
    bondAlgHom m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (stageEmbed n).comp (bondAlgHom m n h) := by
  unfold bondAlgHom
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

theorem bondAlgHom_trans (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    bondAlgHom m k (hmn.trans hnk) =
      (bondAlgHom n k hnk).comp (bondAlgHom m n hmn) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t ht =>
      bondAlgHom m t (hmn.trans ht) =
        (bondAlgHom n t ht).comp (bondAlgHom m n hmn))
    ?base ?succ k hnk
  · simp [bondAlgHom_refl]
  · intro t hnt ih
    rw [bondAlgHom_succ m t (hmn.trans hnt)]
    rw [bondAlgHom_succ n t hnt]
    simp [ih, AlgHom.comp_assoc]

/-- Every finite-stage transition is continuous by finite-dimensionality. -/
def bondCLM (m n : ℕ) (h : m ≤ n) :
    Stage m →L[ℝ] Stage n :=
  LinearMap.toContinuousLinearMap (bondAlgHom m n h).toLinearMap

@[simp] theorem bondCLM_apply (m n : ℕ) (h : m ≤ n) (A : Stage m) :
    bondCLM m n h A = bondAlgHom m n h A :=
  rfl

/-- The Clifford matrix tower as a filtered diagram in `TopCat`. -/
def topologicalDiagram : ℕ ⥤ TopCat where
  obj n := TopCat.of (Stage n)
  map f := TopCat.ofHom
    { toFun := bondCLM _ _ (leOfHom f)
      continuous_toFun := (bondCLM _ _ (leOfHom f)).continuous }
  map_id n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    change bondCLM n n (le_refl n) A = A
    rw [bondCLM_apply, bondAlgHom_refl]
    rfl
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    change bondCLM _ _ (leOfHom (f ≫ g)) A =
      bondCLM _ _ (leOfHom g) (bondCLM _ _ (leOfHom f) A)
    rw [bondCLM_apply, bondCLM_apply, bondCLM_apply]
    exact congrArg (fun e => e A)
      (bondAlgHom_trans _ _ _ (leOfHom f) (leOfHom g))

abbrev topologicalColimit : TopCat :=
  topologicalDirectColimit topologicalDiagram

def topologicalInjection (n : ℕ) :
    (topologicalDiagram.obj n) ⟶ topologicalColimit :=
  topologicalDirectInjection topologicalDiagram n

theorem topologicalInjection_transition
    {m n : ℕ} (hmn : m ≤ n) (A : Stage m) :
    topologicalInjection n (bondAlgHom m n hmn A) =
      topologicalInjection m A := by
  have h := (colimit.cocone topologicalDiagram).w (homOfLE hmn)
  simpa [topologicalInjection, topologicalDiagram, bondCLM] using
    congrArg (fun f => f A) h

/-- Creation representatives survive the topological tower transition. -/
theorem creationRepresentative_transition
    (n : ℕ) (k : Fin n) :
    topologicalInjection (n + 1) (jwCreation (n + 1) k.castSucc) =
      topologicalInjection n (jwCreation n k) := by
  have h := topologicalInjection_transition (m := n) (n := n + 1)
    (Nat.le_succ n) (jwCreation n k)
  simpa [bondAlgHom_succ, stageEmbed_apply] using h

/-- Annihilation representatives survive the topological tower transition. -/
theorem annihilationRepresentative_transition
    (n : ℕ) (k : Fin n) :
    topologicalInjection (n + 1) (jwAnnihilation (n + 1) k.castSucc) =
      topologicalInjection n (jwAnnihilation n k) := by
  have h := topologicalInjection_transition (m := n) (n := n + 1)
    (Nat.le_succ n) (jwAnnihilation n k)
  simpa [bondAlgHom_succ, stageEmbed_apply] using h

end InfoGeometry.Canonical.CliffordCARTopologicalColimit
