import InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Finite `Cl(1,1)` Markov trace cocone in `TopCat`

The one-step topological readout is extended to the whole finite directed
diagram.  The bonding maps are iterated algebra embeddings, and the
normalized trace descends through the existing categorical topological
colimit.  This is a finite-stage cocone theorem; it does not construct a
trace on a completed factor.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Canonical.Cl11MarkovJonesTopologicalBridge
open FilteredColimit.Native.Topological

/-- Iterated algebra embedding along a proof `m ≤ n`. -/
def stageEmbedMap {m n : ℕ} (h : m ≤ n) :
    MatStage m →ₐ[ℝ] MatStage n :=
  Nat.leRecOn h
    (fun {k} (f : MatStage m →ₐ[ℝ] MatStage k) =>
      (stageEmbed k).comp f)
    (AlgHom.id ℝ (MatStage m))

@[simp] theorem stageEmbedMap_refl (m : ℕ) :
    stageEmbedMap (le_refl m) = AlgHom.id ℝ (MatStage m) := by
  dsimp [stageEmbedMap]
  exact Nat.leRecOn_self
    (C := fun k => MatStage m →ₐ[ℝ] MatStage k)
    (AlgHom.id ℝ (MatStage m))

theorem stageEmbedMap_succ {m n : ℕ} (h : m ≤ n) :
    stageEmbedMap (Nat.le.step h) =
      (stageEmbed n).comp (stageEmbedMap h) := by
  dsimp [stageEmbedMap]
  exact Nat.leRecOn_succ
    (C := fun k => MatStage m →ₐ[ℝ] MatStage k) h
    (AlgHom.id ℝ (MatStage m))

theorem stageEmbedMap_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (stageEmbedMap hnk).comp (stageEmbedMap hmn) =
      stageEmbedMap (hmn.trans hnk) := by
  induction hnk with
  | refl =>
      rw [stageEmbedMap_refl]
      simp
  | step hnj ih =>
      rw [stageEmbedMap_succ hnj, stageEmbedMap_succ (hmn.trans hnj)]
      rw [AlgHom.comp_assoc, ih]

theorem stageEmbedMap_apply_refl (m : ℕ) (A : MatStage m) :
    stageEmbedMap (le_refl m) A = A := by
  rw [stageEmbedMap_refl]
  rfl

theorem normalizedTrace_stageEmbedMap {m n : ℕ} (h : m ≤ n)
    (A : MatStage m) :
    normalizedTrace n (stageEmbedMap h A) = normalizedTrace m A := by
  induction h with
  | refl =>
      simp [stageEmbedMap_refl]
  | @step n h ih =>
      rw [stageEmbedMap_succ h]
      change normalizedTrace (n + 1)
        (stageEmbed n (stageEmbedMap h A)) = _
      rw [stageEmbed_apply, normalizedTrace_matStageEmbed, ih]

def continuousStageEmbedMap {m n : ℕ} (h : m ≤ n) :
    ContinuousMap (MatStage m) (MatStage n) :=
  { toFun := stageEmbedMap h
    continuous_toFun :=
      (stageEmbedMap h).toLinearMap.continuous_of_finiteDimensional }

def topologicalDiagram : ℕ ⥤ TopCat where
  obj n := TopCat.of (MatStage n)
  map f := TopCat.ofHom (continuousStageEmbedMap (leOfHom f))
  map_id n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    change stageEmbedMap (le_refl n) A = A
    exact stageEmbedMap_apply_refl n A
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    rw [TopCat.comp_app]
    dsimp [continuousStageEmbedMap]
    have h := congrArg (fun F => F A)
      (stageEmbedMap_comp (leOfHom f) (leOfHom g)).symm
    simpa using h

abbrev topologicalColimitObject : TopCat :=
  topologicalDirectColimit topologicalDiagram

abbrev topologicalColimit : Type := topologicalColimitObject

def topologicalInclusion (n : ℕ) :
    (topologicalDiagram).obj n ⟶ topologicalColimitObject :=
  topologicalDirectInjection topologicalDiagram n

def traceTopologicalCocone : Cocone topologicalDiagram where
  pt := TopCat.of ℝ
  ι :=
    { app := fun n => normalizedTraceTopCatHom n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change normalizedTrace n (stageEmbedMap (leOfHom f) A) =
          normalizedTrace m A
        exact normalizedTrace_stageEmbedMap (leOfHom f) A }

noncomputable def traceTopologicalColimitMap :
    topologicalColimitObject ⟶ TopCat.of ℝ :=
  topologicalDirectDescend topologicalDiagram traceTopologicalCocone

theorem traceTopologicalColimitMap_inclusion (n : ℕ) (A : MatStage n) :
    traceTopologicalColimitMap (topologicalInclusion n A) =
      normalizedTrace n A := by
  have h := topologicalDirectDescend_stage
    topologicalDiagram traceTopologicalCocone n
  exact congrArg (fun f => f A) h

theorem traceTopologicalColimitMap_unique
    (f : topologicalColimitObject ⟶ TopCat.of ℝ)
    (h : ∀ (n : ℕ) (A : MatStage n),
      f (topologicalInclusion n A) = normalizedTrace n A) :
    f = traceTopologicalColimitMap := by
  apply topologicalDirectDescend_unique topologicalDiagram
    traceTopologicalCocone f
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change f (topologicalInclusion n A) = normalizedTrace n A
  exact h n A

end InfoGeometry.Canonical.Cl11MarkovJonesTopologicalColimit
