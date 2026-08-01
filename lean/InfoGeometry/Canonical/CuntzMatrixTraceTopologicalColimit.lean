import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Topological colimit of the noncommutative matrix trace tower

The matrix tower has already been constructed as a genuine `ModuleCat ℂ`
diagram.  This file adds only the topological projection: finite-dimensional
continuity turns each algebraic transition into a `TopCat` morphism, and the
universal topological colimit supplies the canonical injections.  No metric
completion or positive matrix order is inferred here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open FilteredColimit.Native.Topological

def continuousTransition (T : Data) {m n : ℕ} (hmn : m ≤ n) :
    ContinuousMap (MatrixStage m) (MatrixStage n) :=
  { toFun := map T hmn
    continuous_toFun :=
      (map T hmn).toAlgHom.toLinearMap.continuous_of_finiteDimensional }

def topologicalDiagram (T : Data) : ℕ ⥤ TopCat where
  obj n := TopCat.of (MatrixStage n)
  map f := TopCat.ofHom (continuousTransition T (leOfHom f))
  map_id n := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    simp [continuousTransition]
  map_comp f g := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro A
    have h := congrArg (fun e => e A)
      (map_comp T (leOfHom f) (leOfHom g)).symm
    simpa [continuousTransition] using h

abbrev topologicalColimitObject (T : Data) : TopCat :=
  topologicalDirectColimit (topologicalDiagram T)

abbrev topologicalColimit (T : Data) : Type :=
  (topologicalColimitObject T)

def topologicalInclusion (T : Data) (n : ℕ) :
    (topologicalDiagram T).obj n ⟶ topologicalColimitObject T :=
  topologicalDirectInjection (topologicalDiagram T) n

def continuousTrace (n : ℕ) : ContinuousMap (MatrixStage n) ℂ :=
  { toFun := matrixTraceFunctional n
    continuous_toFun :=
      (matrixTraceFunctional n).continuous_of_finiteDimensional }

def traceTopologicalCocone (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    Cocone (topologicalDiagram T) where
  pt := TopCat.of ℂ
  ι :=
    { app := fun n => TopCat.ofHom (continuousTrace n)
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change matrixTraceFunctional n (map T (leOfHom f) A) =
          matrixTraceFunctional m A
        simpa [matrixTraceState] using
    trace_compatible T hT (leOfHom f) A }

noncomputable def traceTopologicalColimitMap (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A) :
    topologicalColimitObject T ⟶ TopCat.of ℂ :=
  topologicalDirectDescend (topologicalDiagram T) (traceTopologicalCocone T hT)

theorem traceTopologicalColimitMap_inclusion (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (n : ℕ)
    (A : MatrixStage n) :
    traceTopologicalColimitMap T hT (topologicalInclusion T n A) =
      matrixTraceFunctional n A := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram T) (traceTopologicalCocone T hT) n
  exact congrArg (fun f => f A) h

theorem traceTopologicalColimitMap_unique (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T n A) = matrixTraceState n A)
    (f : topologicalColimitObject T ⟶ TopCat.of ℂ)
    (h : ∀ (n : ℕ) (A : MatrixStage n),
      f (topologicalInclusion T n A) = matrixTraceFunctional n A) :
    f = traceTopologicalColimitMap T hT := by
  apply topologicalDirectDescend_unique
    (topologicalDiagram T) (traceTopologicalCocone T hT) f
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change f (topologicalInclusion T n A) = matrixTraceFunctional n A
  exact h n A

theorem topologicalInclusion_transition
    (T : Data) {m n : ℕ} (hmn : m ≤ n) (A : MatrixStage m) :
    topologicalInclusion T n (map T hmn A) =
      topologicalInclusion T m A := by
  have h := (colimit.cocone (topologicalDiagram T)).w (homOfLE hmn)
  simpa [topologicalInclusion, topologicalDiagram, continuousTransition] using
    congrArg (fun f => f A) h

end InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
