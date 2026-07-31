import InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
import InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge

/-!
# Topological cocone for the real GNS trace state

The normalized matrix trace already supplies a compatible real algebraic GNS
state at every finite stage.  This owner exposes its real part as a continuous
`TopCat` cocone and descends it through the existing topological colimit.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.CuntzMatrixTraceRealGNSBridge
open FilteredColimit.Native.Topological

def continuousRealTrace (n : ℕ) : ContinuousMap (MatrixStage n) ℝ :=
  { toFun := fun A => (matrixTraceFunctional n A).re
    continuous_toFun :=
      Complex.continuous_re.comp
        (matrixTraceFunctional n).continuous_of_finiteDimensional }

@[simp] theorem continuousRealTrace_apply (n : ℕ) (A : MatrixStage n) :
    continuousRealTrace n A = (matrixTraceFunctional n A).re :=
  rfl

def realTraceTopologicalCocone (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A) :
    Cocone (topologicalDiagram T) where
  pt := TopCat.of ℝ
  ι :=
    { app := fun n => TopCat.ofHom (continuousRealTrace n)
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        rw [TopCat.comp_app, TopCat.comp_app]
        change (matrixTraceFunctional n (map T (leOfHom f) A)).re =
          (matrixTraceFunctional m A).re
        exact congrArg Complex.re (trace_compatible T hT (leOfHom f) A) }

def complexTraceToRealTopCatHom : TopCat.of ℂ ⟶ TopCat.of ℝ :=
  TopCat.ofHom
    { toFun := Complex.re
      continuous_toFun := Complex.continuous_re }

noncomputable def realTraceTopologicalColimitMap (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A) :
    topologicalColimitObject T ⟶ TopCat.of ℝ :=
  topologicalDirectDescend (topologicalDiagram T)
    (realTraceTopologicalCocone T hT)

theorem realTraceTopologicalColimitMap_inclusion
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (n : ℕ) (A : MatrixStage n) :
    realTraceTopologicalColimitMap T hT (topologicalInclusion T n A) =
      (matrixTraceRealLinearMap n A) := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram T) (realTraceTopologicalCocone T hT) n
  have hA := congrArg (fun f => f A) h
  change realTraceTopologicalColimitMap T hT
      (topologicalInclusion T n A) =
      (realTraceTopologicalCocone T hT).ι.app n A
  exact hA

theorem realTraceTopologicalColimitMap_unique
    (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A)
    (f : topologicalColimitObject T ⟶ TopCat.of ℝ)
    (h : ∀ (n : ℕ) (A : MatrixStage n),
      f (topologicalInclusion T n A) = matrixTraceRealLinearMap n A) :
    f = realTraceTopologicalColimitMap T hT := by
  apply topologicalDirectDescend_unique
    (topologicalDiagram T) (realTraceTopologicalCocone T hT) f
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change f (topologicalInclusion T n A) = matrixTraceRealLinearMap n A
  exact h n A

@[reassoc]
theorem realTraceTopologicalColimitMap_factorization (T : Data)
    (hT : ∀ n A, matrixTraceState (n + 1) (T.step n A) = matrixTraceState n A) :
    realTraceTopologicalColimitMap T hT =
      traceTopologicalColimitMap T hT ≫ complexTraceToRealTopCatHom := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change realTraceTopologicalColimitMap T hT
      (topologicalInclusion T n A) =
    Complex.re (traceTopologicalColimitMap T hT
      (topologicalInclusion T n A))
  rw [realTraceTopologicalColimitMap_inclusion T hT,
    traceTopologicalColimitMap_inclusion T hT]
  rfl

end InfoGeometry.Canonical.CuntzMatrixTraceTopologicalGNSBridge
