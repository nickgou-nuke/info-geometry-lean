import InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge

/-!
# Continuous involution readout on the matrix colimit

The algebraic Cl(1,1) direct limit has a stagewise involution, while the
`TopCat` colimit is intentionally kept as a topological object rather than
given a guessed global `StarRing` instance.  This file descends the genuine
finite-dimensional conjugate-transpose maps through the topological colimit.
The result is a continuous involution map with exact stage readback.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTraceTopologicalColimit
open InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open FilteredColimit.Native.Topological

/-! Conjugate transpose is continuous on every finite matrix stage. -/
def continuousConjTranspose (n : ℕ) :
    ContinuousMap (MatrixStage n) (MatrixStage n) :=
  { toFun := Matrix.conjTranspose
    continuous_toFun := continuous_id.matrix_conjTranspose }

def topologicalStarCocone
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) :
    Cocone (topologicalDiagram T) where
  pt := topologicalColimitObject T
  ι :=
    { app := fun n =>
        TopCat.ofHom (continuousConjTranspose n) ≫
          topologicalInclusion T n
      naturality := by
        intro m n f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro A
        change topologicalInclusion T n
            ((map T (leOfHom f) A).conjTranspose) =
          topologicalInclusion T m A.conjTranspose
        have hmap :
            map T (leOfHom f) A.conjTranspose =
              (map T (leOfHom f) A).conjTranspose := by
          simpa only [Matrix.star_eq_conjTranspose] using
            (map_star (map T (leOfHom f)) A)
        rw [← hmap]
        exact topologicalInclusion_transition T (leOfHom f) A.conjTranspose }

noncomputable def topologicalStarReadout
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) :
    topologicalColimitObject T ⟶ topologicalColimitObject T :=
  topologicalDirectDescend (topologicalDiagram T) (topologicalStarCocone T)

theorem topologicalStarReadout_inclusion
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) (n : ℕ)
    (A : MatrixStage n) :
    topologicalStarReadout T (topologicalInclusion T n A) =
      topologicalInclusion T n A.conjTranspose := by
  have h := topologicalDirectDescend_stage
    (topologicalDiagram T) (topologicalStarCocone T) n
  exact congrArg (fun f => f A) h

theorem topologicalStarReadout_involutive
    (T : InfoGeometry.Canonical.CuntzMatrixTraceTower.Data) :
    topologicalStarReadout T ≫ topologicalStarReadout T = 𝟙 _ := by
  apply colimit.hom_ext
  intro n
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro A
  change topologicalStarReadout T
      (topologicalStarReadout T (topologicalInclusion T n A)) =
      topologicalInclusion T n A
  rw [topologicalStarReadout_inclusion,
    topologicalStarReadout_inclusion]
  simp

/-! The algebraic and topological involution readouts commute after the
    coherent finite-stage complexification. -/
theorem coherentComplexification_limitStarAddHom_compatibility
    (x : Limit) :
    coherentComplexificationColimitMap
        (coherentAlgebraicToTopological
          (limitStarAddHom x)) =
      topologicalStarReadout concreteData
        (coherentComplexificationColimitMap
          (coherentAlgebraicToTopological x)) := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change coherentComplexificationColimitMap
          (coherentAlgebraicToTopological
            (limitStarAddHom (ofStage n A))) =
        topologicalStarReadout concreteData
          (coherentComplexificationColimitMap
            (coherentAlgebraicToTopological (ofStage n A)))
      rw [limitStarAddHom_ofStage,
        coherentComplexificationColimit_stageStarMap_conjTranspose,
        coherentAlgebraicToTopological_ofStage,
        coherentComplexificationColimitMap_stage,
        topologicalStarReadout_inclusion]


end InfoGeometry.Canonical.Cl11CuntzTopologicalStarReadout
