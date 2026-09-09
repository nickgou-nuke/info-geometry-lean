import InfoGeometry.Canonical.FilteredQCCRFixedParameterColimit
import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Inverse limits of compatible fixed-q q-CCR loci

The fixed-parameter owner already supplies the natural `TopCat` map from a
stagewise q-locus into the residual zero fibre.  This file performs the
corresponding inverse-limit descent.  All maps are obtained from `limit.lift`
and its projection equations; no pointwise product or coordinate model is
introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredQCCRFixedParameterLimit

universe u

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open InfoGeometry.Canonical.FilteredQCCRFixedParameterColimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- The inverse limit of a compatible fixed-q locus diagram. -/
abbrev qCcrZeroLocusTopologicalLimit
    (qdata : CompatibleQParameter Stage sys) : TopCat :=
  topologicalInverseLimit
    (qCcrZeroLocusTopologicalDiagram Stage sys qdata)

/-- The cone obtained by composing fixed-q projections with the stagewise
    specialization transformation into the residual zero-fibre diagram. -/
def qCcrZeroLocusSpecializationLimitCone
    (qdata : CompatibleQParameter Stage sys) :
    Cone (qCcrParameterZeroFiberTopologicalDiagram Stage sys) where
  pt := qCcrZeroLocusTopologicalLimit Stage sys qdata
  π :=
    { app := fun i =>
        topologicalInverseProjection
            (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i ≫
          (qCcrZeroLocusSpecializationNatTrans Stage sys qdata).app i
      naturality := by
        intro i j f
        change
          (𝟙 _ ≫ topologicalInverseProjection
            (qCcrZeroLocusTopologicalDiagram Stage sys qdata) j) ≫
              (qCcrZeroLocusSpecializationNatTrans Stage sys qdata).app j =
            topologicalInverseProjection
                (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i ≫
              (qCcrZeroLocusSpecializationNatTrans Stage sys qdata).app i ≫
              (qCcrParameterZeroFiberTopologicalDiagram Stage sys).map f
        simp only [Category.id_comp]
        rw [← topologicalInverseProjection_naturality
          (qCcrZeroLocusTopologicalDiagram Stage sys qdata) f]
        rw [Category.assoc]
        rw [(qCcrZeroLocusSpecializationNatTrans Stage sys qdata).naturality f] }

/-- Inverse-limit map induced by the compatible fixed-q specialization maps. -/
noncomputable def qCcrZeroLocusSpecializationLimitMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalLimit Stage sys qdata ⟶
      qCcrParameterZeroFiberTopologicalLimit Stage sys :=
  topologicalInverseLift
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrZeroLocusSpecializationLimitCone Stage sys qdata)

@[reassoc]
theorem qCcrZeroLocusSpecializationLimitMap_projection
    (qdata : CompatibleQParameter Stage sys) (i : I) :
    qCcrZeroLocusSpecializationLimitMap Stage sys qdata ≫
        topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i =
      (qCcrZeroLocusSpecializationLimitCone Stage sys qdata).π.app i := by
  exact topologicalInverseLift_projection
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrZeroLocusSpecializationLimitCone Stage sys qdata) i

theorem qCcrZeroLocusSpecializationLimitMap_projection_apply
    (qdata : CompatibleQParameter Stage sys) (i : I)
    (x : qCcrZeroLocusTopologicalLimit Stage sys qdata) :
    topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
        (qCcrZeroLocusSpecializationLimitMap Stage sys qdata x) =
      (qCcrZeroLocusSpecializationLimitCone Stage sys qdata).π.app i x := by
  exact topologicalInverseLift_projection_apply
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrZeroLocusSpecializationLimitCone Stage sys qdata) i x

theorem qCcrZeroLocusSpecializationLimitMap_unique
    (qdata : CompatibleQParameter Stage sys)
    (f : qCcrZeroLocusTopologicalLimit Stage sys qdata ⟶
      qCcrParameterZeroFiberTopologicalLimit Stage sys)
    (h : ∀ i : I,
      f ≫ topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i =
        (qCcrZeroLocusSpecializationLimitCone Stage sys qdata).π.app i) :
    f = qCcrZeroLocusSpecializationLimitMap Stage sys qdata := by
  exact topologicalInverseLift_unique
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrZeroLocusSpecializationLimitCone Stage sys qdata) f h

theorem qCcrZeroLocusSpecializationLimitMap_injective
    (qdata : CompatibleQParameter Stage sys) :
    Function.Injective (qCcrZeroLocusSpecializationLimitMap Stage sys qdata) := by
  intro x y hxy
  let cx : TopCat.of PUnit ⟶
      qCcrZeroLocusTopologicalLimit Stage sys qdata :=
    TopCat.ofHom
      { toFun := fun _ => x
        continuous_toFun := continuous_const }
  let cy : TopCat.of PUnit ⟶
      qCcrZeroLocusTopologicalLimit Stage sys qdata :=
    TopCat.ofHom
      { toFun := fun _ => y
        continuous_toFun := continuous_const }
  have hcxcy : cx = cy := by
    apply limit.hom_ext
    intro i
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro u
    have hstage :
        topologicalInverseProjection
            (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i x =
          topologicalInverseProjection
            (qCcrZeroLocusTopologicalDiagram Stage sys qdata) i y := by
      apply qCcrZeroLocusSpecializationTopCatHom_isClosedEmbedding
        Stage sys qdata i |>.injective
      have hproj := congrArg
        (fun z => topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i z) hxy
      simpa [qCcrZeroLocusSpecializationLimitMap_projection_apply,
        qCcrZeroLocusSpecializationLimitCone] using hproj
    simpa [cx, cy] using hstage
  exact congrArg (fun g => g PUnit.unit) hcxcy

/-- The ambient inverse-limit map obtained by composing the fixed-q
    specialization with the zero-fibre inclusion. -/
noncomputable def qCcrZeroLocusParameterLimitMap
    (qdata : CompatibleQParameter Stage sys) :
    qCcrZeroLocusTopologicalLimit Stage sys qdata ⟶
      qCcrParameterTopologicalLimit Stage sys :=
  qCcrZeroLocusSpecializationLimitMap Stage sys qdata ≫
    qCcrParameterZeroFiberToParameterLimit Stage sys

theorem qCcrZeroLocusParameterLimitMap_projection_apply
    (qdata : CompatibleQParameter Stage sys) (i : I)
    (x : qCcrZeroLocusTopologicalLimit Stage sys qdata) :
    topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
        (qCcrZeroLocusParameterLimitMap Stage sys qdata x) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
        ((qCcrZeroLocusSpecializationLimitCone Stage sys qdata).π.app i x) := by
  change
    (qCcrParameterZeroFiberToParameterLimit Stage sys ≫
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i)
      (qCcrZeroLocusSpecializationLimitMap Stage sys qdata x) = _
  rw [qCcrParameterZeroFiberToParameterLimit_projection Stage sys i]
  exact congrArg
    (fun y => (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i y)
    (qCcrZeroLocusSpecializationLimitMap_projection_apply Stage sys qdata i x)

theorem qCcrZeroLocusParameterLimitMap_injective
    (qdata : CompatibleQParameter Stage sys) :
    Function.Injective (qCcrZeroLocusParameterLimitMap Stage sys qdata) := by
  exact (qCcrParameterZeroFiberToParameterLimit_injective Stage sys).comp
    (qCcrZeroLocusSpecializationLimitMap_injective Stage sys qdata)

end InfoGeometry.Canonical.FilteredQCCRFixedParameterLimit
