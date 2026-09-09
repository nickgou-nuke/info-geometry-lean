import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Inverse-limit realization of the filtered q-CCR parameter diagrams

The direct-colimit owner records the forward filtered algebraic topology.  This
owner supplies the complementary `TopCat` inverse limits: a point of the limit
is a compatible family of finite-stage parameters.  The closed zero-fibre
inclusion descends to a canonical morphism between the two inverse limits.
No sequence, metric completion, or analytic continuation is introduced.
-/

noncomputable section

namespace InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)

/-- The ambient compatible-family space of q-CCR parameters. -/
abbrev qCcrParameterTopologicalLimit : TopCat :=
  topologicalInverseLimit (qCcrParameterTopologicalDiagram Stage sys)

/-- The compatible-family space cut out by the zero q-CCR relation. -/
abbrev qCcrParameterZeroFiberTopologicalLimit : TopCat :=
  topologicalInverseLimit
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)

/-- A compatible family of finite-stage zero-fibre points is a genuine
    `TopCat` cone. -/
def qCcrParameterZeroFiberPointCone
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    Cone (qCcrParameterZeroFiberTopologicalDiagram Stage sys) where
  pt := TopCat.of PUnit
  π :=
    { app := point
      naturality := by
        intro i j f
        simpa using (hpoint f).symm }

/-- The inverse-limit point determined by a compatible family of finite-stage
    zero-fibre points. -/
noncomputable def qCcrParameterZeroFiberPointLimitMap
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
  topologicalInverseLift
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrParameterZeroFiberPointCone Stage sys point hpoint)

@[simp]
theorem qCcrParameterZeroFiberPointLimitMap_projection
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (i : I) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i
        (qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint u) =
      point i u := by
  exact topologicalInverseLift_projection_apply
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrParameterZeroFiberPointCone Stage sys point hpoint) i u

theorem qCcrParameterZeroFiberPointLimitMap_unique
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (f : TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys)
    (h : ∀ i : I,
      f ≫ topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i = point i) :
    f = qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint := by
  apply topologicalInverseLift_unique
    (qCcrParameterZeroFiberTopologicalDiagram Stage sys)
    (qCcrParameterZeroFiberPointCone Stage sys point hpoint) f
  intro i
  exact h i

/-- The same compatible point family induces a natural transformation from
    the constant `PUnit` diagram to the zero-fibre diagram. -/
def qCcrParameterZeroFiberPointNatTrans
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    (Functor.const I).obj (TopCat.of PUnit) ⟶
      qCcrParameterZeroFiberTopologicalDiagram Stage sys where
  app := point
  naturality := by
    intro i j f
    simpa using (hpoint f).symm

/-- Direct-colimit readout of a compatible zero-fibre point family. -/
noncomputable def qCcrParameterZeroFiberPointColimitMap
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys :=
  colim.map (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint)

@[reassoc]
theorem qCcrParameterZeroFiberPointColimitMap_stage
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (i : I) :
    topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫
        qCcrParameterZeroFiberPointColimitMap Stage sys point hpoint =
      (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint).app i ≫
        qCcrParameterZeroFiberTopologicalInjection Stage sys i := by
  exact colimit.ι_map
    (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint) i

theorem qCcrParameterZeroFiberPointColimitMap_unique
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (f : topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage sys)
    (h : ∀ i : I,
      topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫ f =
        (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint).app i ≫
          qCcrParameterZeroFiberTopologicalInjection Stage sys i) :
    f = qCcrParameterZeroFiberPointColimitMap Stage sys point hpoint := by
  apply colimit.hom_ext
  intro i
  change topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫ f =
    topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫
      qCcrParameterZeroFiberPointColimitMap Stage sys point hpoint
  rw [h i, qCcrParameterZeroFiberPointColimitMap_stage]

/-- Direct-colimit ambient parameter readout of a compatible zero-fibre
    family. -/
noncomputable def qCcrParameterZeroFiberPointAmbientColimitMap
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys :=
  qCcrParameterZeroFiberPointColimitMap Stage sys point hpoint ≫
    qCcrParameterZeroFiberToParameterColimit Stage sys

@[reassoc]
theorem qCcrParameterZeroFiberPointAmbientColimitMap_stage
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (i : I) :
    topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫
        qCcrParameterZeroFiberPointAmbientColimitMap Stage sys point hpoint =
      (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint).app i ≫
        (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i ≫
          qCcrParameterTopologicalInjection Stage sys i := by
  change
    (topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫
      qCcrParameterZeroFiberPointColimitMap Stage sys point hpoint) ≫
      qCcrParameterZeroFiberToParameterColimit Stage sys = _
  rw [qCcrParameterZeroFiberPointColimitMap_stage]
  rw [Category.assoc]
  rw [qCcrParameterZeroFiberToParameterColimit_stage]

theorem qCcrParameterZeroFiberPointAmbientColimitMap_unique
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (f : topologicalDirectColimit ((Functor.const I).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage sys)
    (h : ∀ i : I,
      topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫ f =
        (qCcrParameterZeroFiberPointNatTrans Stage sys point hpoint).app i ≫
          (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i ≫
          qCcrParameterTopologicalInjection Stage sys i) :
    f = qCcrParameterZeroFiberPointAmbientColimitMap Stage sys point hpoint := by
  apply colimit.hom_ext
  intro i
  change topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫ f =
    topologicalDirectInjection ((Functor.const I).obj (TopCat.of PUnit)) i ≫
      qCcrParameterZeroFiberPointAmbientColimitMap Stage sys point hpoint
  rw [h i]
  rw [qCcrParameterZeroFiberPointAmbientColimitMap_stage]

/-- The zero-fibre inclusion is a cone over the ambient inverse-limit
    diagram. -/
def qCcrParameterZeroFiberToParameterLimitCone :
    Cone (qCcrParameterTopologicalDiagram Stage sys) where
  pt := qCcrParameterZeroFiberTopologicalLimit Stage sys
  π :=
    { app := fun i =>
        topologicalInverseProjection
            (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i ≫
          (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
      naturality := by
        intro i j f
        change
          (𝟙 _ ≫ topologicalInverseProjection
            (qCcrParameterZeroFiberTopologicalDiagram Stage sys) j) ≫
              (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app j =
            topologicalInverseProjection
                (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i ≫
              (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i ≫
              (qCcrParameterTopologicalDiagram Stage sys).map f
        simp only [Category.id_comp]
        rw [← topologicalInverseProjection_naturality
          (qCcrParameterZeroFiberTopologicalDiagram Stage sys) f]
        rw [Category.assoc]
        rw [(qCcrParameterZeroFiberToParameterNatTrans Stage sys).naturality f] }

/-- Canonical inverse-limit map induced by the stagewise closed-fibre
    inclusions. -/
noncomputable def qCcrParameterZeroFiberToParameterLimit :
    qCcrParameterZeroFiberTopologicalLimit Stage sys ⟶
      qCcrParameterTopologicalLimit Stage sys :=
  topologicalInverseLift (qCcrParameterTopologicalDiagram Stage sys)
    (qCcrParameterZeroFiberToParameterLimitCone Stage sys)

@[reassoc]
theorem qCcrParameterZeroFiberToParameterLimit_projection
    (i : I) :
    qCcrParameterZeroFiberToParameterLimit Stage sys ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram Stage sys) i =
      (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i := by
  exact topologicalInverseLift_projection
    (qCcrParameterTopologicalDiagram Stage sys)
    (qCcrParameterZeroFiberToParameterLimitCone Stage sys) i

theorem qCcrParameterZeroFiberToParameterLimit_projection_apply
    (i : I) (x : qCcrParameterZeroFiberTopologicalLimit Stage sys) :
    topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
        (qCcrParameterZeroFiberToParameterLimit Stage sys x) =
      (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i x := by
  simpa using congrArg (fun f => f x)
    (qCcrParameterZeroFiberToParameterLimit_projection Stage sys i)

theorem qCcrParameterZeroFiberToParameterLimit_injective :
    Function.Injective (qCcrParameterZeroFiberToParameterLimit Stage sys) := by
  intro x y hxy
  let cx : TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
    TopCat.ofHom
      { toFun := fun _ => x
        continuous_toFun := continuous_const }
  let cy : TopCat.of PUnit ⟶ qCcrParameterZeroFiberTopologicalLimit Stage sys :=
    TopCat.ofHom
      { toFun := fun _ => y
        continuous_toFun := continuous_const }
  have hcxcy : cx = cy := by
    apply limit.hom_ext
    intro i
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    have hx := qCcrParameterZeroFiberToParameterLimit_projection_apply
      Stage sys i x
    have hy := qCcrParameterZeroFiberToParameterLimit_projection_apply
      Stage sys i y
    have hcone :
        (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i x =
          (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i y := by
      calc
        (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i x =
            topologicalInverseProjection
              (qCcrParameterTopologicalDiagram Stage sys) i
              (qCcrParameterZeroFiberToParameterLimit Stage sys x) := hx.symm
        _ = topologicalInverseProjection
              (qCcrParameterTopologicalDiagram Stage sys) i
              (qCcrParameterZeroFiberToParameterLimit Stage sys y) := by
          rw [hxy]
        _ = (qCcrParameterZeroFiberToParameterLimitCone Stage sys).π.app i y := hy
    simpa [qCcrParameterZeroFiberToParameterNatTrans] using hcone
  exact congrArg (fun g => g PUnit.unit) hcxcy

/- The ambient parameter point is defined only after the inverse-limit
   inclusion, so its projection statements can use that inclusion's API. -/
noncomputable def qCcrParameterZeroFiberPointAmbientLimitMap
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j) :
    TopCat.of PUnit ⟶ qCcrParameterTopologicalLimit Stage sys :=
  qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint ≫
    qCcrParameterZeroFiberToParameterLimit Stage sys

@[simp]
theorem qCcrParameterZeroFiberPointAmbientLimitMap_projection
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (i : I) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
        (qCcrParameterZeroFiberPointAmbientLimitMap Stage sys point hpoint u) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i
        (point i u) := by
  change
    (qCcrParameterZeroFiberToParameterLimit Stage sys ≫
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i)
      (qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint u) = _
  rw [qCcrParameterZeroFiberToParameterLimit_projection Stage sys i]
  exact congrArg
    (fun x => (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i x)
    (qCcrParameterZeroFiberPointLimitMap_projection Stage sys point hpoint i u)

theorem qCcrParameterZeroFiberPointAmbientLimitMap_unique
    (point : ∀ i : I, TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage i) //
        p ∈ qCcrParameterZeroLocus (A := Stage i)})
    (hpoint : ∀ {i j : I} (f : i ⟶ j),
      point i ≫ qCcrParameterZeroFiberTransitionTopCatHom Stage sys
          (leOfHom f) = point j)
    (f : TopCat.of PUnit ⟶ qCcrParameterTopologicalLimit Stage sys)
    (h : ∀ i : I,
      f ≫ topologicalInverseProjection
          (qCcrParameterTopologicalDiagram Stage sys) i =
        point i ≫ (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i) :
    f = qCcrParameterZeroFiberPointAmbientLimitMap Stage sys point hpoint := by
  apply limit.hom_ext
  intro i
  change f ≫ topologicalInverseProjection
      (qCcrParameterTopologicalDiagram Stage sys) i =
    qCcrParameterZeroFiberPointAmbientLimitMap Stage sys point hpoint ≫
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
  rw [h i]
  change point i ≫
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i =
    (qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint ≫
      qCcrParameterZeroFiberToParameterLimit Stage sys) ≫
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage sys) i
  rw [Category.assoc,
    qCcrParameterZeroFiberToParameterLimit_projection Stage sys i]
  change point i ≫
      (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i =
    qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint ≫
      (topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i ≫
        (qCcrParameterZeroFiberToParameterNatTrans Stage sys).app i)
  rw [← Category.assoc]
  rw [show qCcrParameterZeroFiberPointLimitMap Stage sys point hpoint ≫
      topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage sys) i =
      point i by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro u
    exact qCcrParameterZeroFiberPointLimitMap_projection
      Stage sys point hpoint i u]

end InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
