import InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitObservable
import InfoGeometry.Topology.D4StarQuotientSeparation

/-!
# Witness-gated D₄ crossed-product Bool readout

The crossed-product coefficient carrier does not have a canonical map to the
coarse star quotient.  This owner therefore takes such stage maps as explicit
witnesses, composes them with the native `quotientToBool`, and descends the
result through the topological colimit.  No unsupported canonical readout is
introduced.
-/

namespace InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitBoolReadout

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalColimit
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductTopologicalTransitions
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitDynamics
open InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitObservable
open InfoGeometry.Topology.ColimitDynamics
open InfoGeometry.Topology.PauliJungD4Star

noncomputable section

variable {I : Type*} [Preorder I]
variable {T : ContinuousD4StarCrossedProductTransitionSystem I}
variable (F : ContinuousD4StarCrossedProductFlowSystem T)

def quotientToBoolTopCat :
    TopCat.of D4StarQuotient ⟶ TopCat.of Bool :=
  TopCat.ofHom
    { toFun := quotientToBool
      continuous_toFun := continuous_quotientToBool }

@[simp] theorem quotientToBoolTopCat_apply (q : D4StarQuotient) :
    quotientToBoolTopCat q = quotientToBool q := rfl

theorem quotientToBoolTopCat_continuous :
    Continuous (quotientToBoolTopCat :
      TopCat.of D4StarQuotient ⟶ TopCat.of Bool) := by
  exact continuous_quotientToBool

def boolToQuotientTopCat :
    TopCat.of Bool ⟶ TopCat.of D4StarQuotient :=
  TopCat.ofHom
    { toFun := boolToQuotient
      continuous_toFun := continuous_boolToQuotient }

@[simp] theorem boolToQuotientTopCat_apply (b : Bool) :
    boolToQuotientTopCat b = boolToQuotient b := rfl

abbrev D4StarQuotientReadout : Type _ :=
  {stageQuotient : ∀ i : I,
      TopCat.of D4StarCrossedProduct ⟶ TopCat.of D4StarQuotient //
    (∀ {i j : I} (hij : i ≤ j),
      T.transitionTopCatHom hij ≫ stageQuotient j = stageQuotient i) ∧
    (∀ (i : I) (t : ℤ),
      F.stageFlow i t ≫ stageQuotient i = stageQuotient i)}

variable (R : D4StarQuotientReadout F)

include R

def toQuotientObservables :
    FlowInvariantObservableData F (TopCat.of D4StarQuotient) :=
  ⟨R.1, R.2⟩

def toBoolObservables :
    FlowInvariantObservableData F (TopCat.of Bool) :=
  ⟨(fun i => R.1 i ≫ quotientToBoolTopCat),
    ⟨by
      intro i j hij
      rw [← Category.assoc, R.2.1 hij],
      by
        intro i t
        rw [← Category.assoc, R.2.2 i t]⟩⟩

noncomputable def colimitBoolObservable
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) : C.pt ⟶ TopCat.of Bool :=
  colimitObservable F (TopCat.of Bool) (toBoolObservables F R) C hC

noncomputable def colimitQuotientObservable
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) :
    C.pt ⟶ TopCat.of D4StarQuotient :=
  colimitObservable F (TopCat.of D4StarQuotient)
    (toQuotientObservables F R) C hC

@[simp] theorem colimitQuotientObservable_stage
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (i : I) :
    C.ι.app i ≫ colimitQuotientObservable F R C hC =
      R.1 i := by
  exact colimitObservable_stage F (TopCat.of D4StarQuotient)
    (toQuotientObservables F R) C hC i

theorem colimitQuotientObservable_invariant
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (t : ℤ) :
    colimitEndomorphism F C hC t ≫ colimitQuotientObservable F R C hC =
      colimitQuotientObservable F R C hC := by
  exact colimitObservable_invariant F (TopCat.of D4StarQuotient)
    (toQuotientObservables F R) C hC t

@[simp] theorem colimitBoolObservable_stage
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (i : I) :
    C.ι.app i ≫ colimitBoolObservable F R C hC =
      R.1 i ≫ quotientToBoolTopCat := by
  exact colimitObservable_stage F (TopCat.of Bool)
    (toBoolObservables F R) C hC i

theorem colimitBoolObservable_factorization
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) :
    colimitBoolObservable F R C hC =
      colimitQuotientObservable F R C hC ≫ quotientToBoolTopCat := by
  apply hC.hom_ext
  intro i
  rw [← Category.assoc, colimitBoolObservable_stage,
    colimitQuotientObservable_stage]

theorem colimitBoolObservable_roundtrip
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) :
    colimitBoolObservable F R C hC ≫ boolToQuotientTopCat =
      colimitQuotientObservable F R C hC := by
  apply hC.hom_ext
  intro i
  rw [← Category.assoc, colimitBoolObservable_stage,
    colimitQuotientObservable_stage]
  ext q
  exact boolToQuotient_quotientToBool (R.1 i q)

theorem colimitBoolObservable_invariant
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) (t : ℤ) :
    colimitEndomorphism F C hC t ≫ colimitBoolObservable F R C hC =
      colimitBoolObservable F R C hC := by
  exact colimitObservable_invariant F (TopCat.of Bool)
    (toBoolObservables F R) C hC t

theorem colimitBoolObservable_continuous
    (C : Cocone (topologicalDiagram T))
    (hC : IsColimit C) :
    Continuous (colimitBoolObservable F R C hC) := by
  exact (colimitBoolObservable F R C hC).hom.continuous

end

end InfoGeometry.OperatorAlgebra.D4StarCrossedProductColimitBoolReadout
