import InfoGeometry.Categorical.LogJordanBraidGroup3Representation
import InfoGeometry.Categorical.LogNilpotentCheckedRAdapter

/-!
# InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift

Categorical readback of the standard logarithmic `B₃` representation.

The presented-group representation is owned by
`LogJordanBraidGroup3Representation`.  The fact that its local checked-`R`
generators are genuine morphisms of the logarithmic triple tensor object is
owned by `LogNilpotentCheckedRAdapter`.

This file only identifies the two surfaces.  No new braid action or coherence
proof is introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift

open CategoryTheory
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanBraidGroup3Representation
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation
open InfoGeometry.Clifford.LogCftMonodromy

/-- Compatibility of the standard checked `R` with the distinguished tensor
nilpotent, in the exact form consumed by the generic categorical adapter. -/
theorem standardHadjiivanov_checkedR_commutes_tensorN :
    standardHadjiivanovCheckedRDatum.checkR.toLinearMap.comp
        (PairObj standardJordanObject).N =
      (PairObj standardJordanObject).N.comp
        standardHadjiivanovCheckedRDatum.checkR.toLinearMap := by
  exact logCheckedR_commutes_tensorN
    standardJordanObject standardJordanObject_sq_zero logShearBase

/-- First categorical braid generator on the standard logarithmic triple
object. -/
def standardCategoricalSigmaOne :
    TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  checkedR12Hom standardJordanObject standardHadjiivanovCheckedRDatum
    standardHadjiivanov_checkedR_commutes_tensorN

/-- Second categorical braid generator on the standard logarithmic triple
object. -/
def standardCategoricalSigmaTwo :
    TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  checkedR23Hom standardJordanObject standardHadjiivanovCheckedRDatum
    standardHadjiivanov_checkedR_commutes_tensorN

/-- The first categorical generator is exactly the underlying linear map of the
first generator of the standard presented-group representation. -/
theorem standardCategoricalSigmaOne_hom :
    standardCategoricalSigmaOne.hom =
      standardHadjiivanovBraidRepresentation sigmaOne := by
  rw [standardHadjiivanov_representation_sigmaOne]
  simpa [standardHadjiivanovCheckedRDatum] using
    (checkedR12Hom_hom standardJordanObject standardHadjiivanovCheckedRDatum
      standardHadjiivanov_checkedR_commutes_tensorN)

/-- The second categorical generator is exactly the underlying linear map of
the second generator of the standard presented-group representation. -/
theorem standardCategoricalSigmaTwo_hom :
    standardCategoricalSigmaTwo.hom =
      standardHadjiivanovBraidRepresentation sigmaTwo := by
  rw [standardHadjiivanov_representation_sigmaTwo]
  simpa [standardHadjiivanovCheckedRDatum] using
    (checkedR23Hom_hom standardJordanObject standardHadjiivanovCheckedRDatum
      standardHadjiivanov_checkedR_commutes_tensorN)

/-- The categorical generator morphisms satisfy the Artin/Yang--Baxter relation
inside the finite-nilpotent logarithmic category. -/
theorem standardCategorical_artin :
    standardCategoricalSigmaOne ≫ standardCategoricalSigmaTwo ≫
        standardCategoricalSigmaOne =
      standardCategoricalSigmaTwo ≫ standardCategoricalSigmaOne ≫
        standardCategoricalSigmaTwo := by
  exact checkedR_yangBaxter standardJordanObject
    standardHadjiivanovCheckedRDatum
    standardHadjiivanov_checkedR_commutes_tensorN

end InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift
