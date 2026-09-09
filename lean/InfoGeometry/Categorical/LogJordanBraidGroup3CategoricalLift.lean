import InfoGeometry.Categorical.LogJordanBraidGroup3Representation
import InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
import InfoGeometry.Categorical.LogNilpotentAmbientSymmetric

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
open InfoGeometry.Categorical.LogEndModuleCategory
open InfoGeometry.Categorical.LogEndModuleCategory.LogEndModule
open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.LogNilpotentAmbientSymmetric
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanBraidGroup3Representation
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation
open InfoGeometry.Clifford.LogCftMonodromy

/-- Compatibility of the standard checked `R` with the distinguished tensor
nilpotent, in the exact form consumed by the generic categorical adapter. -/
theorem standardHadjiivanov_checkedR_commutes_tensorN :
    standardSymmetricSigmaOne.hom.comp
        (TripleObj standardJordanObject).N =
      (TripleObj standardJordanObject).N.comp standardSymmetricSigmaOne.hom := by
  exact standardSymmetricSigmaOne.comm

/-- First categorical braid generator on the standard logarithmic triple
object. -/
def standardCategoricalSigmaOne :
    TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  standardSymmetricSigmaOne

/-- Second categorical braid generator on the standard logarithmic triple
object. -/
def standardCategoricalSigmaTwo :
    TripleObj standardJordanObject ⟶ TripleObj standardJordanObject :=
  standardSymmetricSigmaTwo

/-- The first categorical generator is exactly the underlying linear map of the
first generator of the standard presented-group representation. -/
theorem standardCategoricalSigmaOne_hom :
    standardCategoricalSigmaOne.hom =
      standardHadjiivanovBraidRepresentation sigmaOne := by
  rw [standardHadjiivanov_representation_sigmaOne]
  rfl

/-- The second categorical generator is exactly the underlying linear map of
the second generator of the standard presented-group representation. -/
theorem standardCategoricalSigmaTwo_hom :
    standardCategoricalSigmaTwo.hom =
      standardHadjiivanovBraidRepresentation sigmaTwo := by
  rw [standardHadjiivanov_representation_sigmaTwo]
  rfl

/-- The categorical generator morphisms satisfy the Artin/Yang--Baxter relation
inside the finite-nilpotent logarithmic category. -/
theorem standardCategorical_artin :
    standardCategoricalSigmaOne ≫ standardCategoricalSigmaTwo ≫
        standardCategoricalSigmaOne =
      standardCategoricalSigmaTwo ≫ standardCategoricalSigmaOne ≫
        standardCategoricalSigmaTwo := by
  letI : BraidedCategory (LogNilpotentModule ℂ) := ambientBraidedCategory
  simpa [standardCategoricalSigmaOne, standardCategoricalSigmaTwo,
    standardSymmetricSigmaOne, standardSymmetricSigmaTwo,
    LogNilpotentModule.hom_comp] using
    (congrArg (fun e => e.hom)
      (CategoryTheory.BraidedCategory.yang_baxter_iso
        standardJordanObject standardJordanObject standardJordanObject))

end InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift
