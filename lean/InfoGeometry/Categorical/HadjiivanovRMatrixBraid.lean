import InfoGeometry.Categorical.BraidGroup3PresentationBridge
import InfoGeometry.Categorical.LogJordanBraidProject3Representation
import InfoGeometry.Categorical.LogJordanCategoricalBraidGroup3Representation

/-!
# Hadjiivanov checked R-matrix braid

Named capstone for the repository's logarithmic Hadjiivanov checked braid.

No operator or braid presentation is redefined here.  The file assembles the
existing owner chain

`logShearBase → checkR → YBE → BraidProject B₃ → categorical automorphisms`

and records the exact compatibility between the carrier representation and the
finite-nilpotent logarithmic category.
-/

noncomputable section

namespace InfoGeometry.Categorical.HadjiivanovRMatrixBraid

open CategoryTheory
open Braid

open InfoGeometry.Categorical.BraidGroup3PresentationBridge
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation
open InfoGeometry.Categorical.LogNilpotentCheckedRAdapter
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanBraidGroup3Representation
open InfoGeometry.Categorical.LogJordanBraidProject3Representation
open InfoGeometry.Categorical.LogJordanBraidGroup3CategoricalLift
open InfoGeometry.Categorical.LogJordanCategoricalBraidGroup3Representation
open InfoGeometry.Clifford.LogCftMonodromy

/-- The repository-owned Hadjiivanov checked R-matrix on the standard
rank-two logarithmic tensor square. -/
abbrev hadjiivanovCheckedR :=
  standardHadjiivanovCheckedRDatum.checkR

/-- The first local Hadjiivanov checked R-matrix on the right-associated tensor
cube. -/
abbrev hadjiivanovCheckedR12 :=
  standardHadjiivanovCheckedRDatum.checkR12

/-- The second local Hadjiivanov checked R-matrix on the right-associated tensor
cube. -/
abbrev hadjiivanovCheckedR23 :=
  standardHadjiivanovCheckedRDatum.checkR23

/-- The checked R-matrix intertwines the primitive logarithmic nilpotent on the
tensor square. -/
theorem hadjiivanovCheckedR_commutes_tensorN :
    hadjiivanovCheckedR.toLinearMap.comp
        (PairObj standardJordanObject).N =
      (PairObj standardJordanObject).N.comp
        hadjiivanovCheckedR.toLinearMap :=
  standardHadjiivanov_checkedR_commutes_tensorN

/-- The two local Hadjiivanov checked R-matrices satisfy the exact
Yang--Baxter/Artin equation. -/
theorem hadjiivanovCheckedR_yangBaxter :
    hadjiivanovCheckedR12.toLinearMap ∘ₗ
          hadjiivanovCheckedR23.toLinearMap ∘ₗ
          hadjiivanovCheckedR12.toLinearMap =
      hadjiivanovCheckedR23.toLinearMap ∘ₗ
          hadjiivanovCheckedR12.toLinearMap ∘ₗ
          hadjiivanovCheckedR23.toLinearMap :=
  standardHadjiivanov_yangBaxter

/-- The Hadjiivanov checked R-matrix is genuinely non-symmetric: its double
braiding is not the identity. -/
theorem hadjiivanovCheckedR_monodromy_ne_id :
    standardHadjiivanovCheckedRDatum.monodromy.toLinearMap ≠ LinearMap.id :=
  standardHadjiivanov_monodromy_ne_id

/-- The Hadjiivanov checked R-matrix as an automorphism of the logarithmic
tensor-square object. -/
abbrev hadjiivanovCheckedRLogIso :
    PairObj standardJordanObject ≅ PairObj standardJordanObject :=
  standardHadjiivanovCheckedRLogIso

/-- Categorical Hadjiivanov braid action on the actual `BraidProject` B₃ stage. -/
def hadjiivanovBraidProject3CategoricalHom :
    braid_group 3 →* Aut StandardTripleObject :=
  standardCategoricalBraidGroup3Hom.comp braidProjectToPresentedB3

/-- The first BraidProject generator acts by the first local categorical
Hadjiivanov checked R-matrix. -/
@[simp]
theorem hadjiivanovBraidProject3CategoricalHom_sigmaZero :
    hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2)) =
      standardCategoricalSigmaOneIso := by
  simp [hadjiivanovBraidProject3CategoricalHom]

/-- The second BraidProject generator acts by the second local categorical
Hadjiivanov checked R-matrix. -/
@[simp]
theorem hadjiivanovBraidProject3CategoricalHom_sigmaOne :
    hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2)) =
      standardCategoricalSigmaTwoIso := by
  simp [hadjiivanovBraidProject3CategoricalHom]

/-- The BraidProject action satisfies the Artin relation in the actual
automorphism group of the logarithmic tensor cube. -/
theorem hadjiivanovBraidProject3CategoricalHom_artin :
    hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2)) *
        hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2)) *
        hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2)) =
      hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2)) *
        hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2)) *
        hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2)) := by
  simp only [hadjiivanovBraidProject3CategoricalHom_sigmaZero,
    hadjiivanovBraidProject3CategoricalHom_sigmaOne]
  exact standardCategoricalBraidGroup3Hom_artin

/-- Forgetting the logarithmic categorical structure on the first generator
recovers the existing BraidProject carrier representation. -/
theorem hadjiivanov_sigmaZero_forget :
    (hadjiivanovBraidProject3CategoricalHom
      (σ' 2 (0 : Fin 2))).hom.hom =
        standardHadjiivanovBraidProject3Representation
          (σ' 2 (0 : Fin 2)) := by
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaZero]
  simpa [standardHadjiivanovBraidProject3Representation,
    standardHadjiivanovBraidProject3Hom] using
      standardCategoricalSigmaOne_hom

/-- Forgetting the logarithmic categorical structure on the second generator
recovers the existing BraidProject carrier representation. -/
theorem hadjiivanov_sigmaOne_forget :
    (hadjiivanovBraidProject3CategoricalHom
      (σ' 2 (1 : Fin 2))).hom.hom =
        standardHadjiivanovBraidProject3Representation
          (σ' 2 (1 : Fin 2)) := by
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaOne]
  simpa [standardHadjiivanovBraidProject3Representation,
    standardHadjiivanovBraidProject3Hom] using
      standardCategoricalSigmaTwo_hom

end InfoGeometry.Categorical.HadjiivanovRMatrixBraid
