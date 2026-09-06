import InfoGeometry.Categorical.BraidGroup3PresentationBridge
import InfoGeometry.Categorical.LogJordanBraidProject3Representation
import InfoGeometry.Categorical.LogJordanCategoricalBraidGroup3Representation
import InfoGeometry.Categorical.LogJordanTensorPowerStabilization
import InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
import InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility
import InfoGeometry.Categorical.BraidGroupInfiniteColimitIso

/-!
# Hadjiivanov checked R-matrix braid

Named capstone for the repository's logarithmic Hadjiivanov checked braid.
No operator or braid presentation is redefined here.
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
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanTensorPowerStabilization
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
open InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility
open InfoGeometry.Categorical.BraidGroupInfiniteColimitIso
open InfoGeometry.Clifford.LogCftMonodromy

abbrev hadjiivanovCheckedR := standardHadjiivanovCheckedRDatum.checkR
abbrev hadjiivanovCheckedR12 := standardHadjiivanovCheckedRDatum.checkR12
abbrev hadjiivanovCheckedR23 := standardHadjiivanovCheckedRDatum.checkR23

theorem hadjiivanovCheckedR_commutes_tensorN :
    hadjiivanovCheckedR.toLinearMap.comp (PairObj standardJordanObject).N =
      (PairObj standardJordanObject).N.comp hadjiivanovCheckedR.toLinearMap :=
  standardHadjiivanov_checkedR_commutes_tensorN

theorem hadjiivanovCheckedR_yangBaxter :
    hadjiivanovCheckedR12.toLinearMap ∘ₗ hadjiivanovCheckedR23.toLinearMap ∘ₗ
          hadjiivanovCheckedR12.toLinearMap =
      hadjiivanovCheckedR23.toLinearMap ∘ₗ hadjiivanovCheckedR12.toLinearMap ∘ₗ
          hadjiivanovCheckedR23.toLinearMap :=
  standardHadjiivanov_yangBaxter

theorem hadjiivanovCheckedR_monodromy_ne_id :
    standardHadjiivanovCheckedRDatum.monodromy.toLinearMap ≠ LinearMap.id :=
  standardHadjiivanov_monodromy_ne_id

abbrev hadjiivanovCheckedRLogIso :
    PairObj standardJordanObject ≅ PairObj standardJordanObject :=
  standardHadjiivanovCheckedRLogIso

def hadjiivanovBraidProject3CategoricalHom :
    braid_group 3 →* Aut StandardTripleObject :=
  standardCategoricalBraidGroup3Hom.comp braidProjectToPresentedB3

@[simp]
theorem hadjiivanovBraidProject3CategoricalHom_sigmaZero :
    hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2)) =
      standardCategoricalSigmaOneIso := by
  simp [hadjiivanovBraidProject3CategoricalHom]

@[simp]
theorem hadjiivanovBraidProject3CategoricalHom_sigmaOne :
    hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2)) =
      standardCategoricalSigmaTwoIso := by
  simp [hadjiivanovBraidProject3CategoricalHom]

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

theorem hadjiivanov_sigmaZero_forget :
    (hadjiivanovBraidProject3CategoricalHom (σ' 2 (0 : Fin 2))).hom.hom =
      standardHadjiivanovBraidProject3Representation (σ' 2 (0 : Fin 2)) := by
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaZero]
  simpa [standardHadjiivanovBraidProject3Representation,
    standardHadjiivanovBraidProject3Hom] using standardCategoricalSigmaOne_hom

theorem hadjiivanov_sigmaOne_forget :
    (hadjiivanovBraidProject3CategoricalHom (σ' 2 (1 : Fin 2))).hom.hom =
      standardHadjiivanovBraidProject3Representation (σ' 2 (1 : Fin 2)) := by
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaOne]
  simpa [standardHadjiivanovBraidProject3Representation,
    standardHadjiivanovBraidProject3Hom] using standardCategoricalSigmaTwo_hom

abbrev hadjiivanovTensorPower (n : ℕ) := tensorPowerObj standardJordanObject n
abbrev hadjiivanovTensorPowerGenerator (n : ℕ) (i : Fin (n + 1)) :=
  standardTensorPowerGenerator n i

def hadjiivanovBraidProjectHom (n : ℕ) :
    braid_group (n + 2) →*
      (hadjiivanovTensorPower (n + 2) ≃ₗ[ℂ] hadjiivanovTensorPower (n + 2)) :=
  standardHadjiivanovBraidProjectHom n

def hadjiivanovBraidProjectRepresentation (n : ℕ) :
    Representation ℂ (braid_group (n + 2)) (hadjiivanovTensorPower (n + 2)) :=
  standardHadjiivanovBraidProjectRepresentation n

@[simp]
theorem hadjiivanovBraidProject_sigma (n : ℕ) (i : Fin (n + 1)) :
    hadjiivanovBraidProjectHom n (σ' (n + 1) i) =
      hadjiivanovTensorPowerGenerator n i :=
  standardHadjiivanovBraidProject_sigma n i

theorem hadjiivanovBraidProject_stage4_relations :
    hadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) =
      hadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (1 : Fin 3)) ∧
    hadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (2 : Fin 3)) =
      hadjiivanovBraidProjectHom 2 (σ' 3 (2 : Fin 3)) *
        hadjiivanovBraidProjectHom 2 (σ' 3 (0 : Fin 3)) := by
  exact standardTensorPower_stage4_relation_packet

theorem hadjiivanovBraidProject_stabilization
    (n : ℕ) (g : braid_group (n + 2)) :
    (appendPrimaryBonding (n + 1)).hom.comp
        (hadjiivanovBraidProjectHom n g).toLinearMap =
      (hadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom :=
  appendPrimaryBonding_braid_compat n g

abbrev hadjiivanovBraidInfinity := hadjiivanovBraidGroupInfHom

theorem hadjiivanov_finite_to_infinite
    (n : ℕ) (g : braid_group (n + 2)) :=
  hadjiivanov_finite_infinite_compatibility_hom n g

abbrev braidInfinityColimitIso := braidGroupColimitIsoInfinite
abbrev braidInfinityIsColimit := braidGroupBoundaryCoconeIsColimit

end InfoGeometry.Categorical.HadjiivanovRMatrixBraid