import InfoGeometry.Categorical.BraidGroup3PresentationBridge
import InfoGeometry.Categorical.LogJordanBraidProject3Representation
import InfoGeometry.Categorical.LogJordanCategoricalBraidGroup3Representation
import InfoGeometry.Categorical.LogJordanTensorPowerStabilization
import InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation

/-!
# Hadjiivanov checked R-matrix braid

Named capstone for the repository's logarithmic Hadjiivanov checked braid.

No operator or braid presentation is redefined here.  The file assembles the
existing owner chain

`logShearBase → checkR → YBE → B_n → B_∞ → tensor-power colimit`

and records the exact compatibility between the carrier representations, the
finite-nilpotent logarithmic category, finite braid stabilization, and the
single stabilized module colimit.
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
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
open InfoGeometry.Categorical.LogJordanBraidInfiniteGeneratorColimit
open InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
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

/-! ## Uniform finite Hadjiivanov braid tower -/

/-- Right-associated carrier of the standard Hadjiivanov logarithmic tensor
power. -/
abbrev hadjiivanovTensorPower (n : ℕ) :=
  tensorPowerObj standardJordanObject n

/-- The local Hadjiivanov checked-R inserted at the `i`th adjacent pair. -/
abbrev hadjiivanovTensorPowerGenerator
    (n : ℕ) (i : Fin (n + 1)) :=
  standardTensorPowerGenerator n i

/-- Uniform group-level action of `B_{n+2}` by adjacent Hadjiivanov checked-R
slices. -/
def hadjiivanovBraidProjectHom (n : ℕ) :
    braid_group (n + 2) →*
      (hadjiivanovTensorPower (n + 2) ≃ₗ[ℂ]
        hadjiivanovTensorPower (n + 2)) :=
  standardHadjiivanovBraidProjectHom n

/-- Native Mathlib representation at every finite braid stage. -/
def hadjiivanovBraidProjectRepresentation (n : ℕ) :
    Representation ℂ (braid_group (n + 2))
      (hadjiivanovTensorPower (n + 2)) :=
  standardHadjiivanovBraidProjectRepresentation n

/-- Every abstract Artin generator evaluates to its corresponding adjacent
Hadjiivanov checked-R slice. -/
@[simp]
theorem hadjiivanovBraidProject_sigma
    (n : ℕ) (i : Fin (n + 1)) :
    hadjiivanovBraidProjectHom n (σ' (n + 1) i) =
      hadjiivanovTensorPowerGenerator n i :=
  standardHadjiivanovBraidProject_sigma n i

/-- The four-strand stage simultaneously witnesses adjacent Yang--Baxter and
far commutation. -/
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

/-- The finite-stage Hadjiivanov actions are equivariant under right
stabilization by the primary spectator for every braid element. -/
theorem hadjiivanovBraidProject_stabilization
    (n : ℕ) (g : braid_group (n + 2)) :
    (appendPrimaryBonding (n + 1)).hom.comp
        (hadjiivanovBraidProjectHom n g).toLinearMap =
      (hadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)).toLinearMap.comp
        (appendPrimaryBonding (n + 1)).hom :=
  appendPrimaryBonding_braid_compat n g

/-! ## Global infinite braid action on the tensor-power colimit -/

/-- The stabilized logarithmic tensor-power carrier receiving the infinite
Hadjiivanov braid action. -/
abbrev hadjiivanovTensorPowerColimit := StandardTensorPowerColimit

/-- The `i`th infinite Artin generator acts by the canonical colimit
automorphism induced from the finite checked-R slices on its cofinal tail. -/
abbrev hadjiivanovInfiniteGenerator (i : ℕ) :
    Aut hadjiivanovTensorPowerColimit :=
  infiniteGeneratorAut i

/-- Global group action of the repository-owned presented `B_∞` on the single
stabilized logarithmic tensor-power colimit. -/
abbrev hadjiivanovBraidGroupInfHom :
    braid_group_inf →* Aut hadjiivanovTensorPowerColimit :=
  LogJordanBraidGroupInfRepresentation.hadjiivanovBraidGroupInfHom

/-- Global generator readback. -/
@[simp]
theorem hadjiivanovBraidGroupInf_sigma (i : ℕ) :
    hadjiivanovBraidGroupInfHom (σi i) = hadjiivanovInfiniteGenerator i :=
  LogJordanBraidGroupInfRepresentation.hadjiivanovBraidGroupInfHom_sigma i

/-- Finite-stage readback of every infinite generator once that generator is
present at the finite stage. -/
theorem hadjiivanovBraidGroupInf_sigma_stage
    (i n : ℕ) (h : i ≤ n) :
    stageInclusion n ≫ (hadjiivanovBraidGroupInfHom (σi i)).hom =
      ModuleCat.ofHom
          (hadjiivanovTensorPowerGenerator n ⟨i, by omega⟩).toLinearMap ≫
        stageInclusion n :=
  LogJordanBraidGroupInfRepresentation.hadjiivanovBraidGroupInf_sigma_stage
    i n h

end InfoGeometry.Categorical.HadjiivanovRMatrixBraid
