/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.BraidGroup3PresentationBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.LogJordanBraidProject3Representation
import InfoGeometry.Categorical.LogJordanCategoricalBraidGroup3Representation
import InfoGeometry.Categorical.LogJordanTensorPowerStabilization
import InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
import InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility
import InfoGeometry.Categorical.BraidGroupInfiniteColimitIso
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
import InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge
import InfoGeometry.Clifford.LogCftMonodromy

/-!
# Hadjiivanov checked R-matrix braid

Named capstone for the repository's logarithmic Hadjiivanov checked braid.

No operator or braid presentation is redefined here.  The file assembles the
existing owner chain

`logShearBase → checkR → YBE → B_n → B_∞ → Aut(colim J^{⊗n})`

and records the exact compatibility between finite stages, the infinite braid
group, and the finite-stage group colimit.
-/

noncomputable section

namespace InfoGeometry.Categorical.HadjiivanovRMatrixBraid

open CategoryTheory
open Braid

open scoped TensorProduct

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
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
open InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility
open InfoGeometry.Categorical.BraidGroupInfiniteColimitIso
open InfoGeometry.Clifford.LogCftMonodromy

/- The symmetric logarithmic checked braid below has identity monodromy.  The
genuine non-symmetric Hadjiivanov shear operator and its strictly nontrivial
double braiding are exposed at the end of this file from the proved owners
`shearCheckedR` and `standardHadjiivanov_shear_monodromy_ne_id`; no datum is
used.  The finite and infinite braid lanes use the symmetric logarithmic
braiding through `standardTensorPowerGenerator`. -/

/-- Categorical Hadjiivanov braid action on the actual `BraidProject` B₃ stage. -/
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
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaZero,
    standardCategoricalSigmaOneIso_hom,
    standardCategoricalSigmaOne_hom]
  change standardHadjiivanovBraidRepresentation sigmaOne =
    standardHadjiivanovBraidRepresentation
      (braidProjectToPresentedB3 (σ' 2 (0 : Fin 2)))
  exact congrArg standardHadjiivanovBraidRepresentation
    braidProjectToPresentedB3_sigmaZero.symm

/-- Forgetting the logarithmic categorical structure on the second generator
recovers the existing BraidProject carrier representation. -/
theorem hadjiivanov_sigmaOne_forget :
    (hadjiivanovBraidProject3CategoricalHom
      (σ' 2 (1 : Fin 2))).hom.hom =
        standardHadjiivanovBraidProject3Representation
          (σ' 2 (1 : Fin 2)) := by
  rw [hadjiivanovBraidProject3CategoricalHom_sigmaOne,
    standardCategoricalSigmaTwoIso_hom,
    standardCategoricalSigmaTwo_hom]
  change standardHadjiivanovBraidRepresentation sigmaTwo =
    standardHadjiivanovBraidRepresentation
      (braidProjectToPresentedB3 (σ' 2 (1 : Fin 2)))
  exact congrArg standardHadjiivanovBraidRepresentation
    braidProjectToPresentedB3_sigmaOneIndex.symm

/-! ## Uniform finite Hadjiivanov braid tower -/

abbrev hadjiivanovTensorPower (n : ℕ) :=
  tensorPowerObj standardJordanObject n

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

/-! ## Infinite braid / colimit closure -/

/-- The repository-owned presented infinite braid group acts on the single
native stabilized tensor-power colimit. -/
abbrev hadjiivanovBraidInfinity :=
  hadjiivanovBraidGroupInfHom

/-- Arbitrary finite braid elements agree with their canonical `B_∞` images
after passage to the stabilized tensor-power colimit. -/
theorem hadjiivanov_finite_to_infinite
    (n : ℕ) (g : braid_group (n + 2)) :
    ModuleCat.ofHom (hadjiivanovBraidProjectHom n g).toLinearMap ≫
        stageInclusion n =
      stageInclusion n ≫
        (hadjiivanovBraidGroupInfHom (finiteToInfiniteGroupHom (n + 1) g)).hom :=
  hadjiivanov_finite_infinite_compatibility_hom n g

/-- Structural group-theoretic closure: the repository-presented `B_∞` is
canonically isomorphic to Mathlib's colimit of the finite stabilization tower. -/
abbrev braidInfinityColimitIso :=
  braidGroupColimitIsoInfinite

/-- The existing `B_∞` boundary cocone is a genuine colimit cocone. -/
abbrev braidInfinityIsColimit :=
  braidGroupBoundaryCoconeIsColimit


/-- The genuine checked logarithmic braid operator on the standard rank-two
cell at the Hadjiivanov parameter (no datum wrapper). -/
abbrev hadjiivanovCheckedR :
    (InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V ⊗[ℂ]
      InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V) ≃ₗ[ℂ]
    (InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V ⊗[ℂ]
      InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V) :=
  InfoGeometry.Categorical.LogNilpotentCrossCheckedR.logCheckedR
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject_sq_zero
    logShearBase

abbrev hadjiivanovCheckedR12 :=
  InfoGeometry.Categorical.LogNilpotentCrossCheckedR.logCheckedR12
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject_sq_zero
    logShearBase

abbrev hadjiivanovCheckedR23 :=
  InfoGeometry.Categorical.LogNilpotentCrossCheckedR.logCheckedR23
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject_sq_zero
    logShearBase

theorem hadjiivanovCheckedR_commutes_tensorN :
    hadjiivanovCheckedR.toLinearMap.comp
        (PairObj InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject).N =
      (PairObj InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject).N.comp
        hadjiivanovCheckedR.toLinearMap :=
  InfoGeometry.Categorical.LogNilpotentCrossCheckedR.logCheckedR_commutes_tensorN
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject_sq_zero
    logShearBase

theorem hadjiivanovCheckedR_yangBaxter :
    hadjiivanovCheckedR12.toLinearMap ∘ₗ hadjiivanovCheckedR23.toLinearMap ∘ₗ
          hadjiivanovCheckedR12.toLinearMap =
      hadjiivanovCheckedR23.toLinearMap ∘ₗ hadjiivanovCheckedR12.toLinearMap ∘ₗ
          hadjiivanovCheckedR23.toLinearMap :=
  InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standard_logCheckedR_yangBaxter

/-- The genuine non-symmetric Hadjiivanov checked braid: a finite unipotent
shear followed by the tensor flip at the universal Hadjiivanov parameter. -/
abbrev hadjiivanovShearR :
    (InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V ⊗[ℂ]
      InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V) ≃ₗ[ℂ]
    (InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V ⊗[ℂ]
      InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject.toLogEndModule.V) :=
  InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.shearCheckedR
    InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardJordanObject_sq_zero
    logShearBase

/-- Nontrivial double braiding of the genuine Hadjiivanov shear operator,
inherited from the proved owner (no non-symmetric datum). -/
theorem hadjiivanovShearR_monodromy_ne_id :
    (hadjiivanovShearR.trans hadjiivanovShearR).toLinearMap ≠ LinearMap.id :=
  InfoGeometry.Categorical.LogJordanCheckedRBraidBridge.standardHadjiivanov_shear_monodromy_ne_id

/-- The genuine categorical checked-`R` isomorphism for the Hadjiivanov shear
on the standard rank-two cell (no datum witness). -/
abbrev hadjiivanovCheckedRLogIso :=
  InfoGeometry.Categorical.LogJordanHadjiivanovBraidingBridge.standardHadjiivanovCheckedRLogIso

end InfoGeometry.Categorical.HadjiivanovRMatrixBraid
