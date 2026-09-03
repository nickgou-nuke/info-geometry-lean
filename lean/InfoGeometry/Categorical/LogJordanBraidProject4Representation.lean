import InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
import InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
import proofs.BraidProject.BraidGroup

/-!
# Standard logarithmic B₄ representation

This is the first tensor-power stage where both kinds of Artin relations occur:
adjacent Yang--Baxter relations and far commutation.  The carrier and slice
operators come from `LogNilpotentTensorPowerBraid`; the group itself and its
universal map come from `BraidProject/BraidGroup`.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidProject4Representation

open Braid
open scoped TensorProduct

open InfoGeometry.Categorical.LogNilpotentModuleCategory
open InfoGeometry.Categorical.LogNilpotentModuleCategory.LogNilpotentModule
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Clifford.LogCftMonodromy

/-- Four-fold right-associated tensor carrier of the standard Jordan object. -/
abbrev StandardFourObject := tensorPowerObj standardJordanObject 4
abbrev StandardFourCarrier := StandardFourObject

/-- The three adjacent checked-R slices on the four-fold carrier. -/
def standardBraid4Generator (i : Fin 3) :
    StandardFourCarrier ≃ₗ[ℂ] StandardFourCarrier :=
  braidGeneratorLinearEquiv
    standardJordanObject standardHadjiivanovCheckedRLogIso 2 i

/-- Generator zero acts on the first two tensor factors. -/
@[simp]
theorem standardBraid4Generator_zero_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (0 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) +
        logShearBase •
          (standardJordanObject.N y ⊗ₜ[ℂ]
            (standardJordanObject.N x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) := by
  simp [standardBraid4Generator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso, tensorIso,
    standardHadjiivanovCheckedRLogIso, logCheckedRLogIso,
    checkedRIso, checkedRHom, standardHadjiivanovCheckedRDatum,
    logCheckedRDatum, logCheckedR_tmul]

/-- Generator one acts on the middle two tensor factors. -/
@[simp]
theorem standardBraid4Generator_one_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (1 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] w)) +
        logShearBase •
          (x ⊗ₜ[ℂ]
            (standardJordanObject.N z ⊗ₜ[ℂ]
              (standardJordanObject.N y ⊗ₜ[ℂ] w))) := by
  simp [standardBraid4Generator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso, tensorIso,
    standardHadjiivanovCheckedRLogIso, logCheckedRLogIso,
    checkedRIso, checkedRHom, standardHadjiivanovCheckedRDatum,
    logCheckedRDatum, logCheckedR_tmul]

/-- Generator two acts on the last two tensor factors. -/
@[simp]
theorem standardBraid4Generator_two_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (2 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) +
        logShearBase •
          (x ⊗ₜ[ℂ]
            (y ⊗ₜ[ℂ]
              (standardJordanObject.N w ⊗ₜ[ℂ]
                standardJordanObject.N z))) := by
  simp [standardBraid4Generator, braidGeneratorLinearEquiv,
    isoToLinearEquiv_apply, braidGeneratorIso, tensorIso,
    standardHadjiivanovCheckedRLogIso, logCheckedRLogIso,
    checkedRIso, checkedRHom, standardHadjiivanovCheckedRDatum,
    logCheckedRDatum, logCheckedR_tmul]

/-- First adjacent Artin relation on four tensor factors. -/
theorem standardBraid4_artin_zero_one :
    standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) =
      standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) := by
  apply LinearEquiv.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y tail₂
      refine TensorProduct.induction_on tail₂ ?_ ?_ ?_
      · simp
      · intro z w
        simp [LinearEquiv.mul_apply, standardBraid4Generator_zero_tmul,
          standardBraid4Generator_one_tmul,
          standardJordanObject_sq_zero, pow_two, Module.End.mul_eq_comp]
        module
      · intro a b ha hb
        simp [map_add, ha, hb]
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Second adjacent Artin relation on four tensor factors. -/
theorem standardBraid4_artin_one_two :
    standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) =
      standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) := by
  apply LinearEquiv.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y tail₂
      refine TensorProduct.induction_on tail₂ ?_ ?_ ?_
      · simp
      · intro z w
        simp [LinearEquiv.mul_apply, standardBraid4Generator_one_tmul,
          standardBraid4Generator_two_tmul,
          standardJordanObject_sq_zero, pow_two, Module.End.mul_eq_comp]
        module
      · intro a b ha hb
        simp [map_add, ha, hb]
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- Far commutation on disjoint tensor slots. -/
theorem standardBraid4_far_commute :
    standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) =
      standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) := by
  apply LinearEquiv.ext
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro x tail
    refine TensorProduct.induction_on tail ?_ ?_ ?_
    · simp
    · intro y tail₂
      refine TensorProduct.induction_on tail₂ ?_ ?_ ?_
      · simp
      · intro z w
        simp [LinearEquiv.mul_apply, standardBraid4Generator_zero_tmul,
          standardBraid4Generator_two_tmul]
        module
      · intro a b ha hb
        simp [map_add, ha, hb]
    · intro a b ha hb
      simp [map_add, ha, hb]
  · intro a b ha hb
    simp [map_add, ha, hb]

/-- The three standard slices satisfy every defining relation of
`Braid.braid_group 4`. -/
theorem standardBraid4_relations :
    ∀ r ∈ braid_rels 3,
      FreeGroup.lift standardBraid4Generator r =
        (1 : StandardFourCarrier ≃ₗ[ℂ] StandardFourCarrier) := by
  intro r hr
  change
    (∃ i : Fin 2, r = braid_rel i.castSucc i.succ) ∨
      (∃ i j : Fin 1, i ≤ j ∧
        r = comm_rel i.castSucc.castSucc j.succ.succ) at hr
  rcases hr with hAdj | hFar
  · rcases hAdj with ⟨i, rfl⟩
    fin_cases i
    · simp [braid_rel, FreeGroup.lift_apply_of, standardBraid4_artin_zero_one,
        mul_assoc]
    · simp [braid_rel, FreeGroup.lift_apply_of, standardBraid4_artin_one_two,
        mul_assoc]
  · rcases hFar with ⟨i, j, hij, rfl⟩
    fin_cases i
    fin_cases j
    simp [comm_rel, FreeGroup.lift_apply_of, standardBraid4_far_commute,
      mul_assoc]

/-- Group-level logarithmic braid action on `B₄`. -/
def standardHadjiivanovBraidProject4Hom :
    braid_group 4 →* (StandardFourCarrier ≃ₗ[ℂ] StandardFourCarrier) :=
  braid_group.toGroup standardBraid4Generator standardBraid4_relations

/-- Native Mathlib representation of `B₄` on the four-fold logarithmic tensor
carrier. -/
def standardHadjiivanovBraidProject4Representation :
    Representation ℂ (braid_group 4) StandardFourCarrier :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    standardHadjiivanovBraidProject4Hom

@[simp]
theorem standardHadjiivanovBraidProject4_sigma (i : Fin 3) :
    standardHadjiivanovBraidProject4Hom (σ' 3 i) =
      standardBraid4Generator i := by
  exact braid_group.toGroup_sigma standardBraid4Generator
    standardBraid4_relations i

/-- Stage-4 generators enter the existing infinite braid boundary unchanged. -/
theorem braidProject4_generators_embed_to_infinite (i : Fin 3) :
    finiteToInfiniteGroupHom 3 (σ' 3 i) = σi i.1 := by
  exact finiteToInfiniteGroupHom_sigma 3 i

end InfoGeometry.Categorical.LogJordanBraidProject4Representation
