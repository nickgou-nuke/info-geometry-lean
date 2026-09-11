import InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
import InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
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
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
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
  InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations.standardTensorPowerGenerator 2 i

/-- Generator zero acts on the first two tensor factors. -/
@[simp]
theorem standardBraid4Generator_zero_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (0 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) := by
  simpa [standardBraid4Generator] using
    (standardTensorPowerGenerator_zero_tmul (n := 1) x y
      (z ⊗ₜ[ℂ] w))

/-- Generator one acts on the middle two tensor factors. -/
@[simp]
theorem standardBraid4Generator_one_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (1 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      x ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] w)) := by
  simpa [standardBraid4Generator] using
    (standardTensorPowerGenerator_succ_tmul (n := 1) (i := 0) x
      (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)))

/-- Generator two acts on the last two tensor factors. -/
@[simp]
theorem standardBraid4Generator_two_tmul
    (x y z w : standardJordanObject) :
    standardBraid4Generator (2 : Fin 3)
        (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] z)) := by
  simpa [standardBraid4Generator] using
    (standardTensorPowerGenerator_succ_succ_tmul (n := 0) (i := 0) x y
      (z ⊗ₜ[ℂ] w))

/-- First adjacent Artin relation on four tensor factors. -/
theorem standardBraid4_artin_zero_one :
    standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) =
      standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) := by
  simpa [standardBraid4Generator] using
    (standardTensorPower_artin 1 (0 : Fin 2))

/-- Second adjacent Artin relation on four tensor factors. -/
theorem standardBraid4_artin_one_two :
    standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) =
      standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (1 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) := by
  simpa [standardBraid4Generator] using
    (standardTensorPower_artin 1 (1 : Fin 2))

/-- Far commutation on disjoint tensor slots. -/
theorem standardBraid4_far_commute :
    standardBraid4Generator (0 : Fin 3) *
        standardBraid4Generator (2 : Fin 3) =
      standardBraid4Generator (2 : Fin 3) *
        standardBraid4Generator (0 : Fin 3) := by
  simpa [standardBraid4Generator] using
    (standardTensorPower_far 0 (0 : Fin 1) (0 : Fin 1) (by simp))

/-- The three standard slices satisfy every defining relation of
`Braid.braid_group 4`. -/
theorem standardBraid4_relations :
    ∀ r ∈ braid_rels 3,
      FreeGroup.lift standardBraid4Generator r =
        (1 : StandardFourCarrier ≃ₗ[ℂ] StandardFourCarrier) := by
  intro r hr
  simpa [standardBraid4Generator] using
    (standardTensorPower_braidRelations 2 r hr)

/-- Group-level logarithmic braid action on `B₄`. -/
def standardHadjiivanovBraidProject4Hom :
    braid_group 4 →* (StandardFourCarrier ≃ₗ[ℂ] StandardFourCarrier) :=
  PresentedGroup.toGroup standardBraid4_relations

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
  exact PresentedGroup.toGroup.of standardBraid4_relations

/-- Stage-4 generators enter the existing infinite braid boundary unchanged. -/
theorem braidProject4_generators_embed_to_infinite (i : Fin 3) :
    finiteToInfiniteGroupHom 3 (σ' 3 i) = σi i.1 := by
  exact finiteToInfiniteGroupHom_sigma 3 i

end InfoGeometry.Categorical.LogJordanBraidProject4Representation
