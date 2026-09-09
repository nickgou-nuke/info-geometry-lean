import InfoGeometry.Categorical.BraidGroup3PresentationBridge
import InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
import InfoGeometry.Categorical.LogJordanBraidGroup3Representation

/-!
# Standard logarithmic representation on the BraidProject B₃ stage

The checked logarithmic braid representation was first built using the newer
`FibonacciBraidGroup3Representation.BraidGroup3` presentation.  This file
transports it across the canonical presentation equivalence to
`Braid.braid_group 3`, the first nontrivial stage of the repository's general
`B_n → B_∞` tower.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidProject3Representation

open Braid
open InfoGeometry.Categorical.BraidGroup3PresentationBridge
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.FibonacciBraidGroup3Representation
open InfoGeometry.Categorical.LogJordanBraidGroup3Representation
open InfoGeometry.Categorical.LogNilpotentCrossCheckedR
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Clifford.LogCftMonodromy

/-- The standard Hadjiivanov logarithmic braid action written on the
`BraidProject` stage `braid_group 3`. -/
def standardHadjiivanovBraidProject3Hom :
    braid_group 3 →*
      (StandardTripleCarrier ≃ₗ[ℂ] StandardTripleCarrier) :=
  standardHadjiivanovBraidGroup3Hom.comp braidProjectToPresentedB3

/-- Native Mathlib representation on the `BraidProject` `B₃` stage. -/
def standardHadjiivanovBraidProject3Representation :
    Representation ℂ (braid_group 3) StandardTripleCarrier :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    standardHadjiivanovBraidProject3Hom

/-- First `BraidProject` generator acts by the checked logarithmic `R₁₂`. -/
@[simp]
theorem standardHadjiivanov_braidProject_sigmaZero :
    standardHadjiivanovBraidProject3Hom (σ' 2 (0 : Fin 2)) =
      logCheckedR12 standardJordanObject standardJordanObject_sq_zero
        logShearBase := by
  simp [standardHadjiivanovBraidProject3Hom]

/-- Second `BraidProject` generator acts by the checked logarithmic `R₂₃`. -/
@[simp]
theorem standardHadjiivanov_braidProject_sigmaOne :
    standardHadjiivanovBraidProject3Hom (σ' 2 (1 : Fin 2)) =
      logCheckedR23 standardJordanObject standardJordanObject_sq_zero
        logShearBase := by
  simp [standardHadjiivanovBraidProject3Hom]

/-- The same two abstract generators embed into the infinite braid boundary as
`σ₀` and `σ₁`.  This is the group-theoretic entry point from the concrete
logarithmic `B₃` action into the existing finite/infinite braid tower. -/
theorem braidProject3_generators_embed_to_infinite :
    finiteToInfiniteGroupHom 2 (σ' 2 (0 : Fin 2)) = σi 0 ∧
      finiteToInfiniteGroupHom 2 (σ' 2 (1 : Fin 2)) = σi 1 := by
  constructor <;> simp

/-- The `BraidProject` form still satisfies the Artin relation by group
homomorphism transport. -/
theorem standardHadjiivanov_braidProject_artin :
    standardHadjiivanovBraidProject3Hom (σ' 2 (0 : Fin 2)) *
        standardHadjiivanovBraidProject3Hom (σ' 2 (1 : Fin 2)) *
        standardHadjiivanovBraidProject3Hom (σ' 2 (0 : Fin 2)) =
      standardHadjiivanovBraidProject3Hom (σ' 2 (1 : Fin 2)) *
        standardHadjiivanovBraidProject3Hom (σ' 2 (0 : Fin 2)) *
        standardHadjiivanovBraidProject3Hom (σ' 2 (1 : Fin 2)) := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  exact braid_group.braid (n := 0) (i := (0 : Fin 1))

end InfoGeometry.Categorical.LogJordanBraidProject3Representation

