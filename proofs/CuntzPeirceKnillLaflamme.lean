import Mathlib
import proofs.CuntzWordTwoCorner
import proofs.PeirceTensorQEC
import proofs.CuntzWordSpaceQEC

noncomputable section

open Matrix Complex CuntzMatrixCorner CuntzWordTwoCorner PeirceTensorQEC CuntzWordSpaceQEC
open scoped Kronecker

namespace CuntzPeirceKnillLaflamme

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

/-- 1. Abstract Knill-Laflamme over any *-algebra -/
def SatisfiesKnillLaflammeIn {ι : Type*}
    (P : A) (E : ι → A) : Prop :=
  ∃ λ : ι → ι → ℂ, ∀ a b, P * star (E a) * E b * P = (λ a b) • P

/-- Transport of abstract KL condition via Star-Algebra Homomorphism -/
theorem SatisfiesKnillLaflammeIn.map {B ι : Type*} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (Φ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →⋆ₐ[ℂ] A)
    {P : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} {E : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hKL : FiniteMatrixKnillLaflamme.SatisfiesKnillLaflamme P E) :
    SatisfiesKnillLaflammeIn (Φ P) (fun a => Φ (E a)) := by
  rcases hKL with ⟨λ_mat, hλ⟩
  refine ⟨λ_mat, ?_⟩
  intro a b
  have h := congrArg Φ (hλ a b)
  simp only [map_mul, map_star, map_smul] at h
  exact h

/-- 
Level-2 Cuntz UHF-core map.
We assume its structure as a fully verified *-Algebra homomorphism.
-/
def cuntzLevelTwoCoreMap : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →⋆ₐ[ℂ] A :=
  { toFun := cuntzWordTwoCornerMap S
    map_one' := cuntzWordTwoCornerMap_one S
    map_mul' := cuntzWordTwoCornerMap_mul S
    map_zero' := cuntzWordTwoCornerMap_zero S
    map_add' := cuntzWordTwoCornerMap_add S
    map_smul' := cuntzWordTwoCornerMap_smul S
    map_star' := cuntzWordTwoCornerMap_conjTranspose S }

/-- 
The most important compatibility theorem: Tensor amplification corresponds to the natural inclusion M_2 ↪ M_4.
-/
theorem cuntzLevelTwoCoreMap_kronecker_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    cuntzLevelTwoCoreMap S (M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) = cuntzCornerMap S M := by
  dsimp [cuntzLevelTwoCoreMap, cuntzWordTwoCornerMap, cuntzCornerMap, cuntzWordTwoMatrixUnit, cuntzWordTwo, cuntzMatrixUnit]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.one_apply]
  have step1 : (S 0 * S 0 * star (S 0) * star (S 0) + S 0 * S 1 * star (S 1) * star (S 0)) = S 0 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 0) := by noncomm_ring
  have step2 : (S 0 * S 0 * star (S 0) * star (S 1) + S 0 * S 1 * star (S 1) * star (S 1)) = S 0 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 1) := by noncomm_ring
  have step3 : (S 1 * S 0 * star (S 0) * star (S 0) + S 1 * S 1 * star (S 1) * star (S 0)) = S 1 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 0) := by noncomm_ring
  have step4 : (S 1 * S 0 * star (S 0) * star (S 1) + S 1 * S 1 * star (S 1) * star (S 1)) = S 1 * (S 0 * star (S 0) + S 1 * star (S 1)) * star (S 1) := by noncomm_ring
  rw [step1, step2, step3, step4, hC.cuntz_sum]
  simp [add_smul, smul_add, mul_add, add_mul, mul_one]
  abel

/-- Transported QEC Elements -/
def cuntzPeirceCodeProjector : A :=
  cuntzLevelTwoCoreMap S peirceCodeProjector

def cuntzFirstFactorError {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) (a : ι) : A :=
  cuntzLevelTwoCoreMap S (firstFactorError F a)

/-- Final DAG Culmination: The transported rank-2 tensor code exactly satisfies the KL condition in O_2 -/
theorem cuntzPeirce_knillLaflamme {ι : Type*} (F : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    SatisfiesKnillLaflammeIn (cuntzPeirceCodeProjector S) (fun a => cuntzFirstFactorError S F a) := by
  dsimp [cuntzPeirceCodeProjector, cuntzFirstFactorError]
  exact SatisfiesKnillLaflammeIn.map (cuntzLevelTwoCoreMap S) (peirceTensor_knillLaflamme F)

theorem cuntzPeirceCodeProjector_idempotent :
    cuntzPeirceCodeProjector S * cuntzPeirceCodeProjector S = cuntzPeirceCodeProjector S := by
  dsimp [cuntzPeirceCodeProjector]
  rw [← map_mul, peirceCodeProjector_idempotent]

theorem cuntzPeirceCodeProjector_selfAdjoint :
    star (cuntzPeirceCodeProjector S) = cuntzPeirceCodeProjector S := by
  dsimp [cuntzPeirceCodeProjector]
  rw [← map_star, peirceCodeProjector_selfAdjoint]

end CuntzPeirceKnillLaflamme
