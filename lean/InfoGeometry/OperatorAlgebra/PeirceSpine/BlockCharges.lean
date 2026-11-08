import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismBlocks

/-!
# Charges of supported endomorphism components

The Peirce projections carry degrees -1, 0, 1 on both sides of ad P.
Consequently an arbitrary ordered block has charge output minus input.
The five support-defined components therefore belong to the stated charge
sectors, even when distinct integer charges act identically in B.
-/
namespace InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.LieJordan
variable {B : Type*} [Ring B]

def peirceDegree (i : Fin 3) : ℤ := ![-1, 0, 1] i

private theorem projection_left {P : B} (hP : P * P = P) (i : Fin 3) :
    lieOp ℤ P * threePeirceProjection P i =
      peirceDegree i • threePeirceProjection P i := by
  fin_cases i <;> ext X <;>
    simp [peirceDegree, threePeirceProjection, lieOp_apply, sandwichOp_apply,
      InfoGeometry.Core.PeirceGrading.even,
      InfoGeometry.Core.PeirceDecomposition.component11,
      InfoGeometry.Core.PeirceDecomposition.component00,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, P_mul_P' hP]

private theorem projection_right {P : B} (hP : P * P = P) (i : Fin 3) :
    threePeirceProjection P i * lieOp ℤ P =
      peirceDegree i • threePeirceProjection P i := by
  fin_cases i <;> ext X <;>
    simp [peirceDegree, threePeirceProjection, lieOp_apply, sandwichOp_apply,
      InfoGeometry.Core.PeirceGrading.even,
      InfoGeometry.Core.PeirceDecomposition.component11,
      InfoGeometry.Core.PeirceDecomposition.component00,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      mul_add, add_mul, mul_sub, sub_mul, mul_assoc, hP, P_mul_P' hP]

theorem endomorphismBlock_mem_sector {P : B} (hP : P * P = P)
    (i j : Fin 3) (K : Module.End ℤ B) :
    endomorphismBlock P i j K ∈ chargeSector P (peirceDegree i - peirceDegree j) := by
  rw [mem_chargeSector]
  change lieOp ℤ P * (threePeirceProjection P i * K * threePeirceProjection P j) -
    (threePeirceProjection P i * K * threePeirceProjection P j) * lieOp ℤ P = _
  rw [← mul_assoc (lieOp ℤ P), ← mul_assoc (lieOp ℤ P), projection_left hP,
    mul_assoc (threePeirceProjection P i * K), projection_right hP]
  simp only [smul_mul_assoc, mul_smul_comm, sub_smul, endomorphismBlock]

/-- The five reconstructed components have charges -2, -1, 0, 1, 2. -/
theorem fiveSupportedComponent_mem_sector {P : B} (hP : P * P = P)
    (K : Module.End ℤ B) (d : Fin 5) :
    fiveSupportedComponent P K d ∈ chargeSector P ((d.val : ℤ) - 2) := by
  have h00 : endomorphismBlock P 0 0 K ∈ chargeSector P (0) := by
    have h := endomorphismBlock_mem_sector hP 0 0 K
    norm_num [peirceDegree] at h
    exact h
  have h01 : endomorphismBlock P 0 1 K ∈ chargeSector P (-1) := by
    have h := endomorphismBlock_mem_sector hP 0 1 K
    norm_num [peirceDegree] at h
    exact h
  have h02 : endomorphismBlock P 0 2 K ∈ chargeSector P (-2) := by
    have h := endomorphismBlock_mem_sector hP 0 2 K
    norm_num [peirceDegree] at h
    exact h
  have h10 : endomorphismBlock P 1 0 K ∈ chargeSector P (1) := by
    have h := endomorphismBlock_mem_sector hP 1 0 K
    norm_num [peirceDegree] at h
    exact h
  have h11 : endomorphismBlock P 1 1 K ∈ chargeSector P (0) := by
    have h := endomorphismBlock_mem_sector hP 1 1 K
    norm_num [peirceDegree] at h
    exact h
  have h12 : endomorphismBlock P 1 2 K ∈ chargeSector P (-1) := by
    have h := endomorphismBlock_mem_sector hP 1 2 K
    norm_num [peirceDegree] at h
    exact h
  have h20 : endomorphismBlock P 2 0 K ∈ chargeSector P (2) := by
    have h := endomorphismBlock_mem_sector hP 2 0 K
    norm_num [peirceDegree] at h
    exact h
  have h21 : endomorphismBlock P 2 1 K ∈ chargeSector P (1) := by
    have h := endomorphismBlock_mem_sector hP 2 1 K
    norm_num [peirceDegree] at h
    exact h
  have h22 : endomorphismBlock P 2 2 K ∈ chargeSector P (0) := by
    have h := endomorphismBlock_mem_sector hP 2 2 K
    norm_num [peirceDegree] at h
    exact h
  fin_cases d <;> norm_num [fiveSupportedComponent]
  · exact h02
  · exact (chargeSector P (-1)).add_mem h01 h12
  · exact (chargeSector P 0).add_mem ((chargeSector P 0).add_mem h00 h11) h22
  · exact (chargeSector P 1).add_mem h10 h21
  · exact h20

end InfoGeometry.OperatorAlgebra.PeirceSpine
