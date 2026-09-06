import InfoGeometry.Algebra.TripotentClSUSYBridge

/-!
# Peirce projector consequences for the native Cl(1,1) tripotent

The existing tripotent owner supplies the `p₊`, `p₋`, and vacuum formulas.
This bridge closes the remaining elementary projector laws under the native
relation `O² = 1`; it does not claim a general TKK construction.
-/

namespace TripotentClSUSYBridge

open Cl11Fermions

variable (O : CliffordAlgebra Cl11Fermions.q11)

theorem projVac_zero_of_sq_one (hO2 : O ^ 2 = 1) :
    projVac O = 0 := by
  simp [projVac, hO2]

theorem projVac_idem_of_sq_one (hO2 : O ^ 2 = 1) :
    projVac O * projVac O = projVac O := by
  rw [projVac_zero_of_sq_one O hO2]
  simp

theorem projDown_idem_of_sq_one (hO2 : O ^ 2 = 1) :
    projDown O * projDown O = projDown O := by
  have hrel : projDown O = 1 - projUp O := by
    dsimp [projDown, projUp]
    rw [hO2]
    simp only [Algebra.smul_def, mul_sub, mul_add, mul_one]
    have ha :
        algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) +
            algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) = 1 := by
      rw [← map_add]
      norm_num
    rw [← ha]
    abel
  rw [hrel]
  have hup := projUp_idem O hO2
  calc
    (1 - projUp O) * (1 - projUp O) =
        1 - projUp O - projUp O + projUp O * projUp O := by
          noncomm_ring
    _ = 1 - projUp O := by rw [hup]; noncomm_ring

theorem projUp_projDown_zero_of_sq_one (hO2 : O ^ 2 = 1) :
    projUp O * projDown O = 0 := by
  have hrel : projDown O = 1 - projUp O := by
    dsimp [projDown, projUp]
    rw [hO2]
    simp only [Algebra.smul_def, mul_sub, mul_add, mul_one]
    have ha :
        algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) +
            algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) = 1 := by
      rw [← map_add]
      norm_num
    rw [← ha]
    abel
  rw [hrel]
  have hup := projUp_idem O hO2
  calc
    projUp O * (1 - projUp O) = projUp O - projUp O * projUp O := by
      noncomm_ring
    _ = 0 := by rw [hup]; simp

theorem projDown_projUp_zero_of_sq_one (hO2 : O ^ 2 = 1) :
    projDown O * projUp O = 0 := by
  have hrel : projDown O = 1 - projUp O := by
    dsimp [projDown, projUp]
    rw [hO2]
    simp only [Algebra.smul_def, mul_sub, mul_add, mul_one]
    have ha :
        algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) +
            algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) = 1 := by
      rw [← map_add]
      norm_num
    rw [← ha]
    abel
  rw [hrel]
  have hup := projUp_idem O hO2
  calc
    (1 - projUp O) * projUp O =
        projUp O - projUp O * projUp O := by
          noncomm_ring
    _ = 0 := by rw [hup]; simp

theorem tripotent_projUp_eigen_of_sq_one (hO2 : O ^ 2 = 1) :
    O * projUp O = projUp O := by
  dsimp [projUp]
  simp only [Algebra.smul_def, mul_add, mul_one]
  rw [hO2]
  have hcentral :
      O * (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ)) =
        algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) * O := by
    exact (Algebra.commutes (1 / 2 : ℚ) O).symm
  simp only [mul_one]
  rw [← mul_assoc O (algebraMap ℚ _ (1 / 2 : ℚ)) O, hcentral]
  rw [mul_assoc, ← pow_two, hO2]
  noncomm_ring

theorem tripotent_projDown_eigen_of_sq_one (hO2 : O ^ 2 = 1) :
    O * projDown O = -projDown O := by
  dsimp [projDown]
  simp only [Algebra.smul_def, mul_sub, mul_one]
  rw [hO2]
  have hcentral :
      O * (algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ)) =
        algebraMap ℚ (CliffordAlgebra Cl11Fermions.q11) (1 / 2 : ℚ) * O := by
    exact (Algebra.commutes (1 / 2 : ℚ) O).symm
  simp only [mul_one]
  rw [← mul_assoc O (algebraMap ℚ _ (1 / 2 : ℚ)) O, hcentral]
  rw [mul_assoc, ← pow_two, hO2]
  noncomm_ring

end TripotentClSUSYBridge
