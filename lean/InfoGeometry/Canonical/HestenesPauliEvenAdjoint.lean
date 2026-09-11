import InfoGeometry.Canonical.HestenesPauliEvenClifford
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.HestenesPauliEvenClifford

noncomputable def hestenesHermitianAdjoint (x : ClPlus14) : ClPlus14 :=
  (clPlusPauliAlgEquiv).symm (star ((clPlusPauliAlgEquiv) x))

theorem hestenesHermitianAdjoint_one :
    hestenesHermitianAdjoint (1 : ClPlus14) = 1 := by
  simp [hestenesHermitianAdjoint]

theorem hestenesHermitianAdjoint_add (x y : ClPlus14) :
    hestenesHermitianAdjoint (x + y) =
      hestenesHermitianAdjoint x + hestenesHermitianAdjoint y := by
  simp [hestenesHermitianAdjoint]

theorem hestenesHermitianAdjoint_smul (r : ℝ) (x : ClPlus14) :
    hestenesHermitianAdjoint (r • x) =
      r • hestenesHermitianAdjoint x := by
  simp [hestenesHermitianAdjoint]

theorem hestenesHermitianAdjoint_mul (x y : ClPlus14) :
    hestenesHermitianAdjoint (x * y) =
      hestenesHermitianAdjoint y * hestenesHermitianAdjoint x := by
  simp [hestenesHermitianAdjoint]

theorem hestenesHermitianAdjoint_involutive (x : ClPlus14) :
    hestenesHermitianAdjoint (hestenesHermitianAdjoint x) = x := by
  simp [hestenesHermitianAdjoint]

theorem hestenesHermitianAdjoint_sigma1 :
    hestenesHermitianAdjoint sigma1 = sigma1 := by
  apply (clPlusPauliAlgEquiv).injective
  simp only [hestenesHermitianAdjoint, AlgEquiv.apply_symm_apply]
  change Matrix.conjTranspose (clPlusToPauli sigma1) = clPlusToPauli sigma1
  rw [clPlusToPauli_sigma1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChiralStokesPauliBasis.sheetFlip, Matrix.conjTranspose_apply]

noncomputable def hestenesPauliKreinAdjoint (x : ClPlus14) : ClPlus14 :=
  sigma1 * hestenesHermitianAdjoint x * sigma1

theorem sigma1_sq : sigma1 * sigma1 = (1 : ClPlus14) := by
  apply clPlusToPauli_injective
  rw [map_mul, clPlusToPauli_sigma1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ChiralStokesPauliBasis.sheetFlip, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sigma1_conjugation_mul (a b : ClPlus14) :
    sigma1 * (a * b) * sigma1 =
      (sigma1 * a * sigma1) * (sigma1 * b * sigma1) := by
  calc
    sigma1 * (a * b) * sigma1 =
        (sigma1 * a) * (b * sigma1) := by
          simp only [mul_assoc]
    _ = (sigma1 * a) * (sigma1 * sigma1) * (b * sigma1) := by
          rw [sigma1_sq]
          simp only [mul_one]
    _ = (sigma1 * a * sigma1) * (sigma1 * b * sigma1) := by
          rw [sigma1_sq]
          simp only [mul_one]
          simp only [mul_assoc]
          rw [← mul_assoc sigma1 sigma1 (b * sigma1), sigma1_sq]
          simp only [one_mul]

theorem hestenesPauliKreinAdjoint_one :
    hestenesPauliKreinAdjoint (1 : ClPlus14) = 1 := by
  simp [hestenesPauliKreinAdjoint, hestenesHermitianAdjoint_one,
    sigma1_sq]

theorem hestenesPauliKreinAdjoint_add (x y : ClPlus14) :
    hestenesPauliKreinAdjoint (x + y) =
      hestenesPauliKreinAdjoint x + hestenesPauliKreinAdjoint y := by
  simp [hestenesPauliKreinAdjoint, hestenesHermitianAdjoint_add,
    add_mul, mul_add]

theorem hestenesPauliKreinAdjoint_smul (r : ℝ) (x : ClPlus14) :
    hestenesPauliKreinAdjoint (r • x) =
      r • hestenesPauliKreinAdjoint x := by
  simp [hestenesPauliKreinAdjoint, hestenesHermitianAdjoint_smul]

theorem hestenesPauliKreinAdjoint_mul (x y : ClPlus14) :
    hestenesPauliKreinAdjoint (x * y) =
      hestenesPauliKreinAdjoint y * hestenesPauliKreinAdjoint x := by
  simp only [hestenesPauliKreinAdjoint, hestenesHermitianAdjoint_mul]
  exact sigma1_conjugation_mul _ _

theorem hestenesPauliKreinAdjoint_involutive (x : ClPlus14) :
    hestenesPauliKreinAdjoint (hestenesPauliKreinAdjoint x) = x := by
  simp only [hestenesPauliKreinAdjoint,
    hestenesHermitianAdjoint_mul, hestenesHermitianAdjoint_involutive,
    hestenesHermitianAdjoint_sigma1]
  calc
    sigma1 * (sigma1 * (x * sigma1)) * sigma1 =
        (sigma1 * sigma1) * (x * sigma1) * sigma1 := by
          rw [← mul_assoc]
    _ = x := by
          rw [sigma1_sq]
          simp only [one_mul]
          rw [mul_assoc, sigma1_sq, mul_one]

theorem hestenesPauliKreinAdjoint_sigma1 :
    hestenesPauliKreinAdjoint sigma1 = sigma1 := by
  simp [hestenesPauliKreinAdjoint, hestenesHermitianAdjoint_sigma1,
    sigma1_sq]

end InfoGeometry.Canonical.HestenesPauliEvenClifford
