import InfoGeometry.Canonical.HestenesEvenPauliEquiv

noncomputable section
namespace HestenesOmegaHyperbolic

open HestenesCl14
open HestenesEvenPauliEquiv
open HestenesPauliSheetBridge

abbrev EvenAlgebra := ClPlus14

def omega : EvenAlgebra := volumeEven
def beta : EvenAlgebra := sigmaEven 0

def omegaBetaPlane (a b c d : ℝ) : EvenAlgebra :=
  a • (1 : EvenAlgebra) + b • omega + c • beta + d • (omega * beta)

def nativeBoostRotor (η : ℝ) : EvenAlgebra :=
  Real.cosh (η / 2) • (1 : EvenAlgebra) + Real.sinh (η / 2) • beta

@[simp] theorem omega_sq : omega * omega = -(1 : EvenAlgebra) := by
  apply clPlusToPauli_injective
  rw [omega, map_mul, clPlusToPauli_volumeEven]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem beta_sq : beta * beta = (1 : EvenAlgebra) := by
  exact sigmaEven_zero_sq

@[simp] theorem omega_beta_comm : omega * beta = beta * omega := by
  apply clPlusToPauli_injective
  rw [omega, beta, map_mul, clPlusToPauli_volumeEven,
    clPlusToPauli_sigma0]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

@[simp] theorem omega_beta_sq :
    (omega * beta) * (omega * beta) = -(1 : EvenAlgebra) := by
  calc
    (omega * beta) * (omega * beta) =
        omega * (beta * omega) * beta := by simp only [mul_assoc]
    _ = omega * (omega * beta) * beta := by rw [omega_beta_comm]
    _ = (omega * omega) * (beta * beta) := by simp only [mul_assoc]
    _ = -(1 : EvenAlgebra) := by simp [omega_sq, beta_sq]

@[simp] theorem omega_beta_plane_zero :
    omegaBetaPlane 0 0 0 0 = 0 := by
  simp [omegaBetaPlane]

theorem omega_beta_plane_add (a b c d a' b' c' d' : ℝ) :
    omegaBetaPlane a b c d + omegaBetaPlane a' b' c' d' =
      omegaBetaPlane (a + a') (b + b') (c + c') (d + d') := by
  simp only [omegaBetaPlane, add_smul]
  module

@[simp] theorem nativeBoostRotor_zero :
    nativeBoostRotor 0 = (1 : EvenAlgebra) := by
  simp [nativeBoostRotor]

theorem omega_nativeBoostRotor_comm (η : ℝ) :
    omega * nativeBoostRotor η = nativeBoostRotor η * omega := by
  calc
    omega * nativeBoostRotor η =
        omega * (Real.cosh (η / 2) • (1 : EvenAlgebra)) +
          omega * (Real.sinh (η / 2) • beta) := by
            rw [nativeBoostRotor, mul_add]
    _ = Real.cosh (η / 2) • omega +
          Real.sinh (η / 2) • (omega * beta) := by
            rw [mul_smul_comm, mul_smul_comm]
            simp
    _ = Real.cosh (η / 2) • omega +
          Real.sinh (η / 2) • (beta * omega) := by
            rw [omega_beta_comm]
    _ = nativeBoostRotor η * omega := by
            rw [nativeBoostRotor, add_mul, smul_mul_assoc, smul_mul_assoc]
            simp

end HestenesOmegaHyperbolic
end noncomputable section
