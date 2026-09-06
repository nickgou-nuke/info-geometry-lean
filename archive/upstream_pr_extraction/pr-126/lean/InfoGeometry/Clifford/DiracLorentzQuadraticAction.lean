import InfoGeometry.Clifford.Cl55QuadraticSpinAction
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# Quadratic Lorentz action in the explicit Dirac representation

The concrete Pauli--Dirac gamma matrices are fed into the generic
noncommutative Dirac-system theorem.  The resulting identity is an operator
statement in `M₄(ℂ)`, not a scalar or diagonal reduction.
-/

namespace InfoGeometry.Clifford.DiracPauliGamma

open InfoGeometry.Clifford

theorem gamma_isDiracMatrixSystem :
    IsDiracMatrixSystem eta gamma := by
  intro μ ν
  simpa [operatorAnticommutator, Algebra.smul_def] using gamma_anticomm μ ν

theorem diracBivector_action (μ ν κ : Fin 4) :
    InfoGeometry.Clifford.diracBivector gamma μ ν * gamma κ -
        gamma κ * InfoGeometry.Clifford.diracBivector gamma μ ν =
      (2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta ν κ) * gamma μ -
        (2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta μ κ) * gamma ν := by
  exact InfoGeometry.Clifford.diracBivector_action
    gamma_isDiracMatrixSystem μ ν κ

theorem lorentzGenerator_action (μ ν κ : Fin 4) :
    lorentzGenerator μ ν * gamma κ - gamma κ * lorentzGenerator μ ν =
      (Complex.I / 4) •
        ((2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta ν κ) * gamma μ -
          (2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta μ κ) * gamma ν) := by
  unfold lorentzGenerator
  calc
    (Complex.I / 4) • (gamma μ * gamma ν - gamma ν * gamma μ) * gamma κ -
        gamma κ * ((Complex.I / 4) • (gamma μ * gamma ν - gamma ν * gamma μ)) =
      (Complex.I / 4) •
        (InfoGeometry.Clifford.diracBivector gamma μ ν * gamma κ -
          gamma κ * InfoGeometry.Clifford.diracBivector gamma μ ν) := by
            simp only [smul_mul_assoc, mul_smul_comm]
            unfold InfoGeometry.Clifford.diracBivector
            module
    _ = (Complex.I / 4) •
        ((2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta ν κ) * gamma μ -
          (2 : DiracMatrix) * algebraMap ℂ DiracMatrix (2 * eta μ κ) * gamma ν) := by
            rw [InfoGeometry.Clifford.DiracPauliGamma.diracBivector_action]

end InfoGeometry.Clifford.DiracPauliGamma
