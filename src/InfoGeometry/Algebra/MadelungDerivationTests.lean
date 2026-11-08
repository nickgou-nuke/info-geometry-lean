import InfoGeometry.Algebra.MadelungDerivation
import InfoGeometry.Algebra.MadelungLogDensityCalculus
import InfoGeometry.Algebra.MadelungProofDependency

namespace InfoGeometry.Algebra.MadelungDerivationTests

open MadelungLogDensityCalculus

noncomputable section

theorem exponential_log_derivative (rate : ℝ) :
    deriv (fun point : ℝ => 2 * rate * point) = fun _ => 2 * rate := by
  funext point
  simpa only [id_eq, mul_one] using ((hasDerivAt_id point).const_mul (2 * rate)).deriv

example (rate point : ℝ) :
    deriv (deriv (positiveAmplitude (fun location => 2 * rate * location))) point /
      positiveAmplitude (fun location => 2 * rate * location) point = rate ^ 2 := by
  have twice : DifferentiableAt ℝ (deriv (fun location => 2 * rate * location)) point := by
    rw [exponential_log_derivative]
    fun_prop
  rw [curvature_eq_log_density _ point (by fun_prop) twice, exponential_log_derivative]
  simp only [deriv_const]
  ring

theorem gaussian_log_derivative :
    deriv (fun point : ℝ => -(point ^ 2)) = fun point => -2 * point := by
  funext point
  simp [mul_comm]

example :
    deriv (deriv (positiveAmplitude (fun location => -(location ^ 2)))) 0 /
      positiveAmplitude (fun location => -(location ^ 2)) 0 = -1 := by
  have twice : DifferentiableAt ℝ (deriv (fun location : ℝ => -(location ^ 2))) 0 := by
    rw [gaussian_log_derivative]
    fun_prop
  have linear_derivative : deriv (fun location : ℝ => -2 * location) 0 = -2 := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (0 : ℝ)).const_mul (-2)).deriv
  rw [curvature_eq_log_density _ 0 (by fun_prop) twice, gaussian_log_derivative,
    linear_derivative]
  norm_num

example : positiveAmplitude (fun location => -(location ^ 2)) 0 = 1 := by
  norm_num [positiveAmplitude]

example {Base Carrier : Type*} [CommRing Base] [Field Carrier]
    [Algebra Base Carrier] [CharZero Carrier]
    (spatial temporal : Derivation Base Carrier Carrier)
    (commute : Function.Commute spatial temporal) (phase potential : Carrier)
    (equation : MadelungDerivation.hamiltonJacobiResidual spatial temporal phase potential = 0) :
    MadelungDerivation.eulerResidual spatial temporal (spatial phase) potential = 0 :=
  MadelungDerivation.hamiltonJacobi_implies_euler spatial temporal commute phase potential equation

#print axioms MadelungDerivation.curvature_eq_riccati
#print axioms MadelungDerivation.curvature_eq_density_score
#print axioms MadelungDerivation.derivative_kineticEnergy
#print axioms MadelungDerivation.differentiate_hamiltonJacobi
#print axioms MadelungDerivation.hamiltonJacobi_implies_euler
#print axioms MadelungDerivation.quantum_euler
#print axioms MadelungDerivation.amplitude_transport_implies_continuity
#print axioms MadelungLogDensityCalculus.sqrt_density_curvature
#print axioms MadelungProofDependency.commutation_not_implied_by_curvature

end

end InfoGeometry.Algebra.MadelungDerivationTests
