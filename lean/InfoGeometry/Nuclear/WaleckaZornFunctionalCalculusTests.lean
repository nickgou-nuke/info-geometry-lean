import InfoGeometry.Nuclear.WaleckaZornFunctionalCalculus
import InfoGeometry.Nuclear.ChiralPolarizedZornBasis

namespace InfoGeometry.Nuclear.WaleckaZornFunctionalCalculusTests

open InfoGeometry.Algebra
open InfoGeometry.Nuclear.NambuGorkov
open InfoGeometry.Nuclear.WaleckaZornBdG
open InfoGeometry.Nuclear.ChiralPolarizedZornBasis

noncomputable section

example (state : NambuGorkovCarrier ℝ) :
    regularHamiltonian state ^ 4 =
      ((bogoliubovEnergy state) ^ 2) ^ 2 •
        (1 : Module.End ℝ (ZornVectorMatrix ℝ)) :=
  regularHamiltonian_pow_even state 2

example (order : ℕ) :
    regularHamiltonian (meanFieldState 1 1 1 ![1, 0, 0]) ^ (2 * order) = 1 := by
  rw [regularHamiltonian_pow_even, bogoliubovEnergy_sq, nambu_gorkov_zornNorm]
  norm_num [meanFieldState, effectiveMass, Vec3.dot]

example : 1 - (1 : ℝ) ^ 2 *
    (bogoliubovEnergy (meanFieldState 1 1 1 ![1, 0, 0])) ^ 2 = 0 := by
  rw [bogoliubovEnergy_sq, nambu_gorkov_zornNorm]
  norm_num [meanFieldState, effectiveMass, Vec3.dot]

example (state : NambuGorkovCarrier ℝ) (parameter : ℝ)
    (nonresonant : 1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2 ≠ 0) :
    (1 - parameter • regularHamiltonian state) *
      ((1 - parameter ^ 2 * (bogoliubovEnergy state) ^ 2)⁻¹ •
        (1 + parameter • regularHamiltonian state)) = 1 :=
  (regularHamiltonianResolventUnit state parameter nonresonant).val_inv

example : ZornVectorMatrix.mul (ZornVectorMatrix.E11 : ZornVectorMatrix ℝ)
    ZornVectorMatrix.E22 = 0 := ZornVectorMatrix.E11_mul_E22

example (coordinate : Fin 3) :
    ZornVectorMatrix.mul (ZornVectorMatrix.U coordinate : ZornVectorMatrix ℝ)
      (ZornVectorMatrix.U coordinate) = 0 := ZornVectorMatrix.U_mul_self_zero coordinate

#print axioms regularHamiltonian_pow_even
#print axioms regularHamiltonian_pow_odd
#print axioms regularHamiltonian_finite_series
#print axioms regularHamiltonian_shift_product
#print axioms regularHamiltonian_shift_product_reverse
#print axioms regularHamiltonianResolventUnit
#print axioms diagonal_offDiagonal_anticommutator
#print axioms mass_gap_cross_terms_zero
#print axioms offDiagonal_square
#print axioms nativeHamiltonian_polarized_decomposition
#print axioms identity_anticommutator_ne_zero

end

end InfoGeometry.Nuclear.WaleckaZornFunctionalCalculusTests
