import InfoGeometry.Nuclear.SpinorMultipoles

namespace InfoGeometry.Nuclear.SpinorMultipoles.Tests

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

example : wittCreationBase ^ 3 = 0 := pauli_raising_cube_zero

example : raisingTensor 3 ≠ 0 := raisingTensor_ne_zero 3

example : Fintype.card (Idx 3) = 8 := by
  rw [idx_card_pow_two]

example : raisingTensor 3 * raisingTensor 3 = 0 :=
  raisingTensor_succ_square_zero 2

example : raisingTensor 3 ^ 3 ≠ 1 :=
  raisingTensor_succ_not_periodic 2 3 (by decide)

example : raisingTensor 0 = 1 := rfl

example : ¬ ∃ root : ℝ, root ^ 2 + root + 1 = 0 := by
  rintro ⟨root, vanishes⟩
  exact real_triangular_root_impossible root vanishes

#print axioms ordinary_cube_vs_tensor_cube
#print axioms raisingTensor_succ_not_periodic
#print axioms triangular_root_sum

end InfoGeometry.Nuclear.SpinorMultipoles.Tests
