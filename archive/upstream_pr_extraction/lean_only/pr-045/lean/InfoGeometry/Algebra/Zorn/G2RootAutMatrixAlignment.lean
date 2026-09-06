import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup

namespace InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2Unipotent

theorem autMatrix_rootAut (r : G2Root) :
    autMatrix (rootAut r) =
      autMatrix ((c ^ r.2.val)⁻¹) *
        autMatrix (match r.1 with
          | RootLength.Short => S0
          | RootLength.Long => L0) *
        autMatrix (c ^ r.2.val) := by
  dsimp [rootAut]
  rw [autMatrix_mul, autMatrix_mul]
  simp only [mul_assoc]
  rfl

theorem autMatrix_c :
    autMatrix c = cycle012Matrix * swapCartanMatrix := by
  rw [c, autMatrix_mul, autMatrix_swapCartanMatrix, autMatrix_cycle012Matrix]

theorem autMatrix_c_pow (n : ℕ) :
    autMatrix (c ^ n) = (cycle012Matrix * swapCartanMatrix) ^ n := by
  induction n with
  | zero => simp [autMatrix_one]
  | succ n ih =>
      rw [pow_succ, autMatrix_mul, autMatrix_c, ih, pow_succ']

theorem autMatrix_c_pow_six : autMatrix (c ^ 6) = 1 := by
  rw [c_pow_six, autMatrix_one]

theorem c_inv_eq_c_pow_five : c⁻¹ = c ^ 5 := by
  calc
    c⁻¹ = c⁻¹ * 1 := by rw [_root_.mul_one]
    _ = c⁻¹ * c ^ 6 := by rw [c_pow_six]
    _ = c ^ 5 := by group

theorem autMatrix_c_inv :
    autMatrix c⁻¹ = (cycle012Matrix * swapCartanMatrix) ^ 5 := by
  rw [c_inv_eq_c_pow_five, autMatrix_c_pow]

theorem autMatrix_c_pow_five_normal_form :
    autMatrix (c ^ 5) =
      swapCartanMatrix * (cycle012Matrix * cycle012Matrix) := by
  rw [c_pow_five_eq_swapCartan_mul_cycle_sq, autMatrix_mul,
    autMatrix_mul, autMatrix_swapCartanMatrix, autMatrix_cycle012Matrix]
  have hcomm : swapCartanMatrix * cycle012Matrix =
      cycle012Matrix * swapCartanMatrix := by
    have h := congrArg autMatrix swapCartanAut_comm_cycle012
    simpa [autMatrix_mul, autMatrix_swapCartanMatrix,
      autMatrix_cycle012Matrix] using h.symm
  calc
    cycle012Matrix * cycle012Matrix * swapCartanMatrix =
        cycle012Matrix * (cycle012Matrix * swapCartanMatrix) :=
      mul_assoc _ _ _
    _ = cycle012Matrix * (swapCartanMatrix * cycle012Matrix) := by
      rw [hcomm]
    _ = (cycle012Matrix * swapCartanMatrix) * cycle012Matrix :=
      (mul_assoc _ _ _).symm
    _ = (swapCartanMatrix * cycle012Matrix) * cycle012Matrix := by
      rw [hcomm]
    _ = swapCartanMatrix * (cycle012Matrix * cycle012Matrix) :=
      mul_assoc _ _ _

theorem autMatrix_rootAut_short_one_normal_form :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      (cycle012Matrix * swapCartanMatrix) ^ 5 *
        shortRootMatrix * (cycle012Matrix * swapCartanMatrix) := by
  rw [autMatrix_rootAut]
  change autMatrix c⁻¹ * autMatrix (unipotentShortAut true) * autMatrix c = _
  rw [autMatrix_c_inv, autMatrix_shortRootMatrix,
    autMatrix_c]

theorem autMatrix_rootAut_short_one_reduced :
    autMatrix (rootAut (RootLength.Short, (1 : ZMod 6))) =
      swapCartanMatrix * (cycle012Matrix * cycle012Matrix) *
        shortRootMatrix * (cycle012Matrix * swapCartanMatrix) := by
  rw [autMatrix_rootAut_short_one_normal_form]
  rw [← autMatrix_c_pow_five_normal_form, ← autMatrix_c_pow 5]

theorem c_sq_inv_eq_c_pow_four : (c ^ 2)⁻¹ = c ^ 4 := by
  calc
    (c ^ 2)⁻¹ = (c⁻¹) ^ 2 := by rw [inv_pow]
    _ = (c ^ 5) ^ 2 := by rw [c_inv_eq_c_pow_five]
    _ = c ^ 4 * c ^ 6 := by group
    _ = c ^ 4 := by rw [c_pow_six, _root_.mul_one]

end InfoGeometry.Algebra.Zorn.G2RootAutMatrixAlignment
