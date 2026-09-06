import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55

abbrev AlgMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

structure SplitCartanSector (n r : ℕ) where
  H : Fin r → AlgMat n
  sq_pos_one : ∀ i, H i * H i = 1
  commutes : ∀ i j, H i * H j = H j * H i

def cartanFlow {n r : ℕ} (sector : SplitCartanSector n r) (i : Fin r) (t : ℝ) : AlgMat n :=
  Real.cosh t • (1 : AlgMat n) + Real.sinh t • sector.H i

theorem cartanFlow_add {n r : ℕ} (sector : SplitCartanSector n r) (i : Fin r) (s t : ℝ) :
    cartanFlow sector i (s + t) = cartanFlow sector i s * cartanFlow sector i t := by
  dsimp [cartanFlow]
  rw [Real.cosh_add, Real.sinh_add]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Matrix.one_mul,
    Matrix.mul_one, smul_smul, sector.sq_pos_one i]
  module

theorem cartanFlow_commutes {n r : ℕ} (sector : SplitCartanSector n r)
    (i j : Fin r) (ti tj : ℝ) :
    cartanFlow sector i ti * cartanFlow sector j tj =
      cartanFlow sector j tj * cartanFlow sector i ti := by
  dsimp [cartanFlow]
  simp only [add_mul, mul_add, Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
    Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [sector.commutes i j]
  module

end InfoGeometry.OperatorAlgebra.Cl55
