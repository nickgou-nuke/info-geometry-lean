import InfoGeometry.Clifford.SplitQuaternionMatrixModel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Chiral/Witt coordinates for the split-quaternion matrix model

The orthogonal basis `(ι, ℓ, ℓι)` is replaced by the null arrows `s₊, s₋`
and the diagonal Cartan element `s₃`.  This is the Peirce decomposition of
`M₂(ℝ)`, not a new non-associative product.
-/

namespace InfoGeometry.Clifford.SplitQuaternionChiralCone

open InfoGeometry.Clifford.SplitQuaternionMatrixModel
open scoped Matrix

abbrev Mat2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

noncomputable def sPlus : Mat2R := (1 / 2 : ℝ) • (hyperbolic - elliptic)

noncomputable def sMinus : Mat2R := (1 / 2 : ℝ) • (hyperbolic + elliptic)

def sThree : Mat2R := bivector

def rhoPlus : Mat2R := !![(1 : ℝ), 0; 0, 0]

def rhoMinus : Mat2R := !![(0 : ℝ), 0; 0, 1]

@[simp] theorem sPlus_sq : sPlus * sPlus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sPlus, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

@[simp] theorem sMinus_sq : sMinus * sMinus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sMinus, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem sPlus_mul_sMinus : sPlus * sMinus = rhoPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sPlus, sMinus, rhoPlus, sThree, elliptic, hyperbolic, bivector,
      one, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sMinus_mul_sPlus : sMinus * sPlus = rhoMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sPlus, sMinus, rhoMinus, sThree, elliptic, hyperbolic, bivector,
      one, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem rhoPlus_sq : rhoPlus * rhoPlus = rhoPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rhoPlus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem rhoMinus_sq : rhoMinus * rhoMinus = rhoMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rhoMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rhoPlus_mul_rhoMinus : rhoPlus * rhoMinus = 0 := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rhoPlus, rhoMinus, Matrix.mul_apply, Fin.sum_univ_two]

theorem rhoPlus_add_rhoMinus : rhoPlus + rhoMinus = one := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rhoPlus, rhoMinus, one]

theorem sThree_mul_sPlus : sThree * sPlus = sPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sThree, sPlus, bivector, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem sPlus_mul_sThree : sPlus * sThree = -sPlus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sThree, sPlus, bivector, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem sThree_mul_sMinus : sThree * sMinus = -sMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sThree, sMinus, bivector, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem sMinus_mul_sThree : sMinus * sThree = sMinus := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [sThree, sMinus, bivector, elliptic, hyperbolic, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem sThree_comm_sPlus : sThree * sPlus - sPlus * sThree = 2 • sPlus := by
  rw [sThree_mul_sPlus, sPlus_mul_sThree]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [sPlus] <;> ring

theorem sThree_comm_sMinus : sThree * sMinus - sMinus * sThree = -2 • sMinus := by
  rw [sThree_mul_sMinus, sMinus_mul_sThree]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [sMinus] <;> ring

theorem sPlus_comm_sMinus : sPlus * sMinus - sMinus * sPlus = sThree := by
  rw [sPlus_mul_sMinus, sMinus_mul_sPlus]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rhoPlus, rhoMinus, sThree, bivector] <;> ring

theorem chiral_det (α xPlus xMinus β : ℝ) :
    (α • rhoPlus + xPlus • sPlus + xMinus • sMinus + β • rhoMinus).det
      = α * β - xPlus * xMinus := by
  simp [rhoPlus, rhoMinus, sPlus, sMinus, sThree, one, elliptic,
    hyperbolic, bivector, Matrix.det_fin_two, Matrix.add_apply,
    Matrix.smul_apply, pow_two]
  ring

end InfoGeometry.Clifford.SplitQuaternionChiralCone
