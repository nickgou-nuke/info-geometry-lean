import InfoGeometry.Clifford.Cl11WittBasis
import InfoGeometry.Canonical.MatrixExponentialTraceDet
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Hyperbolic Peirce kernel in the split Clifford sheet model

`Gamma_mat` is the existing involutive sheet generator.  This owner records
its complementary idempotents and the exact diagonal exponential kernel.  It
does not assert a group Fourier transform or an analytic integral.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitCliffordHyperbolicPeirceKernel

open InfoGeometry.Clifford
open scoped Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def peircePlus : Mat2 := (1 / 2 : ℝ) • (I_mat + Gamma_mat)

def peirceMinus : Mat2 := (1 / 2 : ℝ) • (I_mat - Gamma_mat)

theorem peircePlus_sq : peircePlus * peircePlus = peircePlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, I_mat, Gamma_mat, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem peirceMinus_sq : peirceMinus * peirceMinus = peirceMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peirceMinus, I_mat, Gamma_mat, Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem peircePlus_mul_peirceMinus : peircePlus * peirceMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus, I_mat, Gamma_mat,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem peirceMinus_mul_peircePlus : peirceMinus * peircePlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus, I_mat, Gamma_mat,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

theorem peircePlus_add_peirceMinus : peircePlus + peirceMinus = I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus, I_mat, Gamma_mat]
    <;> ring

theorem peircePlus_sub_peirceMinus : peircePlus - peirceMinus = Gamma_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus, I_mat, Gamma_mat]
    <;> ring

def hyperbolicKernel (t : ℝ) : Mat2 :=
  NormedSpace.exp (t • Gamma_mat)

theorem hyperbolicKernel_matrix (t : ℝ) :
    hyperbolicKernel t = !![Real.exp t, 0; 0, Real.exp (-t)] := by
  have hdiag : (t • Gamma_mat : Mat2) = Matrix.diagonal ![t, -t] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gamma_mat, Matrix.diagonal, Pi.smul_apply]
  rw [hyperbolicKernel, hdiag, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Pi.coe_exp, Real.exp_neg, Real.exp_eq_exp_ℝ]

theorem hyperbolicKernel_peirce_decomposition (t : ℝ) :
    hyperbolicKernel t =
      (Real.exp t : ℝ) • peircePlus +
        (Real.exp (-t) : ℝ) • peirceMinus := by
  rw [hyperbolicKernel_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [peircePlus, peirceMinus, I_mat, Gamma_mat,
      Matrix.diagonal, Matrix.smul_apply]
    <;> ring

theorem hyperbolicKernel_zero : hyperbolicKernel 0 = I_mat := by
  rw [hyperbolicKernel_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mat]

theorem hyperbolicKernel_add (s t : ℝ) :
    hyperbolicKernel (s + t) = hyperbolicKernel s * hyperbolicKernel t := by
  rw [hyperbolicKernel_matrix, hyperbolicKernel_matrix, hyperbolicKernel_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]
    <;> ring

theorem hyperbolicKernel_neg_mul (t : ℝ) :
    hyperbolicKernel (-t) * hyperbolicKernel t = I_mat := by
  rw [hyperbolicKernel_matrix, hyperbolicKernel_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I_mat, Matrix.mul_apply, Fin.sum_univ_two]
    <;> rw [← Real.exp_add]
    <;> simp

/-! The square-minus-one companion gives the finite elliptic/Fourier kernel. -/

def ellipticKernel (t : ℝ) : Mat2 :=
  (Real.cos t : ℝ) • I_mat + (Real.sin t : ℝ) • K_mat

theorem ellipticKernel_zero : ellipticKernel 0 = I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticKernel, I_mat, K_mat]

theorem ellipticKernel_add (s t : ℝ) :
    ellipticKernel (s + t) = ellipticKernel s * ellipticKernel t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticKernel, I_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add]
    <;> ring

theorem ellipticKernel_neg_mul (t : ℝ) :
    ellipticKernel (-t) * ellipticKernel t = I_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticKernel, I_mat, K_mat, Matrix.mul_apply, Fin.sum_univ_two,
      Real.cos_neg, Real.sin_neg, Real.cos_sq_add_sin_sq]
    <;> try ring
    <;> nlinarith [Real.sin_sq_add_cos_sq t]

end InfoGeometry.Clifford.SplitCliffordHyperbolicPeirceKernel
