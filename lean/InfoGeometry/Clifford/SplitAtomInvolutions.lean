import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.HypercomplexTriad
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# The split atom: signs, Peirce blocks, and Clifford involutions

The carrier and Clifford equivalence belong to `Cl11Matrix`.  These aliases
use the convention I = epsilon, J = sigma_z, K = I J = -sigma_x.  In particular
`HypercomplexTriad.I` has the opposite sign.  No operation below is identified
with physical charge conjugation, parity, or antiunitary time reversal.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitAtom

abbrev Mat2 := Cl11Matrix.Mat2
abbrev I : Mat2 := Cl11Matrix.Eminus
abbrev J : Mat2 := Cl11Matrix.Eplus
abbrev K : Mat2 := -Cl11Matrix.J1
abbrev Pplus : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.Pplus
abbrev Pminus : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.Pminus
abbrev raising : Mat2 := InfoGeometry.Algebra.HypercomplexTriad.N

@[simp] theorem I_sq : I * I = -(1 : Mat2) := by
  simpa using Cl11Matrix.Eminus_sq

@[simp] theorem J_sq : J * J = (1 : Mat2) := Cl11Matrix.Eplus_sq

@[simp] theorem K_sq : K * K = (1 : Mat2) := by
  simpa only [K, neg_mul_neg] using Cl11Matrix.J1_sq

@[simp] theorem I_mul_J : I * J = K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem J_mul_I : J * I = -K := by
  simpa only [J, I, K, neg_neg] using Cl11Matrix.Eplus_mul_Eminus

@[simp] theorem J_mul_K : J * K = -I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem K_mul_J : K * J = I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem K_mul_I : K * I = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem I_mul_K : I * K = -J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]

theorem elliptic_owner_sign : I = -InfoGeometry.Algebra.HypercomplexTriad.I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [I, Cl11Matrix.Eminus, InfoGeometry.Algebra.HypercomplexTriad.I]

theorem raising_eq_half_I_sub_K : raising = (1 / 2 : ℝ) • (I - K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [raising, InfoGeometry.Algebra.HypercomplexTriad.N, I, K,
      Cl11Matrix.Eminus, Cl11Matrix.J1]

theorem Pplus_formula : Pplus = (1 / 2 : ℝ) • ((1 : Mat2) + J) := rfl

theorem Pminus_formula : Pminus = (1 / 2 : ℝ) • ((1 : Mat2) - J) := rfl

/-- Full operator Peirce decomposition, including both off-diagonal blocks. -/
theorem peirce_four_blocks (A : Mat2) :
    A = Pplus * A * Pplus + Pplus * A * Pminus +
      Pminus * A * Pplus + Pminus * A * Pminus := by
  have hp : Pplus + Pminus = (1 : Mat2) :=
    InfoGeometry.Algebra.HypercomplexTriad.Pplus_add_Pminus
  calc
    A = (Pplus + Pminus) * A * (Pplus + Pminus) := by rw [hp]; simp
    _ = _ := by noncomm_ring

