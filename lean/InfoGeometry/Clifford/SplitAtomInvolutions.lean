import InfoGeometry.Clifford.Cl11Matrix
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

/-- Grade involution in the matrix representation. -/
def grade (A : Mat2) : Mat2 := K * A * K

/-- Reflection of the negative Clifford generator, not a CPT identification. -/
def spatialReflection (A : Mat2) : Mat2 := J * A * J

@[simp] theorem grade_grade (A : Mat2) : grade (grade A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grade, K, Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem grade_one : grade (1 : Mat2) = 1 := by simp [grade]

theorem grade_mul (A B : Mat2) : grade (A * B) = grade A * grade B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grade, K, Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def gradeEquiv : Mat2 ≃ₐ[ℝ] Mat2 where
  toFun := grade
  invFun := grade
  left_inv := grade_grade
  right_inv := grade_grade
  map_mul' := grade_mul
  map_add' A B := by simp [grade, mul_add, add_mul]
  commutes' r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [grade, K, Cl11Matrix.J1, Algebra.algebraMap_eq_smul_one,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Reversion fixes vectors and reverses multiplication. -/
def reversion : Mat2 →ₗ[ℝ] Mat2 where
  toFun A := J * Aᵀ * J
  map_add' A B := by simp [Matrix.transpose_add, mul_add, add_mul]
  map_smul' r A := by simp [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc]

@[simp] theorem reversion_apply (A : Mat2) : reversion A = J * Aᵀ * J := rfl

theorem reversion_mul (A B : Mat2) : reversion (A * B) = reversion B * reversion A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reversion, J, Cl11Matrix.Eplus, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem reversion_reversion (A : Mat2) : reversion (reversion A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reversion, J, Cl11Matrix.Eplus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem reversion_one : reversion (1 : Mat2) = 1 := by simp [reversion]

@[simp] theorem reversion_I : reversion I = I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reversion, I, J, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem reversion_J : reversion J = J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reversion, J, Cl11Matrix.Eplus, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem reversion_K : reversion K = -K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reversion, J, K, Cl11Matrix.Eplus, Cl11Matrix.J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Clifford conjugation, which the source incorrectly calls reversion. -/
def cliffordConjugation (A : Mat2) : Mat2 := -I * Aᵀ * I

theorem cliffordConjugation_eq_grade_reversion (A : Mat2) :
    cliffordConjugation A = grade (reversion A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordConjugation, grade, reversion, I, J, K,
      Cl11Matrix.Eminus, Cl11Matrix.Eplus, Cl11Matrix.J1,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_cliffordConjugation (A : Mat2) :
    A * cliffordConjugation A = A.det • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cliffordConjugation, I, Cl11Matrix.Eminus,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

/-- Negating an inner automorphism is not a unital algebra automorphism. -/
theorem negative_grade_not_unital : -grade (1 : Mat2) ≠ (1 : Mat2) := by
  intro h
  have h00 := congrArg (fun A : Mat2 => A 0 0) h
  norm_num at h00

theorem representation_iota (v : Cl11Matrix.Vec11) :
    Cl11Matrix.cl11EquivMat (CliffordAlgebra.ι Cl11Matrix.q11 v) =
      v.1 • J + v.2 • I := by
  change Cl11Matrix.cl11ToMat (CliffordAlgebra.ι Cl11Matrix.q11 v) = _
  simp [Cl11Matrix.cl11ToMat, Cl11Matrix.gen, J, I]

/-- The concrete anti-automorphism is Mathlib's actual Clifford reversion. -/
theorem representation_reverse (a : CliffordAlgebra Cl11Matrix.q11) :
    Cl11Matrix.cl11EquivMat (CliffordAlgebra.reverse a) =
      reversion (Cl11Matrix.cl11EquivMat a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
      simp only [CliffordAlgebra.reverse.commutes, AlgEquiv.commutes,
        Algebra.algebraMap_eq_smul_one, map_smul, reversion_one]
  | ι v =>
      rw [CliffordAlgebra.reverse_ι, representation_iota]
      simp only [map_add, map_smul, reversion_J, reversion_I]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb =>
      simp only [CliffordAlgebra.reverse.map_mul, map_mul, ha, hb, reversion_mul]

/-- The concrete automorphism is Mathlib's actual grade involution. -/
theorem representation_involute (a : CliffordAlgebra Cl11Matrix.q11) :
    Cl11Matrix.cl11EquivMat (CliffordAlgebra.involute a) =
      gradeEquiv (Cl11Matrix.cl11EquivMat a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp
  | ι v =>
      rw [CliffordAlgebra.involute_ι, map_neg, representation_iota]
      change -(v.1 • J + v.2 • I) = grade (v.1 • J + v.2 • I)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [grade, I, J, K, Cl11Matrix.Eminus, Cl11Matrix.Eplus,
          Cl11Matrix.J1, Matrix.mul_apply, Fin.sum_univ_two]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

end InfoGeometry.Clifford.SplitAtom
