import Mathlib.Tactic

/-!
# Polynomial symmetry operators

Finite matrix anchors for tripotent, nilpotent, and crystallographic rotation
polynomial identities.
-/

namespace PolynomialSymmetry

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Traceless Pauli-vector matrix `x σ₁ + y σ₂ + z σ₃`. -/
def pauliVec (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, x - I * y; x + I * y, -z]

/-- Pauli quadratic closure: `(x σ₁ + y σ₂ + z σ₃)² = (x²+y²+z²)I`. -/
theorem pauliVec_sq (x y z : ℂ) :
    pauliVec x y z * pauliVec x y z =
      (x ^ 2 + y ^ 2 + z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVec, Matrix.mul_apply, Matrix.smul_apply] <;>
    ring_nf <;>
    try rw [Complex.I_sq] <;>
    ring_nf

/-- Tripotent/trifactor defect operator: `T^3 - T = 0`. -/
def is_tripotent_defect (A : Matrix n n ℂ) : Prop :=
  A ^ 3 - A = 0

/-- Nilpotent/zero-mode defect operator: `Z^k = 0`. -/
def is_nilpotent_defect (A : Matrix n n ℂ) (k : ℕ) : Prop :=
  A ^ k = 0

/-- Wallpaper rotation polynomial: `C^k - I = 0`. -/
def is_wallpaper_rotation (A : Matrix n n ℂ) (k : ℕ) : Prop :=
  A ^ k - 1 = 0

/-- Tripotent defect matrix `diag(1,-1,0)`. -/
def T_mat : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, -1, 0; 0, 0, 0]

/-- `T_mat` strictly satisfies `T^3-T=0`. -/
theorem T_mat_is_tripotent : is_tripotent_defect T_mat := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [is_tripotent_defect, T_mat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

/-- Nilpotent light-cone matrix. -/
def Z_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- `Z_mat^2=0`. -/
theorem Z_mat_is_nilpotent : is_nilpotent_defect Z_mat 2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [is_nilpotent_defect, Z_mat, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete `C4` wallpaper rotation. -/
def C4_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

/-- `C4_mat^4=I`. -/
theorem C4_mat_is_rotation : is_wallpaper_rotation C4_mat 4 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [is_wallpaper_rotation, C4_mat, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

end PolynomialSymmetry
