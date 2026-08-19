import Mathlib.Tactic

/-!
# Published thesis architecture seal

A final publication-level capstone.  Concrete algebraic kernels are proved;
large physical/geometric readings are outside the finite theorem owners.

Slogan:
`Spacetime is the invariant determinant geometry of spin.  The Squash projects;
the Sign quantizes; the CPT atom seals.`
-/

noncomputable section

namespace PublishedThesisArchitecture

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ## Spin determinant geometry -/

def σ1 : M2C := !![0, 1; 1, 0]
def σ2 : M2C := !![0, -Complex.I; Complex.I, 0]
def σ3 : M2C := !![1, 0; 0, -1]

def Xspin (t x y z : ℂ) : M2C := t • (1 : M2C) + x • σ1 + y • σ2 + z • σ3

theorem spin_det_minkowski (t x y z : ℂ) :
    (Xspin t x y z).det = t^2 - x^2 - y^2 - z^2 := by
  simp [Xspin, σ1, σ2, σ3, Matrix.det_fin_two, Matrix.smul_apply, Matrix.add_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Squash/sign/CPT atom -/

def scalarSquash (δ : ℂ) : ℂ := (δ - 1) / (δ + 1)

theorem scalarSquash_defect : scalarSquash 1 = 0 := by
  norm_num [scalarSquash]

def eps : M2R := !![0, 1; 1, 0]
def J : M2R := !![0, -1; 1, 0]
def CPT : M2R := eps * J

theorem eps_sq : eps * eps = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eps, Matrix.mul_apply, Fin.sum_univ_two]

theorem J_sq : J * J = (-1 : ℝ) • (1 : M2R) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two]

theorem eps_J_anticomm : eps * J = - (J * eps) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eps, J, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

theorem CPT_sq : CPT * CPT = 1 := by
  unfold CPT
  calc
    (eps * J) * (eps * J) = eps * (J * eps) * J := by simp [mul_assoc]
    _ = eps * (-(eps * J)) * J := by
      have h := congrArg Neg.neg eps_J_anticomm
      simp at h
      rw [h]
    _ = -((eps * eps) * (J * J)) := by simp [mul_assoc]
    _ = 1 := by rw [eps_sq, J_sq]; ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-! ## Bogoliubov frame preservation -/

def bogoliubov (c s : ℝ) : M2R := !![c, s; s, c]
def krein : M2R := !![1, 0; 0, -1]

theorem bogoliubov_krein (c s : ℝ) (h : c^2 - s^2 = 1) :
    (bogoliubov c s)ᵀ * krein * (bogoliubov c s) = krein := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [bogoliubov, krein, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith

/-- Final publication seal theorem. -/
theorem published_thesis_architecture_seal :
    (∀ t x y z : ℂ, (Xspin t x y z).det = t^2 - x^2 - y^2 - z^2) ∧
    scalarSquash 1 = 0 ∧
    eps * eps = 1 ∧ J * J = (-1 : ℝ) • (1 : M2R) ∧ eps * J = - (J * eps) ∧ CPT * CPT = 1 ∧
    (∀ c s : ℝ, c^2 - s^2 = 1 → (bogoliubov c s)ᵀ * krein * (bogoliubov c s) = krein) := by
  exact ⟨spin_det_minkowski, scalarSquash_defect, eps_sq, J_sq, eps_J_anticomm, CPT_sq,
    bogoliubov_krein⟩

#check published_thesis_architecture_seal

end PublishedThesisArchitecture
