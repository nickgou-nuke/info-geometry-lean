import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CPTAtom

/-!
# Published thesis architecture seal

A final publication-level capstone.  Concrete algebraic kernels are proved;
large physical/geometric readings are represented as theorem-honest sockets.

Slogan:
`Spacetime is the invariant determinant geometry of spin.  The Squash projects;
the Sign quantizes; the CPT atom seals.`
-/

noncomputable section

namespace PublishedThesisArchitecture

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev M2R := InfoGeometry.Algebra.FiniteSpin.Mat2R

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

abbrev eps : M2R := InfoGeometry.Physics.CPTAtom.eps
abbrev J : M2R := InfoGeometry.Physics.CPTAtom.J
abbrev CPT : M2R := InfoGeometry.Physics.CPTAtom.CPT

theorem eps_sq : eps * eps = 1 := by
  simpa [eps] using InfoGeometry.Physics.CPTAtom.eps_sq

theorem J_sq : J * J = (-1 : ℝ) • (1 : M2R) := by
  simpa [J] using InfoGeometry.Physics.CPTAtom.J_sq

theorem eps_J_anticomm : eps * J = - (J * eps) := by
  simpa [eps, J] using InfoGeometry.Physics.CPTAtom.eps_J_anticomm

theorem CPT_sq : CPT * CPT = 1 := by
  simpa [CPT] using InfoGeometry.Physics.CPTAtom.CPT_sq

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
