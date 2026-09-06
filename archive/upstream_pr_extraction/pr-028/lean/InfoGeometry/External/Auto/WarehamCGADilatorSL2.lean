import Mathlib.Tactic

noncomputable section

namespace WarehamCGADilatorSL2

abbrev M2Q := Matrix (Fin 2) (Fin 2) ℚ

open scoped Matrix

def I2 : M2Q := !![1, 0; 0, 1]
def e : M2Q := !![1, 0; 0, -1]
def ebar : M2Q := !![0, 1; -1, 0]
def S : M2Q := e * ebar
def nvec : M2Q := e + ebar
def nbar : M2Q := e - ebar

def comm (A B : M2Q) : M2Q := A * B - B * A
def anticomm (A B : M2Q) : M2Q := A * B + B * A

def H : M2Q := -S
def E : M2Q := (1/2 : ℚ) • nvec
def F : M2Q := (1/2 : ℚ) • nbar

def Casimir : M2Q := H * H + (2 : ℚ) • (E * F + F * E)

theorem e_square : e * e = I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [e, I2, Matrix.mul_apply]

theorem ebar_square : ebar * ebar = -I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [ebar, I2, Matrix.mul_apply]

theorem e_ebar_anticomm : anticomm e ebar = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [anticomm, e, ebar, Matrix.mul_apply]

theorem S_square : S * S = I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [S, e, ebar, I2, Matrix.mul_apply]

theorem S_n_left : S * nvec = -nvec := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [S, nvec, e, ebar, Matrix.mul_apply]

theorem n_S_right : nvec * S = nvec := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [S, nvec, e, ebar, Matrix.mul_apply]

theorem S_nbar_left : S * nbar = nbar := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [S, nbar, e, ebar, Matrix.mul_apply]

theorem nbar_S_right : nbar * S = -nbar := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [S, nbar, e, ebar, Matrix.mul_apply]

theorem anticomm_S_n : anticomm S nvec = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [anticomm, S, nvec, e, ebar, Matrix.mul_apply]

theorem anticomm_S_nbar : anticomm S nbar = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [anticomm, S, nbar, e, ebar, Matrix.mul_apply]

theorem anticomm_n_nbar : anticomm nvec nbar = (4 : ℚ) • I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [anticomm, nvec, nbar, e, ebar, I2, Matrix.mul_apply]

theorem comm_S_n : comm S nvec = (-2 : ℚ) • nvec := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, S, nvec, e, ebar, Matrix.mul_apply]

theorem comm_S_nbar : comm S nbar = (2 : ℚ) • nbar := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, S, nbar, e, ebar, Matrix.mul_apply]

theorem comm_n_nbar : comm nvec nbar = (-4 : ℚ) • S := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, S, nvec, nbar, e, ebar, Matrix.mul_apply]

theorem sl2_HE : comm H E = (2 : ℚ) • E := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, H, E, S, nvec, e, ebar, Matrix.mul_apply]

theorem sl2_HF : comm H F = (-2 : ℚ) • F := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, H, F, S, nbar, e, ebar, Matrix.mul_apply]

theorem sl2_EF : comm E F = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, H, E, F, S, nvec, nbar, e, ebar, Matrix.mul_apply]

theorem casimir_eq_three : Casimir = (3 : ℚ) • I2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [Casimir, H, E, F, S, nvec, nbar, e, ebar, I2, Matrix.mul_apply]

theorem casimir_central_H : comm Casimir H = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, Casimir, H, E, F, S, nvec, nbar, e, ebar, Matrix.mul_apply]

theorem casimir_central_E : comm Casimir E = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, Casimir, H, E, F, S, nvec, nbar, e, ebar, Matrix.mul_apply]

theorem casimir_central_F : comm Casimir F = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [comm, Casimir, H, E, F, S, nvec, nbar, e, ebar, Matrix.mul_apply]

inductive Concept where
  | Wareham_CGA_Dilator
  | Null_Basis_n_nbar
  | SL2R_Subalgebra
  | SO21_Isomorphic_Form
  | Quadratic_Casimir_3
  deriving DecidableEq, Repr

inductive Edge where
  | generated_by
  | anticommutes_with
  | closes_to
  | has_casimir
  | isomorphic_to
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Wareham_CGA_Dilator, Edge.generated_by, Concept.Null_Basis_n_nbar => true
  | Concept.Wareham_CGA_Dilator, Edge.closes_to, Concept.SL2R_Subalgebra => true
  | Concept.SL2R_Subalgebra, Edge.isomorphic_to, Concept.SO21_Isomorphic_Form => true
  | Concept.SL2R_Subalgebra, Edge.has_casimir, Concept.Quadratic_Casimir_3 => true
  | Concept.Null_Basis_n_nbar, Edge.anticommutes_with, Concept.Wareham_CGA_Dilator => true
  | _, _, _ => false

end WarehamCGADilatorSL2

end noncomputable section
