import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Clifford

variable {B : Type*} [Ring B]

def I_mat : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, 1]
def Gamma_mat : Matrix (Fin 2) (Fin 2) B := !![1, 0; 0, -1]
def J_mat : Matrix (Fin 2) (Fin 2) B := !![0, 1; 1, 0]
def K_mat : Matrix (Fin 2) (Fin 2) B := !![0, 1; -1, 0]

@[simp] theorem Gamma_sq : Gamma_mat (B := B) * Gamma_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gamma_mat, I_mat, Matrix.mul_apply]

@[simp] theorem J_sq : J_mat (B := B) * J_mat = I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, I_mat, Matrix.mul_apply]

@[simp] theorem K_sq : K_mat (B := B) * K_mat = - I_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, I_mat, Matrix.mul_apply]

theorem J_Gamma : J_mat (B := B) * Gamma_mat = -(Gamma_mat * J_mat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat, Gamma_mat, Matrix.mul_apply]

theorem K_eq_Gamma_J : K_mat (B := B) = Gamma_mat * J_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [K_mat, Gamma_mat, J_mat, Matrix.mul_apply]

/-- Reconstruction of an operator in M₂(B) from its four B-valued Stokes components. -/
def reconstruct_jones (a0 a3 a1 a2 : B) : Matrix (Fin 2) (Fin 2) B :=
  a0 • I_mat + a3 • Gamma_mat + a1 • J_mat + a2 • K_mat

/-- The fundamental decomposition mapping abstract Stokes coordinate entries onto the Cl(1, 1) sheet grading. -/
theorem jones_decomposition_eq (a0 a3 a1 a2 : B) :
    reconstruct_jones a0 a3 a1 a2 = !![a0 + a3, a1 + a2; a1 - a2, a0 - a3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [reconstruct_jones, I_mat, Gamma_mat, J_mat, K_mat] <;> abel

/-! ## Complex circular coordinates with operator coefficients -/

/-- A sheet packet with coefficients in an arbitrary complex module `B`.
When `B = Module.End ℂ W`, these are operator-valued rather than scalar
coordinates. -/
@[ext] structure CausalOperatorCoordinates (B : Type*) where
  scalar : B
  chiral : B
  exchange : B
  circular : B

section ComplexCoordinates

variable [Module ℂ B]

/--
Reconstruction in the ordered causal packet `(1, Γ, J, -i ΓJ)`.
The entrywise form is valid for noncommuting operator coefficients because no
products between distinct coefficients are introduced.
-/
def reconstruct_causal (A : CausalOperatorCoordinates B) :
    Matrix (Fin 2) (Fin 2) B :=
  !![A.scalar + A.chiral, A.exchange - Complex.I • A.circular;
     A.exchange + Complex.I • A.circular, A.scalar - A.chiral]

/-- Extract the four operator-valued causal coordinates of a sheet matrix. -/
noncomputable def causalCoordinates (A : Matrix (Fin 2) (Fin 2) B) :
    CausalOperatorCoordinates B where
  scalar := (1 / 2 : ℂ) • (A 0 0 + A 1 1)
  chiral := (1 / 2 : ℂ) • (A 0 0 - A 1 1)
  exchange := (1 / 2 : ℂ) • (A 0 1 + A 1 0)
  circular := (Complex.I / 2 : ℂ) • (A 0 1 - A 1 0)

/-- Every operator-valued sheet matrix is recovered from its causal coordinates. -/
@[simp] theorem reconstruct_causalCoordinates
    (A : Matrix (Fin 2) (Fin 2) B) :
    reconstruct_causal (causalCoordinates A) = A := by
  have hIhalf : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
    rw [div_eq_mul_inv, ← mul_assoc, Complex.I_mul_I]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reconstruct_causal, causalCoordinates, smul_smul, hIhalf] <;>
    module

/-- Causal coordinates are unique. -/
@[simp] theorem causalCoordinates_reconstruct
    (A : CausalOperatorCoordinates B) :
    causalCoordinates (reconstruct_causal A) = A := by
  rcases A with ⟨A0, A3, A1, A2⟩
  apply CausalOperatorCoordinates.ext
  · change (1 / 2 : ℂ) • ((A0 + A3) + (A0 - A3)) = A0
    rw [show (A0 + A3) + (A0 - A3) = (2 : ℂ) • A0 by module]
    simp [smul_smul]
  · change (1 / 2 : ℂ) • ((A0 + A3) - (A0 - A3)) = A3
    rw [show (A0 + A3) - (A0 - A3) = (2 : ℂ) • A3 by module]
    simp [smul_smul]
  · change (1 / 2 : ℂ) •
      ((A1 - Complex.I • A2) + (A1 + Complex.I • A2)) = A1
    rw [show (A1 - Complex.I • A2) + (A1 + Complex.I • A2) =
      (2 : ℂ) • A1 by module]
    simp [smul_smul]
  · change (Complex.I / 2 : ℂ) •
      ((A1 - Complex.I • A2) - (A1 + Complex.I • A2)) = A2
    rw [show (A1 - Complex.I • A2) - (A1 + Complex.I • A2) =
      (-2 * Complex.I : ℂ) • A2 by module]
    rw [smul_smul]
    have hc : (Complex.I / 2 : ℂ) * (-2 * Complex.I) = 1 := by
      field_simp
      rw [Complex.I_sq]
      norm_num
    rw [hc, one_smul]

/-- The causal packet is exactly the full operator-valued `2 × 2` space. -/
noncomputable def causalOperatorCoordinatesEquiv :
    CausalOperatorCoordinates B ≃ Matrix (Fin 2) (Fin 2) B where
  toFun := reconstruct_causal
  invFun := causalCoordinates
  left_inv := causalCoordinates_reconstruct
  right_inv := reconstruct_causalCoordinates

/-- The requested specialization `M₂(End W)` of the coefficient theorem. -/
abbrev SheetEndomorphismMatrix
    (W : Type*) [AddCommMonoid W] [Module ℂ W] :=
  Matrix (Fin 2) (Fin 2) (Module.End ℂ W)

end ComplexCoordinates

/-! ## Strict Dirac/Clifford theorem boundary -/

section DiracBoundary

variable {ι R Op : Type*} [CommRing R] [Ring Op] [Algebra R Op]

/-- Anticommutator in the represented operator algebra. -/
def operatorAnticommutator (A C : Op) : Op := A * C + C * A

/--
An operator family is a Dirac-matrix system precisely when the metric
anticommutation relation is supplied. Coordinate expansion alone does not
construct a value of this predicate.
-/
def IsDiracMatrixSystem (g : ι → ι → R) (gamma : ι → Op) : Prop :=
  ∀ a b, operatorAnticommutator (gamma a) (gamma b) =
    algebraMap R Op (2 * g a b)

/-- Read back one Clifford relation from a proved Dirac-matrix system. -/
theorem anticommutator_eq_metric
    {g : ι → ι → R} {gamma : ι → Op}
    (h : IsDiracMatrixSystem g gamma) (a b : ι) :
    operatorAnticommutator (gamma a) (gamma b) =
      algebraMap R Op (2 * g a b) :=
  h a b

end DiracBoundary

end InfoGeometry.Clifford
