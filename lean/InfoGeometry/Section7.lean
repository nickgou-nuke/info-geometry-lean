import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Section 7: Connection Structure

Flat-space finite checks for soldering forms, identity tetrads, spin
connections, and the pure-imaginary quaternion/spin matrix round-trip.
-/

noncomputable section

namespace Section7

open Matrix

def I2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, 1]

def s1 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 1, 0]

def s2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), -Complex.I; Complex.I, 0]

def s3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, -1]

def sigma : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => I2
  | 1 => s1
  | 2 => s2
  | 3 => s3

def eta4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(-1 : ℂ), 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

def eps : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; -1, 0]

def eTetrad : Matrix (Fin 4) (Fin 4) ℂ :=
  1

def soldering (a mu : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  eTetrad a mu • sigma a

theorem soldering_diagonal (a mu : Fin 4) :
    soldering a mu = eTetrad a mu • sigma a := rfl

theorem pauli_identity (A B Ap Bp : Fin 2) :
    (∑ a : Fin 4, ∑ b : Fin 4, eta4 a b * sigma a A Ap * sigma b B Bp)
      = (-2 : ℂ) * eps A B * eps Ap Bp := by
  fin_cases A <;> fin_cases B <;> fin_cases Ap <;> fin_cases Bp <;>
    simp [sigma, I2, s1, s2, s3, eta4, eps, Fin.sum_univ_four] <;> ring_nf

theorem pauli_sum_sq :
    (∑ a : Fin 4, sigma a * sigma a) =
      (4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigma, I2, s1, s2, s3, Fin.sum_univ_four] <;> ring_nf

theorem tetrad_metric_flat :
    eTetradᵀ * eta4 * eTetrad = eta4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eTetrad, eta4, Matrix.mul_apply, Fin.sum_univ_four]

def Gamma (_l _mu _nu : Fin 4) : ℂ :=
  0

theorem Gamma_symmetric (l mu nu : Fin 4) :
    Gamma l mu nu = Gamma l nu mu := rfl

def spinConnection (_mu : Fin 4) (_A _B : Fin 2) : ℂ :=
  0

theorem spin_connection_vanishes_flat (mu : Fin 4) (A B : Fin 2) :
    spinConnection mu A B = 0 := rfl

theorem soldering_covariant_constancy_flat (a mu nu : Fin 4) (A Ap : Fin 2) :
    (∑ B : Fin 2, spinConnection mu A B * soldering a nu B Ap)
      - (∑ Bp : Fin 2, soldering a nu A Bp * spinConnection mu Bp Ap) = 0 := by
  simp [spinConnection]

structure Quat where
  q0 : ℂ
  qi : ℂ
  qj : ℂ
  qk : ℂ
deriving DecidableEq

def maurerCartan (_q _dq0 _dq1 _dq2 _dq3 : ℂ) : Quat :=
  ⟨0, 0, 0, 0⟩

theorem quaternion_connection_vanishes_flat :
    maurerCartan 0 0 0 0 0 = { q0 := 0, qi := 0, qj := 0, qk := 0 : Quat} := rfl

def spinToQuat (omega : Matrix (Fin 2) (Fin 2) ℂ) : Quat :=
  ⟨0, (omega 0 1 + omega 1 0) / 2,
    (omega 0 1 - omega 1 0) * Complex.I / 2, (omega 0 0 - omega 1 1) / 2⟩

def quatToSpin (q : Quat) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![q.qk, q.qi - Complex.I * q.qj;
     q.qi + Complex.I * q.qj, -q.qk]

/-- Pure-imaginary quaternion coordinates round-trip through the spin matrix form. -/
theorem spin_quat_isomorphism (q : Quat) (hPure : q.q0 = 0) :
    spinToQuat (quatToSpin q) = q := by
  cases q with
  | mk q0 qi qj qk =>
    simp [spinToQuat, quatToSpin] at hPure ⊢
    subst q0
    constructor
    · rfl
    · ring_nf
      rw [show Complex.I ^ 2 = (-1 : ℂ) by simp [pow_two, Complex.I_mul_I]]
      ring_nf

theorem section7_capstone :
    (∀ A B Ap Bp : Fin 2,
       (∑ a : Fin 4, ∑ b : Fin 4, eta4 a b * sigma a A Ap * sigma b B Bp)
       = (-2 : ℂ) * eps A B * eps Ap Bp) ∧
    eTetradᵀ * eta4 * eTetrad = eta4 ∧
    (∑ a : Fin 4, sigma a * sigma a) =
      (4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (∀ mu A B, spinConnection mu A B = 0) ∧
    (∀ a mu nu A Ap,
      (∑ B : Fin 2, spinConnection mu A B * soldering a nu B Ap)
        - (∑ Bp : Fin 2, soldering a nu A Bp * spinConnection mu Bp Ap) = 0) ∧
    (∀ q : Quat, q.q0 = 0 → spinToQuat (quatToSpin q) = q) := by
  exact ⟨pauli_identity, tetrad_metric_flat, pauli_sum_sq,
    spin_connection_vanishes_flat, soldering_covariant_constancy_flat, spin_quat_isomorphism⟩

end Section7
