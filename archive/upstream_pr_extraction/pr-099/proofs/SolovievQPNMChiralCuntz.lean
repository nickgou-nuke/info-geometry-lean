import Mathlib

/-!
# Soloviev QPNM as a Chiral Cuntz Matrix-Unit Shadow

This module records the finite theorem kernel behind the proposed dictionary
between Soloviev's quasiparticle-phonon nuclear model and the chiral
Cuntz/TKK spine of the repository.

The checked layer is deliberately small:

* odd quasiparticle lanes are modeled by nilpotent matrix units `Splus` and
  `Sminus`;
* even phonon/projector lanes are modeled by `Nplus = Splus*Sminus` and
  `Nminus = Sminus*Splus`;
* the grade-zero/RPA truncation keeps only `Nplus,Nminus`;
* the modular/Coriolis generator `h = Nplus - Nminus` satisfies
  `[h,Splus]=2Splus` and `[h,Sminus]=-2Sminus`;
* the detector coincidence matrix layer is represented as the Gram form
  `C = A^* A`.

Scope: these `2 x 2` matrices form a finite CAR/matrix-unit model, not a
faithful representation of the full C*-Cuntz algebra `O_2` with genuine
isometries.  The formal claims in this file are exactly the finite matrix
identities stated below.
-/

noncomputable section

open Matrix
open Complex

namespace SolovievQPNMChiralCuntz

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Right/even projector. -/
def Nplus : M2C := !![(1 : ℂ), 0; 0, 0]

/-- Left/even projector. -/
def Nminus : M2C := !![(0 : ℂ), 0; 0, 1]

/-- Odd raising/tunneling lane. -/
def Splus : M2C := !![(0 : ℂ), 1; 0, 0]

/-- Odd lowering/tunneling lane. -/
def Sminus : M2C := !![(0 : ℂ), 0; 1, 0]

/-- The finite identity. -/
def Itwo : M2C := 1

/-- Modular/Coriolis grading Hamiltonian. -/
def h : M2C := Nplus - Nminus

/-- Matrix commutator. -/
def comm (A B : M2C) : M2C := A * B - B * A

/-- Chiral QPNM toy fiber:
`H = Eplus Nplus + Eminus Nminus + W Splus + W* Sminus`. -/
def qpnmHamiltonian (Eplus Eminus : ℝ) (W : ℂ) : M2C :=
  (Eplus : ℂ) • Nplus + (Eminus : ℂ) • Nminus +
    W • Splus + (starRingEnd ℂ W) • Sminus

/-- RPA/grade-zero truncation: discard the odd `Splus,Sminus` lanes. -/
def rpaTruncation (Eplus Eminus : ℝ) : M2C :=
  (Eplus : ℂ) • Nplus + (Eminus : ℂ) • Nminus

/-- Detector coincidence Gram matrix `C = A^* A`. -/
def coincidenceGram (A : M2C) : M2C := Matrix.conjTranspose A * A

/-- `Splus^2 = 0`: finite algebraic Pauli exclusion in the chiral shadow. -/
theorem Splus_nilpotent : Splus * Splus = 0 := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Splus, Matrix.mul_apply]

/-- `Sminus^2 = 0`: the opposite odd lane is nilpotent as well. -/
theorem Sminus_nilpotent : Sminus * Sminus = 0 := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Sminus, Matrix.mul_apply]

/-- `Nplus^2 = Nplus`: even phonon/projector idempotence. -/
theorem Nplus_idempotent : Nplus * Nplus = Nplus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Nplus, Matrix.mul_apply]

/-- `Nminus^2 = Nminus`: opposite even projector idempotence. -/
theorem Nminus_idempotent : Nminus * Nminus = Nminus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Nminus, Matrix.mul_apply]

/-- `Splus*Sminus = Nplus`: the even phonon lane is an odd loop. -/
theorem Splus_mul_Sminus_eq_Nplus : Splus * Sminus = Nplus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Splus, Sminus, Nplus, Matrix.mul_apply]

/-- `Sminus*Splus = Nminus`: the opposite even lane is the reverse odd loop. -/
theorem Sminus_mul_Splus_eq_Nminus : Sminus * Splus = Nminus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Splus, Sminus, Nminus, Matrix.mul_apply]

/-- Completeness of the finite chiral matrix-unit shadow. -/
theorem chiral_completeness : Splus * Sminus + Sminus * Splus = Itwo := by
  rw [Splus_mul_Sminus_eq_Nplus, Sminus_mul_Splus_eq_Nminus]
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Nplus, Nminus, Itwo]

/-- The finite shadow is partial-isometry/CAR-like, not literal `O_2`
isometry: `Splus^* Splus = Nminus`, not `I`. -/
theorem Splus_adjoint_times_Splus :
    Matrix.conjTranspose Splus * Splus = Nminus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Splus, Nminus, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Similarly, `Sminus^* Sminus = Nplus`. -/
theorem Sminus_adjoint_times_Sminus :
    Matrix.conjTranspose Sminus * Sminus = Nplus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [Sminus, Nplus, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The modular/Coriolis generator activates the odd `Splus` lane with weight `+2`. -/
theorem coriolis_comm_Splus : comm h Splus = (2 : ℂ) • Splus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [comm, h, Nplus, Nminus, Splus]
  all_goals ring_nf

/-- The opposite odd lane has modular/Coriolis weight `-2`. -/
theorem coriolis_comm_Sminus : comm h Sminus = (-2 : ℂ) • Sminus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [comm, h, Nplus, Nminus, Sminus]
  all_goals ring_nf

/-- RPA is exactly the grade-zero truncation of the finite chiral Hamiltonian
when the odd/Coriolis coupling `W` is zero. -/
theorem rpa_exact_when_coupling_zero (Eplus Eminus : ℝ) :
    qpnmHamiltonian Eplus Eminus 0 = rpaTruncation Eplus Eminus := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [qpnmHamiltonian, rpaTruncation, Nplus, Nminus, Splus, Sminus]

/-- Matrix form of the finite QPNM toy Hamiltonian. -/
theorem qpnmHamiltonian_matrix (Eplus Eminus : ℝ) (W : ℂ) :
    qpnmHamiltonian Eplus Eminus W =
      !![(Eplus : ℂ), W; starRingEnd ℂ W, (Eminus : ℂ)] := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [qpnmHamiltonian, Nplus, Nminus, Splus, Sminus]

/-- Coincidence matrices are positive Gram matrices by definition: `C=A^*A`. -/
theorem coincidenceGram_eq_AadjA (A : M2C) :
    coincidenceGram A = Matrix.conjTranspose A * A := rfl

/-- Exact rational identity for the numerical comparison
`1.1777` vs `1.1781`: the gap is `1/2500`.  The Python file audits the
floating comparison with `3*pi/8`. -/
theorem second_moment_decimal_gap :
    (11781 : ℚ) / 10000 - (11777 : ℚ) / 10000 = 1 / 2500 := by
  norm_num

/-- Synthesis theorem: the finite algebraic QPNM/Cuntz shadow is closed. -/
theorem soloviev_qpnm_chiral_cuntz_synthesis :
    Splus * Splus = 0 ∧
    Sminus * Sminus = 0 ∧
    Splus * Sminus = Nplus ∧
    Sminus * Splus = Nminus ∧
    Splus * Sminus + Sminus * Splus = Itwo ∧
    comm h Splus = (2 : ℂ) • Splus ∧
    comm h Sminus = (-2 : ℂ) • Sminus ∧
    (∀ Eplus Eminus : ℝ, qpnmHamiltonian Eplus Eminus 0 = rpaTruncation Eplus Eminus) ∧
    ((11781 : ℚ) / 10000 - (11777 : ℚ) / 10000 = 1 / 2500) := by
  constructor
  · exact Splus_nilpotent
  constructor
  · exact Sminus_nilpotent
  constructor
  · exact Splus_mul_Sminus_eq_Nplus
  constructor
  · exact Sminus_mul_Splus_eq_Nminus
  constructor
  · exact chiral_completeness
  constructor
  · exact coriolis_comm_Splus
  constructor
  · exact coriolis_comm_Sminus
  constructor
  · exact rpa_exact_when_coupling_zero
  · exact second_moment_decimal_gap

end SolovievQPNMChiralCuntz
