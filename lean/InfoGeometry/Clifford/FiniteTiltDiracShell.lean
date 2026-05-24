import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.FiniteTiltDiracShell

Proof-only finite Dirac shell built from the concrete `Cl(1,1)` Pauli model.

This file stays on the algebraic side:

* the odd tilt generators are the real Pauli matrices `Eplus` and `Eminus`;
* the even rotation generator is `J1`;
* the local shell operator is the finite odd-even combination
  `Eplus + Eminus + m • J1`;
* its square closes exactly on the even scalar lane.

No OSp representation theorem.
No analytic current density.
No zeta claim.
-/

noncomputable section

open scoped Matrix
open scoped Polynomial

namespace InfoGeometry.Clifford.FiniteTiltDiracShell

open InfoGeometry.Clifford.Cl11Matrix

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- Odd tilt generator `Q_A`. -/
@[rep_depth operator]
def tiltOddA : Mat2 := Eplus

/-- Odd tilt generator `Q_B`. -/
@[rep_depth operator]
def tiltOddB : Mat2 := Eminus

/-- Even rotation generator `J`. -/
@[rep_depth operator]
def tiltEvenJ : Mat2 := J1

@[simp, rep_depth operator]
theorem tiltOddA_sq :
    tiltOddA * tiltOddA = 1 := by
  simpa [tiltOddA] using Eplus_sq

@[simp, rep_depth operator]
theorem tiltOddB_sq :
    tiltOddB * tiltOddB = -1 • (1 : Mat2) := by
  simpa [tiltOddB] using Eminus_sq

@[simp, rep_depth operator]
theorem tiltOddA_mul_tiltOddB :
    tiltOddA * tiltOddB = tiltEvenJ := by
  simpa [tiltOddA, tiltOddB, tiltEvenJ] using Eplus_mul_Eminus

@[simp, rep_depth operator]
theorem tiltOddB_mul_tiltOddA :
    tiltOddB * tiltOddA = - tiltEvenJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddB, tiltOddA, tiltEvenJ, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp, rep_depth operator]
theorem tiltEvenJ_sq :
    tiltEvenJ * tiltEvenJ = 1 := by
  simpa [tiltEvenJ] using J1_sq

@[simp, rep_depth operator]
theorem tiltEvenJ_mul_tiltOddA :
    tiltEvenJ * tiltOddA = - tiltOddB := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp, rep_depth operator]
theorem tiltOddA_mul_tiltEvenJ :
    tiltOddA * tiltEvenJ = tiltOddB := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp, rep_depth operator]
theorem tiltEvenJ_mul_tiltOddB :
    tiltEvenJ * tiltOddB = - tiltOddA := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp, rep_depth operator]
theorem tiltOddB_mul_tiltEvenJ :
    tiltOddB * tiltEvenJ = tiltOddA := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1,
      Matrix.mul_apply, Fin.sum_univ_two]

/--
Local Dirac shell operator:

`D_m = Q_A + Q_B + m J`.
-/
@[rep_depth operator]
def finiteTiltDiracShell (m : ℝ) : Mat2 :=
  tiltOddA + tiltOddB + m • tiltEvenJ

/-- Super-Casimir readout: the square of the finite shell operator. -/
@[rep_depth operator]
def finiteTiltSuperCasimir (m : ℝ) : Mat2 :=
  finiteTiltDiracShell m * finiteTiltDiracShell m

/--
Boundary current of the finite tilt shell.

This is the odd part `Q_A + Q_B` of the local `Cl(1,1)` atom.
It is the discrete current density across the shell boundary.
-/
@[rep_depth operator]
def finiteTiltBoundaryCurrent : Mat2 :=
  tiltOddA + tiltOddB

/-- The finite shell current-density readout is definitionally the boundary current. -/
@[rep_depth operator]
def finiteTiltCurrentDensity : Mat2 :=
  finiteTiltBoundaryCurrent

/-- The current-density readout is definitionally the boundary current. -/
@[rep_depth operator]
theorem finiteTiltCurrentDensity_eq_boundaryCurrent :
    finiteTiltCurrentDensity = finiteTiltBoundaryCurrent := by
  rfl

/-- The boundary current is nilpotent. -/
@[rep_depth operator]
theorem finiteTiltBoundaryCurrent_sq_zero :
    finiteTiltBoundaryCurrent * finiteTiltBoundaryCurrent = 0 := by
  unfold finiteTiltBoundaryCurrent
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tiltOddA, tiltOddB, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The current-density readout is nilpotent. -/
@[rep_depth operator]
theorem finiteTiltCurrentDensity_sq_zero :
    finiteTiltCurrentDensity * finiteTiltCurrentDensity = 0 := by
  simpa [finiteTiltCurrentDensity_eq_boundaryCurrent] using finiteTiltBoundaryCurrent_sq_zero

/-- The shell operator splits into boundary current plus mass term. -/
@[rep_depth operator]
theorem finiteTiltDiracShell_eq_boundaryCurrent_add_mass (m : ℝ) :
    finiteTiltDiracShell m = finiteTiltBoundaryCurrent + m • tiltEvenJ := by
  unfold finiteTiltDiracShell finiteTiltBoundaryCurrent
  rfl

/--
The finite tilt Dirac shell closes on the even scalar lane:

`D_m^2 = m^2 · 1`.
-/
theorem finiteTiltDiracShell_sq (m : ℝ) :
    finiteTiltDiracShell m * finiteTiltDiracShell m =
      (m ^ 2 : ℝ) • (1 : Mat2) := by
  have h_explicit :
      finiteTiltDiracShell m =
        !![(1 : ℝ), 1 + m; m - 1, (-1 : ℝ)] := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [finiteTiltDiracShell, tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1] <;>
      linarith
  rw [h_explicit]
  ext i j <;> fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
    try ring

/-- The super-Casimir readout is exactly the scalar even closure. -/
theorem finiteTiltSuperCasimir_eq (m : ℝ) :
    finiteTiltSuperCasimir m = (m ^ 2 : ℝ) • (1 : Mat2) := by
  simpa [finiteTiltSuperCasimir] using finiteTiltDiracShell_sq m

/-- The finite shell has vanishing trace. -/
theorem finiteTiltDiracShell_trace (m : ℝ) :
    Matrix.trace (finiteTiltDiracShell m) = 0 := by
  simp [finiteTiltDiracShell, tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1,
    Matrix.trace, Fin.sum_univ_two]

/-- The finite shell determinant is `-m^2`. -/
@[rep_depth operator]
theorem finiteTiltDiracShell_det (m : ℝ) :
    Matrix.det (finiteTiltDiracShell m) = - m ^ 2 := by
  have h_explicit :
      finiteTiltDiracShell m =
        !![(1 : ℝ), 1 + m; m - 1, (-1 : ℝ)] := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [finiteTiltDiracShell, tiltOddA, tiltOddB, tiltEvenJ, Eplus, Eminus, J1] <;>
      linarith
  rw [h_explicit]
  simp [Matrix.det_fin_two]
  ring

/-- The finite shell characteristic polynomial is `X^2 - m^2`. -/
@[rep_depth operator]
theorem finiteTiltDiracShell_charpoly (m : ℝ) :
    (finiteTiltDiracShell m).charpoly = Polynomial.X ^ 2 - Polynomial.C (m ^ 2 : ℝ) := by
  rw [Matrix.charpoly_fin_two, finiteTiltDiracShell_trace, finiteTiltDiracShell_det]
  simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[rep_depth operator]
def FiniteTiltDiracShellSpectralTarget : Prop :=
  ∀ m : ℝ, Matrix.trace (finiteTiltDiracShell m) = 0 ∧
    Matrix.det (finiteTiltDiracShell m) = - m ^ 2 ∧
    (finiteTiltDiracShell m).charpoly = Polynomial.X ^ 2 - Polynomial.C (m ^ 2 : ℝ)

theorem finiteTiltDiracShellSpectralTarget :
    FiniteTiltDiracShellSpectralTarget := by
  intro m
  constructor
  · exact finiteTiltDiracShell_trace m
  constructor
  · exact finiteTiltDiracShell_det m
  · exact finiteTiltDiracShell_charpoly m

@[rep_depth operator]
def FiniteTiltDiracShellOwnerTarget : Prop :=
  ∀ m : ℝ, finiteTiltDiracShell m * finiteTiltDiracShell m =
    (m ^ 2 : ℝ) • (1 : Mat2)

theorem finiteTiltDiracShellOwnerTarget :
    FiniteTiltDiracShellOwnerTarget := by
  intro m
  exact finiteTiltDiracShell_sq m

end InfoGeometry.Clifford.FiniteTiltDiracShell
