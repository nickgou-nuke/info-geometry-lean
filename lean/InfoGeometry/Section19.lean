import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# Section 19: finite `Cl(4,C)` matrix shadow

This file repairs the Section 19 prose into a theorem-safe finite model.

#### BUCKET 1: CLOSED FINITE THEOREMS
Using the already-property Pauli-Dirac matrices, we construct four
`4 x 4` complex matrices
`E0 = i γ0`, `E1 = γ1`, `E2 = γ2`, and `E3 = γ3`. Each squares to `-I`, and
distinct generators anticommute. This is a finite matrix representation of the
`Cl(4,C)` generator relations with negative square convention.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None. These are direct consequences of the finite Clifford theorem.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove a full algebra isomorphism `Cl(4,C) ≃ M₄(C)`, does
not construct tensor products or `M₂(H)`, and does not identify real-algebra
forms. The generator list in the source prose using `I ⊗ iσ₁` together with
`σ₃ ⊗ iσ₁` is not copied as a theorem because those two matrices commute, so
they cannot be distinct Clifford generators.
-/

noncomputable section

namespace Section19

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open InfoGeometry.Clifford.DiracPauliGamma

abbrev Mat4C := InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix

def cl4Generator : Fin 4 → Mat4C
  | 0 => Complex.I • InfoGeometry.Clifford.DiracPauliGamma.gamma0
  | 1 => InfoGeometry.Clifford.DiracPauliGamma.gamma1
  | 2 => InfoGeometry.Clifford.DiracPauliGamma.gamma2
  | 3 => InfoGeometry.Clifford.DiracPauliGamma.gamma3

theorem cl4Generator_square (mu : Fin 4) :
    cl4Generator mu * cl4Generator mu = -(1 : Mat4C) := by
  fin_cases mu
  · change (Complex.I • InfoGeometry.Clifford.DiracPauliGamma.gamma0) * (Complex.I • InfoGeometry.Clifford.DiracPauliGamma.gamma0) =
      -(1 : Mat4C)
    rw [Matrix.smul_mul, Matrix.mul_smul, InfoGeometry.Clifford.DiracPauliGamma.gamma0_mul_self]
    ext i j
    by_cases h : i = j
    · subst j
      simp [Complex.I_mul_I]
    · simp [Matrix.one_apply, h]
  · exact InfoGeometry.Clifford.DiracPauliGamma.gamma1_mul_self
  · exact InfoGeometry.Clifford.DiracPauliGamma.gamma2_mul_self
  · exact InfoGeometry.Clifford.DiracPauliGamma.gamma3_mul_self

theorem cl4Generator_anticomm (mu nu : Fin 4) (h : mu ≠ nu) :
    cl4Generator mu * cl4Generator nu + cl4Generator nu * cl4Generator mu =
      (0 : Mat4C) := by
  fin_cases mu <;> fin_cases nu <;> try contradiction
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma1_anticomm]
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma2_anticomm]
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma3_anticomm]
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma0_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma2_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma3_anticomm]
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma2_gamma0_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma2_gamma1_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma2_gamma3_anticomm]
  · simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [InfoGeometry.Clifford.DiracPauliGamma.gamma3_gamma0_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma3_gamma1_anticomm]
  · simp [cl4Generator, InfoGeometry.Clifford.DiracPauliGamma.gamma3_gamma2_anticomm]

/-- The corrected spatial gamma pair anticommutes. -/
theorem corrected_spatial_pair_anticomm :
    InfoGeometry.Clifford.DiracPauliGamma.gamma1 * InfoGeometry.Clifford.DiracPauliGamma.gamma3 +
      InfoGeometry.Clifford.DiracPauliGamma.gamma3 * InfoGeometry.Clifford.DiracPauliGamma.gamma1 = (0 : Mat4C) :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma3_anticomm

theorem section19_capstone :
    (∀ mu : Fin 4, cl4Generator mu * cl4Generator mu = -(1 : Mat4C)) ∧
    (∀ mu nu : Fin 4, mu ≠ nu →
      cl4Generator mu * cl4Generator nu + cl4Generator nu * cl4Generator mu =
        (0 : Mat4C)) := by
  exact ⟨cl4Generator_square, cl4Generator_anticomm⟩

end Section19
