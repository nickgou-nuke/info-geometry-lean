import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Section5

/-!
# Section 19: finite `Cl(4,C)` matrix shadow

This file repairs the Section 19 prose into a theorem-safe finite model.

#### BUCKET 1: CLOSED FINITE THEOREMS
Using the already-certified Section 5 Pauli-Dirac matrices, we construct four
`4 x 4` complex matrices
`E0 = i γ0`, `E1 = γ1`, `E2 = γ2`, and `E3 = γ3`.  Each squares to `-I`, and
distinct generators anticommute.  This is a finite matrix representation of the
`Cl(4,C)` generator relations with negative square convention.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  These are direct consequences of Section 5's finite Clifford theorem.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove a full algebra isomorphism `Cl(4,C) ≃ M₄(C)`, does
not construct tensor products or `M₂(H)`, and does not identify real-algebra
forms.  The generator list in the source prose using `I ⊗ iσ₁` together with
`σ₃ ⊗ iσ₁` is not copied as a theorem because those two matrices commute, so
they cannot be distinct Clifford generators.
-/

noncomputable section

namespace Section19

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

abbrev Mat4C := Section5.DiracMatrix

def cl4Generator : Fin 4 → Mat4C
  | 0 => Complex.I • Section5.γ0
  | 1 => Section5.γ1
  | 2 => Section5.γ2
  | 3 => Section5.γ3

theorem cl4Generator_square (mu : Fin 4) :
    cl4Generator mu * cl4Generator mu = -(1 : Mat4C) := by
  fin_cases mu
  · change (Complex.I • Section5.γ0) * (Complex.I • Section5.γ0) = -(1 : Mat4C)
    rw [Matrix.smul_mul, Matrix.mul_smul, Section5.γ0_sq]
    ext i j
    by_cases h : i = j
    · subst j
      simp [Complex.I_mul_I]
    · simp [Matrix.one_apply, h]
  · exact (Section5.γi_sq_neg).1
  · exact (Section5.γi_sq_neg).2.1
  · exact (Section5.γi_sq_neg).2.2

theorem cl4Generator_anticomm (mu nu : Fin 4) (h : mu ≠ nu) :
    cl4Generator mu * cl4Generator nu + cl4Generator nu * cl4Generator mu =
      (0 : Mat4C) := by
  fin_cases mu <;> fin_cases nu <;> try contradiction
  · -- 0,1
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [(Section5.clifford_anticomm).1]
  · -- 0,2
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [(Section5.clifford_anticomm).2.1]
  · -- 0,3
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [(Section5.clifford_anticomm).2.2.1]
  · -- 1,0
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [show Section5.γ1 * Section5.γ0 + Section5.γ0 * Section5.γ1 =
        (0 : Mat4C) by simpa [add_comm] using (Section5.clifford_anticomm).1]
  · -- 1,2
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.1]
  · -- 1,3
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.2.1]
  · -- 2,0
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [show Section5.γ2 * Section5.γ0 + Section5.γ0 * Section5.γ2 =
        (0 : Mat4C) by simpa [add_comm] using (Section5.clifford_anticomm).2.1]
  · -- 2,1
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.1]
  · -- 2,3
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.2.2]
  · -- 3,0
    simp only [cl4Generator, Matrix.smul_mul, Matrix.mul_smul]
    rw [← smul_add]
    simp [show Section5.γ3 * Section5.γ0 + Section5.γ0 * Section5.γ3 =
        (0 : Mat4C) by simpa [add_comm] using (Section5.clifford_anticomm).2.2.1]
  · -- 3,1
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.2.1]
  · -- 3,2
    simp [cl4Generator, (Section5.clifford_anticomm).2.2.2.2.2]

/-- The corrected Section 5 spatial gamma pair anticommutes. -/
theorem corrected_spatial_pair_anticomm :
    Section5.γ1 * Section5.γ3 + Section5.γ3 * Section5.γ1 = (0 : Mat4C) :=
  (Section5.clifford_anticomm).2.2.2.2.1

theorem section19_capstone :
    (∀ mu : Fin 4, cl4Generator mu * cl4Generator mu = -(1 : Mat4C)) ∧
    (∀ mu nu : Fin 4, mu ≠ nu →
      cl4Generator mu * cl4Generator nu + cl4Generator nu * cl4Generator mu =
        (0 : Mat4C)) := by
  exact ⟨cl4Generator_square, cl4Generator_anticomm⟩

end Section19
