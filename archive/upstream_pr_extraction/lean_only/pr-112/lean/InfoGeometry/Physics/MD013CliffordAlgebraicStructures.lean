import Mathlib.Tactic
import InfoGeometry.Physics.MD006OperatorEigenoperators
import InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

/-!
# Repaired MD 013: finite Clifford algebraic structures

Source: `github-nick:nickgou-nuke/MD`, file `013.md`.

Chapter 13 develops Clifford zero divisors, idempotents, nilpotents, Clifford
bundles, spinor bundles, spin representations, and projector/Fock pictures.
The bundle, manifold, Dirac-operator, spin-classification, and index-theoretic
claims are not finite algebraic theorems in this repository owner.

This file formalizes the finite algebraic consequences:

* nontrivial idempotents give explicit left/right zero-divisor witnesses;
* square-zero nilpotents give explicit zero-divisor witnesses;
* a zero-divisor relation gives a nontrivial kernel property for multiplication;
* the existing `2 × 2` matrix-unit algebra gives a one-mode CAR shadow where
  `E12` and `E21` are nilpotent, their products are orthogonal projectors, and
  those projectors partition the identity.

No theorem here asserts Clifford bundle construction, Chevalley bundle
identification, `∂ = d - δ`, spin-structure existence, Morita/classification of
Clifford modules, primitive/minimal-ideal classification, or index formulas.
-/

noncomputable section

namespace InfoGeometry.Physics.MD013CliffordAlgebraicStructures

set_option linter.unusedSimpArgs false

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD006OperatorEigenoperators
open InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

/-- Explicit left zero-divisor property data, represented as a subtype. -/
def LeftZeroDivisor (R : Type) [Mul R] [Zero R] :=
  { p : R × R // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 * p.2 = 0 }

namespace LeftZeroDivisor

abbrev a {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) : R := w.1.1
abbrev annihilator {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) : R := w.1.2
abbrev ha {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) : w.a ≠ 0 := w.2.1
abbrev hannihilator {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) : w.annihilator ≠ 0 := w.2.2.1
abbrev hmul {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) : w.a * w.annihilator = 0 := w.2.2.2

end LeftZeroDivisor

/-- Explicit right zero-divisor property data, represented as a subtype. -/
def RightZeroDivisor (R : Type) [Mul R] [Zero R] :=
  { p : R × R // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 * p.1 = 0 }

def IsLeftZeroDivisor {R : Type} [Mul R] [Zero R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ a * b = 0

def IsRightZeroDivisor {R : Type} [Mul R] [Zero R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ b * a = 0

theorem leftZeroDivisor_iff_isLeftZeroDivisor
    {R : Type} [Mul R] [Zero R] (w : LeftZeroDivisor R) :
    IsLeftZeroDivisor (LeftZeroDivisor.a w) := by
  exact ⟨LeftZeroDivisor.ha w, LeftZeroDivisor.annihilator w,
    LeftZeroDivisor.hannihilator w, LeftZeroDivisor.hmul w⟩

theorem rightZeroDivisor_iff_isRightZeroDivisor
    {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) :
    IsRightZeroDivisor w.1.1 := by
  exact ⟨w.2.1, w.1.2, w.2.2.1, w.2.2.2⟩

namespace RightZeroDivisor

abbrev a {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) : R := w.1.1
abbrev annihilator {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) : R := w.1.2
abbrev ha {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) : w.a ≠ 0 := w.2.1
abbrev hannihilator {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) : w.annihilator ≠ 0 := w.2.2.1
abbrev hmul {R : Type} [Mul R] [Zero R] (w : RightZeroDivisor R) : w.annihilator * w.a = 0 := w.2.2.2

end RightZeroDivisor

/-- A nontrivial idempotent gives a left zero-divisor property `e(1-e)=0`. -/
def leftZeroDivisor_of_nontrivial_idempotent {R : Type} [Ring R]
    (e : R) (hidem : e * e = e) (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    LeftZeroDivisor R := by
  refine ⟨(e, 1 - e), hne0, ?_, ?_⟩
  · intro h
    exact hne1 (sub_eq_zero.mp h).symm
  · calc
      e * (1 - e) = e - e * e := by noncomm_ring
      _ = 0 := by rw [hidem]; abel

/-- A nontrivial idempotent gives a right zero-divisor property `(1-e)e=0`. -/
def rightZeroDivisor_of_nontrivial_idempotent {R : Type} [Ring R]
    (e : R) (hidem : e * e = e) (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    RightZeroDivisor R := by
  refine ⟨(e, 1 - e), hne0, ?_, ?_⟩
  · intro h
    exact hne1 (sub_eq_zero.mp h).symm
  · calc
      (1 - e) * e = e - e * e := by noncomm_ring
      _ = 0 := by rw [hidem]; abel

/-- A square-zero nonzero nilpotent gives a left zero-divisor property. -/
def leftZeroDivisor_of_square_zero {R : Type} [Mul R] [Zero R]
    (n : R) (hne0 : n ≠ 0) (hsq : n * n = 0) : LeftZeroDivisor R :=
  ⟨(n, n), hne0, hne0, hsq⟩

/-- A square-zero nonzero nilpotent gives a right zero-divisor property. -/
def rightZeroDivisor_of_square_zero {R : Type} [Mul R] [Zero R]
    (n : R) (hne0 : n ≠ 0) (hsq : n * n = 0) : RightZeroDivisor R :=
  ⟨(n, n), hne0, hne0, hsq⟩

/-- A right-zero-divisor relation is exactly a nontrivial kernel property for right multiplication. -/
theorem rightKernel_of_rightZeroDivisor {R : Type} [Mul R] [Zero R]
    (a b : R) (hb : b ≠ 0) (hba : b * a = 0) :
    ∃ x : R, x ≠ 0 ∧ x * a = 0 :=
  ⟨b, hb, hba⟩

/-- A left-zero-divisor relation is exactly a nontrivial kernel property for left multiplication. -/
theorem leftKernel_of_leftZeroDivisor {R : Type} [Mul R] [Zero R]
    (a b : R) (hb : b ≠ 0) (hab : a * b = 0) :
    ∃ x : R, x ≠ 0 ∧ a * x = 0 :=
  ⟨b, hb, hab⟩

/-- Orthogonal idempotents have an idempotent sum. -/
theorem orthogonal_idempotent_sum {R : Type} [NonUnitalNonAssocRing R]
    (e f : R) (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0) :
    (e + f) * (e + f) = e + f := by
  calc
    (e + f) * (e + f) = e * e + e * f + f * e + f * f := by noncomm_ring
    _ = e + f := by rw [he, hf, hef, hfe]; abel

/-- Matrix-unit projector/idempotent used as the finite Clifford projector shadow. -/
theorem E11_idempotent : E11 * E11 = E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, Matrix.mul_apply, Fin.sum_univ_two]

theorem E11_ne_zero : E11 ≠ 0 := by
  intro h
  have h00 := congrArg (fun M => M (0 : Fin 2) (0 : Fin 2)) h
  simp [E11] at h00

/-- The complementary matrix-unit projector is idempotent. -/
theorem E22_idempotent : E22 * E22 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22, Matrix.mul_apply, Fin.sum_univ_two]

theorem E22_ne_zero : E22 ≠ 0 := by
  intro h
  have h11 := congrArg (fun M => M (1 : Fin 2) (1 : Fin 2)) h
  simp [E22] at h11

/-- The two matrix-unit projectors are orthogonal in one order. -/
theorem E11_mul_E22_zero : E11 * E22 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, E22, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two matrix-unit projectors are orthogonal in the other order. -/
theorem E22_mul_E11_zero : E22 * E11 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, E22, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two matrix-unit projectors partition the identity. -/
theorem E11_add_E22_eq_one : E11 + E22 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, E22]

/-- The sum of the two orthogonal matrix-unit projectors is idempotent. -/
theorem E11_add_E22_idempotent : (E11 + E22) * (E11 + E22) = E11 + E22 :=
  orthogonal_idempotent_sum E11 E22 E11_idempotent E22_idempotent E11_mul_E22_zero E22_mul_E11_zero

/-- The creation/annihilation matrix unit `E12` is square-zero. -/
theorem E12_square_zero : E12 * E12 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, Matrix.mul_apply, Fin.sum_univ_two]

theorem E12_ne_zero : E12 ≠ 0 := by
  intro h
  have h01 := congrArg (fun M => M (0 : Fin 2) (1 : Fin 2)) h
  simp [E12] at h01

theorem E12_cube_zero : E12 ^ 3 = 0 := by
  rw [pow_succ, pow_two, E12_square_zero]
  simp

/-- The creation/annihilation matrix unit `E21` is square-zero. -/
theorem E21_square_zero : E21 * E21 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E21, Matrix.mul_apply, Fin.sum_univ_two]

theorem E21_ne_zero : E21 ≠ 0 := by
  intro h
  have h10 := congrArg (fun M => M (1 : Fin 2) (0 : Fin 2)) h
  simp [E21] at h10

theorem E21_cube_zero : E21 ^ 3 = 0 := by
  rw [pow_succ, pow_two, E21_square_zero]
  simp

theorem E12_isLeftZeroDivisor : IsLeftZeroDivisor E12 := by
  exact ⟨E12_ne_zero, E12, E12_ne_zero, E12_square_zero⟩

theorem E12_isRightZeroDivisor : IsRightZeroDivisor E12 := by
  exact ⟨E12_ne_zero, E12, E12_ne_zero, E12_square_zero⟩

theorem E21_isLeftZeroDivisor : IsLeftZeroDivisor E21 := by
  exact ⟨E21_ne_zero, E21, E21_ne_zero, E21_square_zero⟩

theorem E21_isRightZeroDivisor : IsRightZeroDivisor E21 := by
  exact ⟨E21_ne_zero, E21, E21_ne_zero, E21_square_zero⟩

/-- One-mode CAR product `E12 E21` gives the first projector. -/
theorem E12_mul_E21 : E12 * E21 = E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, E11, Matrix.mul_apply, Fin.sum_univ_two]

theorem E12_mul_E21_ne_zero : E12 * E21 ≠ 0 := by
  rw [E12_mul_E21]
  exact E11_ne_zero

/-- One-mode CAR product `E21 E12` gives the second projector. -/
theorem E21_mul_E12 : E21 * E12 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, E22, Matrix.mul_apply, Fin.sum_univ_two]

theorem E21_mul_E12_ne_zero : E21 * E12 ≠ 0 := by
  rw [E21_mul_E12]
  exact E22_ne_zero

/-- Finite one-mode CAR anticommutator in matrix-unit form. -/
theorem oneModeCAR_matrix_units :
    E12 * E21 + E21 * E12 = E11 + E22 := by
  rw [E12_mul_E21, E21_mul_E12]

/-- The CAR number/vacuum product `E12 E21` is a projector. -/
theorem oneModeCAR_projector_left :
    (E12 * E21) * (E12 * E21) = E12 * E21 := by
  rw [E12_mul_E21, E11_idempotent]

/-- The CAR number/vacuum product `E21 E12` is a projector. -/
theorem oneModeCAR_projector_right :
    (E21 * E12) * (E21 * E12) = E21 * E12 := by
  rw [E21_mul_E12, E22_idempotent]

/-- The two CAR projectors are orthogonal. -/
theorem oneModeCAR_projectors_orthogonal :
    (E12 * E21) * (E21 * E12) = 0 ∧ (E21 * E12) * (E12 * E21) = 0 := by
  constructor
  · rw [E12_mul_E21, E21_mul_E12, E11_mul_E22_zero]
  · rw [E12_mul_E21, E21_mul_E12, E22_mul_E11_zero]

/-- The two CAR projectors sum to the identity. -/
theorem oneModeCAR_projector_partition_identity :
    E12 * E21 + E21 * E12 = 1 := by
  rw [oneModeCAR_matrix_units, E11_add_E22_eq_one]

end InfoGeometry.Physics.MD013CliffordAlgebraicStructures

end noncomputable section
