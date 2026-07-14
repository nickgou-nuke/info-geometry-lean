import Mathlib
import InfoGeometry.Physics.MD006OperatorEigenoperators
import InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

/-!
# Repaired MD 013: finite Clifford algebraic structures

Source: `github-nick:nickgou-nuke/MD`, file `013.md`.

Chapter 13 develops Clifford zero divisors, idempotents, nilpotents, Clifford
bundles, spinor bundles, spin representations, and projector/Fock pictures.
The bundle, manifold, Dirac-operator, spin-classification, and index-theoretic
claims are not finite algebraic theorems in this repository owner.

This file formalizes the theorem-safe finite socket:

* nontrivial idempotents give explicit left/right zero-divisor witnesses;
* square-zero nilpotents give explicit zero-divisor witnesses;
* a zero-divisor relation gives a nontrivial kernel witness for multiplication;
* the existing `2 × 2` matrix-unit algebra gives a one-mode CAR shadow where
  `E12` and `E21` are nilpotent, their products are orthogonal projectors, and
  those projectors partition the identity.

No theorem here asserts Clifford bundle construction, Chevalley bundle
identification, `∂ = d - δ`, spin-structure existence, Morita/classification of
Clifford modules, primitive/minimal-ideal classification, or index formulas.
-/

noncomputable section

namespace MD013CliffordAlgebraicStructures

set_option linter.unusedSimpArgs false

open Matrix
open InfoGeometry.Physics.MD001MatrixQuantumGeometry
open InfoGeometry.Physics.MD006OperatorEigenoperators
open InfoGeometry.Physics.MD007QuantumEigenoperatorInterpretation

/-- Explicit left zero-divisor witness data in an associative algebra. -/
structure LeftZeroDivisor (R : Type) [Mul R] [Zero R] where
  a : R
  annihilator : R
  ha : a ≠ 0
  hannihilator : annihilator ≠ 0
  hmul : a * annihilator = 0

/-- Explicit right zero-divisor witness data in an associative algebra. -/
structure RightZeroDivisor (R : Type) [Mul R] [Zero R] where
  a : R
  annihilator : R
  ha : a ≠ 0
  hannihilator : annihilator ≠ 0
  hmul : annihilator * a = 0

/-- A nontrivial idempotent gives a left zero-divisor witness `e(1-e)=0`. -/
def leftZeroDivisor_of_nontrivial_idempotent {R : Type} [Ring R]
    (e : R) (hidem : e * e = e) (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    LeftZeroDivisor R := by
  refine ⟨e, 1 - e, hne0, ?_, ?_⟩
  · intro h
    exact hne1 (sub_eq_zero.mp h).symm
  · calc
      e * (1 - e) = e - e * e := by noncomm_ring
      _ = 0 := by rw [hidem]; abel

/-- A nontrivial idempotent gives a right zero-divisor witness `(1-e)e=0`. -/
def rightZeroDivisor_of_nontrivial_idempotent {R : Type} [Ring R]
    (e : R) (hidem : e * e = e) (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    RightZeroDivisor R := by
  refine ⟨e, 1 - e, hne0, ?_, ?_⟩
  · intro h
    exact hne1 (sub_eq_zero.mp h).symm
  · calc
      (1 - e) * e = e - e * e := by noncomm_ring
      _ = 0 := by rw [hidem]; abel

/-- A square-zero nonzero nilpotent gives a left zero-divisor witness. -/
def leftZeroDivisor_of_square_zero {R : Type} [Mul R] [Zero R]
    (n : R) (hne0 : n ≠ 0) (hsq : n * n = 0) : LeftZeroDivisor R :=
  ⟨n, n, hne0, hne0, hsq⟩

/-- A square-zero nonzero nilpotent gives a right zero-divisor witness. -/
def rightZeroDivisor_of_square_zero {R : Type} [Mul R] [Zero R]
    (n : R) (hne0 : n ≠ 0) (hsq : n * n = 0) : RightZeroDivisor R :=
  ⟨n, n, hne0, hne0, hsq⟩

/-- A right-zero-divisor relation is exactly a nontrivial kernel witness for right multiplication. -/
theorem rightKernelWitness_of_rightZeroDivisor {R : Type} [Mul R] [Zero R]
    (a b : R) (hb : b ≠ 0) (hba : b * a = 0) :
    ∃ x : R, x ≠ 0 ∧ x * a = 0 :=
  ⟨b, hb, hba⟩

/-- A left-zero-divisor relation is exactly a nontrivial kernel witness for left multiplication. -/
theorem leftKernelWitness_of_leftZeroDivisor {R : Type} [Mul R] [Zero R]
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

/-- The complementary matrix-unit projector is idempotent. -/
theorem E22_idempotent : E22 * E22 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22, Matrix.mul_apply, Fin.sum_univ_two]

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

/-- The creation/annihilation matrix unit `E21` is square-zero. -/
theorem E21_square_zero : E21 * E21 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E21, Matrix.mul_apply, Fin.sum_univ_two]

/-- One-mode CAR product `E12 E21` gives the first projector. -/
theorem E12_mul_E21 : E12 * E21 = E11 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, E11, Matrix.mul_apply, Fin.sum_univ_two]

/-- One-mode CAR product `E21 E12` gives the second projector. -/
theorem E21_mul_E12 : E21 * E12 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, E22, Matrix.mul_apply, Fin.sum_univ_two]

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

/-- Repaired theorem-safe Chapter 13 finite Clifford-algebra packet. -/
theorem repaired_MD013_clifford_algebra_packet {R : Type} [Ring R]
    (e n a b : R) (heidem : e * e = e) (he0 : e ≠ 0) (he1 : e ≠ 1)
    (hn0 : n ≠ 0) (hn2 : n * n = 0) (hb0 : b ≠ 0) (hba : b * a = 0) :
    e * (1 - e) = 0 ∧
    (1 - e) * e = 0 ∧
    (∃ y : R, y ≠ 0 ∧ n * y = 0) ∧
    (∃ x : R, x ≠ 0 ∧ x * a = 0) ∧
    E12 * E12 = 0 ∧
    E21 * E21 = 0 ∧
    E12 * E21 + E21 * E12 = E11 + E22 ∧
    E12 * E21 + E21 * E12 = 1 ∧
    (E12 * E21) * (E12 * E21) = E12 * E21 ∧
    (E21 * E12) * (E21 * E12) = E21 * E12 ∧
    (E12 * E21) * (E21 * E12) = 0 ∧
    (E21 * E12) * (E12 * E21) = 0 := by
  refine ⟨?_, ?_, ⟨n, hn0, hn2⟩, rightKernelWitness_of_rightZeroDivisor a b hb0 hba,
    E12_square_zero, E21_square_zero, oneModeCAR_matrix_units,
    oneModeCAR_projector_partition_identity, oneModeCAR_projector_left,
    oneModeCAR_projector_right, oneModeCAR_projectors_orthogonal.1,
    oneModeCAR_projectors_orthogonal.2⟩
  · exact (leftZeroDivisor_of_nontrivial_idempotent e heidem he0 he1).hmul
  · exact (rightZeroDivisor_of_nontrivial_idempotent e heidem he0 he1).hmul

end MD013CliffordAlgebraicStructures

end noncomputable section
