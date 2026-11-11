/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.BinaryWeyl
import InfoGeometry.Projective.BinarySymplecticGeometry
import Mathlib.Algebra.Lie.OfAssociative

/-!
# The signed two-qubit lift of binary projective incidence

Each binary label `((a₁,b₁),(a₂,b₂))` is lifted to the actual matrix
`X^a₁ Z^b₁ ⊗ X^a₂ Z^b₂`. The cocycle is retained in multiplication and the
symplectic form detects commutation. These are four-by-four matrices over the
stated coefficient ring; no compact or quaternionic real form is identified.
-/

namespace InfoGeometry.Quantum.TwoQubitPauli

open Matrix
open scoped Kronecker
open Projective.BinarySymplectic BinaryWeyl

variable {R : Type*} [CommRing R]

/-- The full two-factor matrix carrier, with its ordinary matrix multiplication. -/
abbrev Operator (R : Type*) := Matrix (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) R

/-- Ordered binary Weyl words in two tensor factors. -/
def pauli (v : Label) : Operator R :=
  word v.1.1 v.1.2 ⊗ₖ word v.2.1 v.2.2

@[simp] theorem pauli_zero : pauli (R := R) 0 = 1 := by
  simp [pauli]

/-- The central sign discarded by the label diagram is present in matrix multiplication. -/
theorem pauli_mul (v w : Label) :
    pauli (R := R) v * pauli w = phase (R := R) (cocycle v w) • pauli (v + w) := by
  simp only [pauli, ← Matrix.mul_kronecker_mul, word_mul,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← phase_add]
  simp only [cocycle, add_comm (v.2.2 * w.2.1)]
  rfl

theorem pauli_mul_self (v : Label) :
    pauli (R := R) v * pauli v = phase (R := R) (cocycle v v) • (1 : Operator R) := by
  rw [pauli_mul, label_add_self, pauli_zero]

/-- An explicit right inverse is available for every word over every coefficient ring. -/
theorem pauli_mul_inverse (v : Label) :
    pauli (R := R) v * (phase (R := R) (cocycle v v) • pauli v) = 1 := by
  rw [mul_smul_comm, pauli_mul_self, smul_smul, phase_mul_self, one_smul]

theorem pauli_ne_zero [Nontrivial R] (v : Label) : pauli (R := R) v ≠ 0 := by
  intro h
  have hi := pauli_mul_inverse (R := R) v
  rw [h, zero_mul] at hi
  exact zero_ne_one hi

/-- Scalar coefficients can be read faithfully from a fixed invertible matrix word. -/
theorem smul_pauli_injective (v : Label) :
    Function.Injective (fun r : R => r • pauli (R := R) v) := by
  intro r s h
  have hi := congrArg (fun A : Operator R => A *
    (phase (R := R) (cocycle v v) • pauli v)) h
  simp only [smul_mul_assoc, pauli_mul_inverse] at hi
  have he := congrArg (fun A : Operator R => A (0, 0) (0, 0)) hi
  simpa using he

/-- Reversing the order changes the matrix product by the symplectic sign. -/
theorem pauli_phase_commutation (v w : Label) :
    pauli (R := R) v * pauli w =
      phase (R := R) (symplectic v w) • (pauli w * pauli v) := by
  rw [pauli_mul, pauli_mul, smul_smul, ← phase_add, add_comm w v]
  congr 2
  simp [symplectic, add_assoc, CharTwo.add_self_eq_zero]

/-- The ordinary associative-ring Lie bracket, with its phase-sensitive coefficient. -/
theorem pauli_lie (v w : Label) :
    ⁅pauli (R := R) v, pauli (R := R) w⁆ =
      (phase (R := R) (cocycle v w) - phase (R := R) (cocycle w v)) • pauli (v + w) := by
  rw [Ring.lie_def, pauli_mul, pauli_mul, add_comm w v, sub_smul]

/-- The ordered product of the three line labels is a specified scalar matrix. -/
theorem pauli_line_product (v w : Label) :
    pauli (R := R) v * pauli w * pauli (v + w) =
      phase (R := R) (cocycle v w + cocycle (v + w) (v + w)) • (1 : Operator R) := by
  rw [pauli_mul, smul_mul_assoc, pauli_mul_self, smul_smul, ← phase_add]

/-- In characteristic zero, binary isotropy is exactly matrix commutation. -/
theorem pauli_commute_iff [CharZero R] (v w : Label) :
    Commute (pauli (R := R) v) (pauli w) ↔ symplectic v w = 0 := by
  change pauli (R := R) v * pauli w = pauli w * pauli v ↔ _
  rw [pauli_mul, pauli_mul, add_comm w v]
  constructor
  · intro h
    have hc := phase_injective (smul_pauli_injective (v + w) h)
    simpa [symplectic, hc] using CharTwo.add_self_eq_zero (cocycle w v)
  · intro h
    have hc : cocycle v w = cocycle w v := CharTwo.add_eq_zero.mp h
    rw [hc]

theorem pauli_anticommute_of_pairing_one (v w : Label)
    (h : symplectic v w = 1) :
    pauli (R := R) v * pauli w = -(pauli w * pauli v) := by
  rw [pauli_phase_commutation, h, phase_one, neg_one_smul]

/-- Pairwise commutation on the three-point set is decided by its generating pair. -/
theorem line_pairwise_commute_iff [CharZero R] (v w : Label) :
    (∀ x ∈ line v w, ∀ y ∈ line v w,
      Commute (pauli (R := R) x) (pauli y)) ↔ symplectic v w = 0 := by
  simp only [pauli_commute_iff]
  exact line_isotropic_iff v w

private instance decidablePauliCommute [DecidableEq R] (v w : Label) :
    Decidable (Commute (pauli (R := R) v) (pauli w)) :=
  inferInstanceAs (Decidable (pauli (R := R) v * pauli w = pauli w * pauli v))

/-- Exactly fifteen of the thirty-five binary projective lines lift to commuting triples. -/
theorem commuting_operator_lines_card [CharZero R] [DecidableEq R] :
    (lines.filter (fun L => ∀ x ∈ L, ∀ y ∈ L,
      Commute (pauli (R := R) x) (pauli y))).card = 15 := by
  simp only [pauli_commute_iff]
  exact commutingLines_card

/-- A carrier-matched witness: shift and clock on the first factor do not commute. -/
theorem first_factor_noncommute [CharZero R] :
    pauli (R := R) ((1, 0), (0, 0)) * pauli ((0, 1), (0, 0)) ≠
      pauli ((0, 1), (0, 0)) * pauli ((1, 0), (0, 0)) := by
  intro h
  have hc := (pauli_commute_iff (R := R) ((1, 0), (0, 0)) ((0, 1), (0, 0))).mp h
  norm_num [symplectic, cocycle] at hc

end InfoGeometry.Quantum.TwoQubitPauli
