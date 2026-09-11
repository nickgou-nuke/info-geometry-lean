import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Parity-graded Hamiltonians

A small native algebraic owner for Hamiltonians split into parts that are even
and odd under conjugation by an involution.

For an involution `P`, an even operator `H₀`, and an odd operator `V`, the
one-parameter Hamiltonian

`H(λ) = H₀ + λ • V`

satisfies

`P * H(λ) * P = H(-λ)`.

This is purely an associative-algebra theorem.  No physical interpretation of
`P`, `H₀`, `V`, or `λ` is built into the definitions.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearParityGradedHamiltonian

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Conjugation by an algebra element, without assuming invertibility. -/
def conjugate (P X : A) : A :=
  P * X * P

/-- The algebraic involution condition used by the parity packet. -/
def IsInvolution (P : A) : Prop :=
  P * P = 1

/-- An operator is even when conjugation by `P` fixes it. -/
def EvenUnderConjugation (P X : A) : Prop :=
  conjugate P X = X

/-- An operator is odd when conjugation by `P` changes its sign. -/
def OddUnderConjugation (P X : A) : Prop :=
  conjugate P X = -X

/-- Affine one-parameter Hamiltonian with a distinguished interaction term. -/
def parameterHamiltonian (H0 V : A) (lambda : ℝ) : A :=
  H0 + lambda • V

@[simp] theorem conjugate_add (P X Y : A) :
    conjugate P (X + Y) = conjugate P X + conjugate P Y := by
  unfold conjugate
  noncomm_ring

@[simp] theorem conjugate_sub (P X Y : A) :
    conjugate P (X - Y) = conjugate P X - conjugate P Y := by
  unfold conjugate
  noncomm_ring

@[simp] theorem conjugate_smul (P X : A) (r : ℝ) :
    conjugate P (r • X) = r • conjugate P X := by
  unfold conjugate
  rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

/-- Conjugation by an involution is itself involutive. -/
theorem conjugate_involutive
    {P : A} (hP : IsInvolution P) (X : A) :
    conjugate P (conjugate P X) = X := by
  unfold conjugate IsInvolution at *
  calc
    P * (P * X * P) * P = (P * P) * X * (P * P) := by noncomm_ring
    _ = X := by rw [hP]; simp

/-- The identity operator is even under any algebraic involution. -/
theorem one_even
    {P : A} (hP : IsInvolution P) :
    EvenUnderConjugation P (1 : A) := by
  unfold EvenUnderConjugation conjugate IsInvolution at *
  simpa [mul_assoc] using hP

/-- Sums of even operators remain even. -/
theorem even_add
    {P X Y : A}
    (hX : EvenUnderConjugation P X)
    (hY : EvenUnderConjugation P Y) :
    EvenUnderConjugation P (X + Y) := by
  unfold EvenUnderConjugation at *
  rw [conjugate_add, hX, hY]

/-- Real scalar multiples preserve the even sector. -/
theorem even_smul
    {P X : A} (r : ℝ)
    (hX : EvenUnderConjugation P X) :
    EvenUnderConjugation P (r • X) := by
  unfold EvenUnderConjugation at *
  rw [conjugate_smul, hX]

/-- Real scalar multiples preserve the odd sector. -/
theorem odd_smul
    {P X : A} (r : ℝ)
    (hX : OddUnderConjugation P X) :
    OddUnderConjugation P (r • X) := by
  unfold OddUnderConjugation at *
  rw [conjugate_smul, hX]
  simp

/-- Sums of odd operators remain odd. -/
theorem odd_add
    {P X Y : A}
    (hX : OddUnderConjugation P X)
    (hY : OddUnderConjugation P Y) :
    OddUnderConjugation P (X + Y) := by
  unfold OddUnderConjugation at *
  rw [conjugate_add, hX, hY]
  simp [add_comm]

/-- Core parity-graded Hamiltonian theorem:

`P H0 P = H0` and `P V P = -V` imply
`P (H0 + λ V) P = H0 - λ V = H(-λ)`.
-/
theorem conjugate_parameterHamiltonian
    {P H0 V : A}
    (hEven : EvenUnderConjugation P H0)
    (hOdd : OddUnderConjugation P V)
    (lambda : ℝ) :
    conjugate P (parameterHamiltonian H0 V lambda) =
      parameterHamiltonian H0 V (-lambda) := by
  unfold parameterHamiltonian EvenUnderConjugation OddUnderConjugation at *
  rw [conjugate_add, conjugate_smul, hEven, hOdd]
  simp

/-- Equivalent subtraction form of the parameter-reversal theorem. -/
theorem conjugate_even_plus_odd_eq_sub
    {P H0 V : A}
    (hEven : EvenUnderConjugation P H0)
    (hOdd : OddUnderConjugation P V)
    (lambda : ℝ) :
    conjugate P (H0 + lambda • V) = H0 - lambda • V := by
  have h := conjugate_parameterHamiltonian hEven hOdd lambda
  simpa [parameterHamiltonian, sub_eq_add_neg] using h

/-- The parameter-sign action is a `ℤ₂` symmetry when `P` is an involution. -/
theorem parameter_sign_action_involutive
    {P H0 V : A}
    (hP : IsInvolution P)
    (lambda : ℝ) :
    conjugate P (conjugate P (parameterHamiltonian H0 V lambda)) =
      parameterHamiltonian H0 V lambda := by
  exact conjugate_involutive hP _

end InfoGeometry.Physics.NuclearParityGradedHamiltonian

end noncomputable section
