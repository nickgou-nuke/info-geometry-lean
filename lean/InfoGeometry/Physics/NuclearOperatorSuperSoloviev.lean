import Mathlib
import InfoGeometry.Physics.NuclearParityGradedHamiltonian

/-!
# Operator-valued super Soloviev parity theory

This module lifts the finite scalar Soloviev parity law to `2 × 2` block
Hamiltonians over an arbitrary associative real operator algebra.

There are two independent `ℤ₂` signs:

* the outer Fock sign, implemented by the block diagonal matrix
  `diag(Γ,-Γ)`;
* the internal parity of each operator coefficient under `x ↦ Γ*x*Γ`.

Consequently an internally **even** off-diagonal channel acquires the usual
Soloviev sign reflection, while an internally **odd** off-diagonal channel has
its internal sign cancelled by the outer Fock sign and the total block is
invariant.

This is an associative operator theorem. Raw non-associative Zorn/split-
octonion multiplication is intentionally not placed under Mathlib matrix
multiplication; such data must enter through a proved associative
representation or envelope.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearOperatorSuperSoloviev

open Matrix
open InfoGeometry.Physics.NuclearParityGradedHamiltonian

variable {A : Type*} [Ring A] [Algebra ℝ A]

abbrev Block2 (A : Type*) [Ring A] := Matrix (Fin 2) (Fin 2) A

/-- Internal parity datum carried by the operator algebra. -/
structure InternalParity (A : Type*) [Ring A] where
  gamma : A
  gamma_sq : gamma * gamma = 1

namespace InternalParity

variable (P : InternalParity A)

/-- Internal conjugation by the grading element. -/
def act (x : A) : A := P.gamma * x * P.gamma

/-- Internally even operator coefficient. -/
def IsEven (x : A) : Prop := P.act x = x

/-- Internally odd operator coefficient. -/
def IsOdd (x : A) : Prop := P.act x = -x

@[simp] theorem act_apply (x : A) :
    P.act x = P.gamma * x * P.gamma := rfl

/-- The internal conjugation is involutive. -/
theorem act_involutive (x : A) : P.act (P.act x) = x := by
  unfold act
  calc
    P.gamma * (P.gamma * x * P.gamma) * P.gamma =
        (P.gamma * P.gamma) * x * (P.gamma * P.gamma) := by
      noncomm_ring
    _ = x := by rw [P.gamma_sq]; simp

end InternalParity

/-- General operator-valued two-sector Hamiltonian. The lower-left channel is
kept independent so the algebraic theorem does not require a star structure. -/
def blockHamiltonian (E0 E1 V W : A) : Block2 A :=
  !![E0, V; W, E1]

/-- Total Fock/internal parity `diag(Γ,-Γ)`. -/
def totalParity (P : InternalParity A) : Block2 A :=
  !![P.gamma, 0; 0, -P.gamma]

/-- Reflection of both off-diagonal channels. -/
def reflectOffDiagonal (E0 E1 V W : A) : Block2 A :=
  blockHamiltonian E0 E1 (-V) (-W)

/-- The total block parity is an involution. -/
theorem totalParity_sq (P : InternalParity A) :
    totalParity P * totalParity P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalParity, Matrix.mul_apply, Fin.sum_univ_two, P.gamma_sq]

/-- Entrywise master superconjugation formula. -/
theorem totalParity_conjugation_formula
    (P : InternalParity A) (E0 E1 V W : A) :
    totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
      !![P.act E0, -P.act V; -P.act W, P.act E1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [totalParity, blockHamiltonian, InternalParity.act,
      Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

/-- Internally even diagonal coefficients and internally even off-diagonal
coefficients give the ordinary Soloviev sign reflection. -/
theorem reflection_of_all_internal_even
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsEven V) (hW : P.IsEven W) :
    totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
      reflectOffDiagonal E0 E1 V W := by
  rw [totalParity_conjugation_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectOffDiagonal, blockHamiltonian,
      InternalParity.IsEven] at hE0 hE1 hV hW ⊢ <;>
    simp_all

/-- Internally even diagonal coefficients and internally odd off-diagonal
coefficients produce a total `ℤ₂`-even super-Hamiltonian: the internal odd sign
is cancelled by the outer Fock sign. -/
theorem invariant_of_even_diagonal_odd_offDiagonal
    (P : InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1)
    (hV : P.IsOdd V) (hW : P.IsOdd W) :
    totalParity P * blockHamiltonian E0 E1 V W * totalParity P =
      blockHamiltonian E0 E1 V W := by
  rw [totalParity_conjugation_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockHamiltonian, InternalParity.IsEven, InternalParity.IsOdd] at
      hE0 hE1 hV hW ⊢ <;>
    simp_all

/-- The master formula itself is involutive because the total parity squares
to the identity. -/
theorem totalParity_action_twice
    (P : InternalParity A) (H : Block2 A) :
    totalParity P * (totalParity P * H * totalParity P) * totalParity P = H := by
  calc
    totalParity P * (totalParity P * H * totalParity P) * totalParity P =
        (totalParity P * totalParity P) * H *
          (totalParity P * totalParity P) := by
      noncomm_ring
    _ = H := by rw [totalParity_sq]; simp

section Star

variable [StarRing A]

/-- Hermitian-style operator Soloviev block with lower-left channel `star V`. -/
def starBlockHamiltonian (E0 E1 V : A) : Block2 A :=
  blockHamiltonian E0 E1 V (star V)

/-- Self-adjoint internal parity datum. -/
def InternalParity.IsSelfAdjoint (P : InternalParity A) : Prop :=
  star P.gamma = P.gamma

/-- Internal evenness is preserved by star for a self-adjoint grading. -/
theorem InternalParity.star_even
    (P : InternalParity A) (hP : P.IsSelfAdjoint)
    {x : A} (hx : P.IsEven x) : P.IsEven (star x) := by
  unfold InternalParity.IsEven InternalParity.act at *
  have h := congrArg star hx
  simpa [star_mul, hP, mul_assoc] using h

/-- Internal oddness is preserved by star for a self-adjoint grading. -/
theorem InternalParity.star_odd
    (P : InternalParity A) (hP : P.IsSelfAdjoint)
    {x : A} (hx : P.IsOdd x) : P.IsOdd (star x) := by
  unfold InternalParity.IsOdd InternalParity.act at *
  have h := congrArg star hx
  simpa [star_mul, hP, mul_assoc] using h

/-- Hermitian-style Soloviev reflection for internally even coupling. -/
theorem starBlock_reflection_of_internal_even
    (P : InternalParity A) (hP : P.IsSelfAdjoint)
    (E0 E1 V : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1) (hV : P.IsEven V) :
    totalParity P * starBlockHamiltonian E0 E1 V * totalParity P =
      starBlockHamiltonian E0 E1 (-V) := by
  have hStar : P.IsEven (star V) := P.star_even hP hV
  have h := reflection_of_all_internal_even P E0 E1 V (star V)
    hE0 hE1 hV hStar
  simpa [starBlockHamiltonian, reflectOffDiagonal, blockHamiltonian] using h

/-- Hermitian-style total super-invariance for internally odd coupling. -/
theorem starBlock_invariant_of_internal_odd
    (P : InternalParity A) (hP : P.IsSelfAdjoint)
    (E0 E1 V : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1) (hV : P.IsOdd V) :
    totalParity P * starBlockHamiltonian E0 E1 V * totalParity P =
      starBlockHamiltonian E0 E1 V := by
  have hStar : P.IsOdd (star V) := P.star_odd hP hV
  exact invariant_of_even_diagonal_odd_offDiagonal P E0 E1 V (star V)
    hE0 hE1 hV hStar

end Star

end InfoGeometry.Physics.NuclearOperatorSuperSoloviev

end noncomputable section
