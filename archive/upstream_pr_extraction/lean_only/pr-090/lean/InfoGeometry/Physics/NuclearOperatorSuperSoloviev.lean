import Mathlib
import InfoGeometry.Physics.NuclearParityGradedHamiltonian

/-!
# Operator-valued super Soloviev parity theory

This module lifts the finite scalar Soloviev parity law to `2 × 2` block
Hamiltonians over an arbitrary associative operator ring.

There are two independent `ℤ₂` signs:

* the outer Fock sign, implemented by the block diagonal matrix
  `diag(Γ,-Γ)`;
* the internal parity of each operator coefficient under `x ↦ Γ*x*Γ`.

The internal parity is proved to be a multiplicative involution.  Its even and
odd eigenspaces therefore satisfy the exact superalgebra multiplication table

`A₀ A₀ ⊆ A₀`, `A₀ A₁ ⊆ A₁`, `A₁ A₀ ⊆ A₁`, `A₁ A₁ ⊆ A₀`.

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

variable {A : Type*} [Ring A]

abbrev Block2 (A : Type*) [Ring A] := Matrix (Fin 2) (Fin 2) A

/-- Internal parity datum carried by the operator ring. -/
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

/-- Internal parity preserves addition. -/
theorem act_add (x y : A) : P.act (x + y) = P.act x + P.act y := by
  unfold act
  noncomm_ring

/-- Internal parity preserves negation. -/
theorem act_neg (x : A) : P.act (-x) = -P.act x := by
  unfold act
  noncomm_ring

/-- Internal parity is multiplicative. -/
theorem act_mul (x y : A) : P.act (x * y) = P.act x * P.act y := by
  unfold act
  calc
    P.gamma * (x * y) * P.gamma =
        P.gamma * x * 1 * y * P.gamma := by simp [mul_assoc]
    _ = P.gamma * x * (P.gamma * P.gamma) * y * P.gamma := by
      rw [P.gamma_sq]
    _ = (P.gamma * x * P.gamma) * (P.gamma * y * P.gamma) := by
      noncomm_ring

/-- Even coefficients are closed under addition. -/
theorem even_add {x y : A} (hx : P.IsEven x) (hy : P.IsEven y) :
    P.IsEven (x + y) := by
  unfold IsEven at *
  rw [P.act_add, hx, hy]

/-- Odd coefficients are closed under addition. -/
theorem odd_add {x y : A} (hx : P.IsOdd x) (hy : P.IsOdd y) :
    P.IsOdd (x + y) := by
  unfold IsOdd at *
  rw [P.act_add, hx, hy]
  simp

/-- Even times even is even. -/
theorem even_mul_even {x y : A} (hx : P.IsEven x) (hy : P.IsEven y) :
    P.IsEven (x * y) := by
  unfold IsEven at *
  rw [P.act_mul, hx, hy]

/-- Even times odd is odd. -/
theorem even_mul_odd {x y : A} (hx : P.IsEven x) (hy : P.IsOdd y) :
    P.IsOdd (x * y) := by
  unfold IsEven IsOdd at *
  rw [P.act_mul, hx, hy]
  simp

/-- Odd times even is odd. -/
theorem odd_mul_even {x y : A} (hx : P.IsOdd x) (hy : P.IsEven y) :
    P.IsOdd (x * y) := by
  unfold IsEven IsOdd at *
  rw [P.act_mul, hx, hy]
  simp

/-- Odd times odd is even. -/
theorem odd_mul_odd {x y : A} (hx : P.IsOdd x) (hy : P.IsOdd y) :
    P.IsEven (x * y) := by
  unfold IsEven IsOdd at *
  rw [P.act_mul, hx, hy]
  simp

/-- Ordinary associative commutator. -/
def comm (x y : A) : A := x * y - y * x

/-- Associative anticommutator. -/
def anticomm (x y : A) : A := x * y + y * x

/-- Even-even commutators remain even. -/
theorem even_comm_even {x y : A} (hx : P.IsEven x) (hy : P.IsEven y) :
    P.IsEven (comm x y) := by
  unfold comm IsEven
  simp only [sub_eq_add_neg, P.act_add, P.act_neg, P.act_mul, hx, hy]

/-- Even-odd commutators remain odd. -/
theorem even_comm_odd {x y : A} (hx : P.IsEven x) (hy : P.IsOdd y) :
    P.IsOdd (comm x y) := by
  unfold comm IsOdd
  simp only [sub_eq_add_neg, P.act_add, P.act_neg, P.act_mul, hx, hy]
  noncomm_ring

/-- Odd-odd superbrackets (anticommutators) are even. -/
theorem odd_anticomm_odd {x y : A} (hx : P.IsOdd x) (hy : P.IsOdd y) :
    P.IsEven (anticomm x y) := by
  unfold anticomm IsEven
  rw [P.act_add, P.act_mul, P.act_mul, hx, hy]
  simp

/-- Consolidated `ℤ₂` multiplication table. -/
theorem superalgebra_multiplication_packet
    {e0 e1 o0 o1 : A}
    (he0 : P.IsEven e0) (he1 : P.IsEven e1)
    (ho0 : P.IsOdd o0) (ho1 : P.IsOdd o1) :
    P.IsEven (e0 * e1) ∧
      P.IsOdd (e0 * o0) ∧
      P.IsOdd (o0 * e0) ∧
      P.IsEven (o0 * o1) :=
  ⟨P.even_mul_even he0 he1,
    P.even_mul_odd he0 ho0,
    P.odd_mul_even ho0 he0,
    P.odd_mul_odd ho0 ho1⟩

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
