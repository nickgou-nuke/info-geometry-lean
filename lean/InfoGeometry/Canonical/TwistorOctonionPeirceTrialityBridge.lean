import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Generic Algebraic Identities for Commutators and Involutions

This module collects generic ring-level identities: associativity makes the
defined associator defect zero; commutators satisfy product derivation rules;
an involution with a central half gives Peirce idempotents; and orthogonal
idempotents yield square-zero off-diagonal products. It also records elementary
scalar incidence equations. These statements do not construct a split-octonion
derivation, an Iwasawa decomposition, a unipotent group action, or a new
twistor theorem.
-/

section

namespace InfoGeometry.Canonical.RingInvolutionIdentities

/-! ### Associativity Defect in Rings -/

section AssociatorAlgebra

variable {A : Type*} [Ring A]

/-- The associator defect expression; under `[Ring A]` it vanishes by associativity. -/
def associator (x y z : A) : A := (x * y) * z - x * (y * z)

/-- In any associative ring, the associator vanishes identically. -/
theorem associator_eq_zero_of_assoc (x y z : A) : associator x y z = 0 := by
  dsimp [associator]
  rw [mul_assoc, sub_self]

/-- Linearity of associator in the left argument. -/
theorem associator_add_left (x₁ x₂ y z : A) :
    associator (x₁ + x₂) y z = associator x₁ y z + associator x₂ y z := by
  dsimp [associator]
  simp only [add_mul, mul_assoc]
  abel

/-- Left annihilation of associator by zero. -/
theorem associator_zero_left (y z : A) : associator (0 : A) y z = 0 := by
  dsimp [associator]
  simp only [zero_mul, sub_self]

end AssociatorAlgebra

/-! ### Commutator Identities for a Symmetrized Product -/

section SymmetrizedProduct

variable {R : Type*} [Ring R]

/-- Lie algebra commutator bracket $[A, B] = A * B - B * A$. -/
def comm (A B : R) : R := A * B - B * A

/-- Derivation identity on products in the left slot: $[A * B, C] = A * [B, C] + [A, C] * B$. -/
theorem comm_mul_left (A B C : R) : comm (A * B) C = A * comm B C + comm A C * B := by
  dsimp [comm]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- Derivation identity on products in the right slot: $[A, B * C] = [A, B] * C + B * [A, C]$. -/
theorem comm_mul_right (A B C : R) : comm A (B * C) = comm A B * C + B * comm A C := by
  dsimp [comm]
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

/-- The symmetrized product of two ring elements. -/
def symmetrizedProduct (ω π : R) : R := ω * π + π * ω

/-- Commutator identity for the symmetrized product, assuming `[ω, π] = c`. -/
theorem symmetrizedProduct_comm_first (ω π c : R) (h_ccr : comm ω π = c) :
    comm (symmetrizedProduct ω π) ω = -(c * ω + ω * c) := by
  have h_comm : comm (ω * ω) π = ω * c + c * ω := by
    calc comm (ω * ω) π
      _ = ω * comm ω π + comm ω π * ω := comm_mul_left ω ω π
      _ = ω * c + c * ω := by rw [h_ccr]
  have h_alg : comm (symmetrizedProduct ω π) ω = - comm (ω * ω) π := by
    dsimp [symmetrizedProduct, comm]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  rw [h_alg, h_comm]
  abel

/-- Companion commutator identity for the symmetrized product. -/
theorem symmetrizedProduct_comm_second (ω π c : R) (h_ccr : comm ω π = c) :
    comm (symmetrizedProduct ω π) π = c * π + π * c := by
  have h_comm : comm ω (π * π) = c * π + π * c := by
    calc comm ω (π * π)
      _ = comm ω π * π + π * comm ω π := comm_mul_right ω π π
      _ = c * π + π * c := by rw [h_ccr]
  have h_alg : comm (symmetrizedProduct ω π) π = comm ω (π * π) := by
    dsimp [symmetrizedProduct, comm]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  rw [h_alg, h_comm]

end SymmetrizedProduct

/-! ### Peirce Idempotents from a Central Half and an Involution -/

section SplitPeircePolarization

variable {A : Type*} [Ring A]

/-- Positive Peirce projector: $P_+ = \mathrm{half} * (1 + \ell)$. -/
def peircePlus (half ℓ : A) : A := half * (1 + ℓ)

/-- Negative Peirce projector: $P_- = \mathrm{half} * (1 - \ell)$. -/
def peirceMinus (half ℓ : A) : A := half * (1 - ℓ)

/-- Idempotency of the positive Peirce projector: $P_+^2 = P_+$. -/
theorem peircePlus_sq (half ℓ : A)
    (h_half_add : half + half = 1)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hℓ : ℓ * ℓ = 1) :
    peircePlus half ℓ * peircePlus half ℓ = peircePlus half ℓ := by
  dsimp [peircePlus]
  have h_sq : (1 + ℓ) * (1 + ℓ) = (1 + 1) * (1 + ℓ) := by
    calc (1 + ℓ) * (1 + ℓ)
      _ = 1 * (1 + ℓ) + ℓ * (1 + ℓ) := by rw [add_mul]
      _ = (1 + ℓ) + (ℓ * 1 + ℓ * ℓ) := by rw [one_mul, mul_add]
      _ = 1 + ℓ + (ℓ + 1) := by rw [mul_one, hℓ]
      _ = (1 + 1) * (1 + ℓ) := by
          simp only [add_mul, one_mul]
          abel
  have h_comm1 : (1 + ℓ) * half = half * (1 + ℓ) := (h_half_comm (1 + ℓ)).symm
  calc (half * (1 + ℓ)) * (half * (1 + ℓ))
    _ = half * ((1 + ℓ) * half) * (1 + ℓ) := by simp only [mul_assoc]
    _ = half * (half * (1 + ℓ)) * (1 + ℓ) := by rw [h_comm1]
    _ = (half * half) * ((1 + ℓ) * (1 + ℓ)) := by simp only [mul_assoc]
    _ = (half * half) * ((1 + 1) * (1 + ℓ)) := by rw [h_sq]
    _ = (half * (half * (1 + 1))) * (1 + ℓ) := by simp only [mul_assoc]
    _ = (half * (half + half)) * (1 + ℓ) := by
        have : half * (1 + 1) = half + half := by
          rw [mul_add, mul_one]
        rw [this]
    _ = (half * 1) * (1 + ℓ) := by rw [h_half_add]
    _ = half * (1 + ℓ) := by rw [mul_one]

/-- Idempotency of the negative Peirce projector: $P_-^2 = P_-$. -/
theorem peirceMinus_sq (half ℓ : A)
    (h_half_add : half + half = 1)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hℓ : ℓ * ℓ = 1) :
    peirceMinus half ℓ * peirceMinus half ℓ = peirceMinus half ℓ := by
  dsimp [peirceMinus]
  have h_sq : (1 - ℓ) * (1 - ℓ) = (1 + 1) * (1 - ℓ) := by
    calc (1 - ℓ) * (1 - ℓ)
      _ = 1 * (1 - ℓ) - ℓ * (1 - ℓ) := by rw [sub_mul]
      _ = (1 - ℓ) - (ℓ * 1 - ℓ * ℓ) := by rw [one_mul, mul_sub]
      _ = (1 - ℓ) - (ℓ - 1) := by rw [mul_one, hℓ]
      _ = (1 + 1) * (1 - ℓ) := by
          simp only [add_mul, one_mul]
          abel
  have h_comm1 : (1 - ℓ) * half = half * (1 - ℓ) := (h_half_comm (1 - ℓ)).symm
  calc (half * (1 - ℓ)) * (half * (1 - ℓ))
    _ = half * ((1 - ℓ) * half) * (1 - ℓ) := by simp only [mul_assoc]
    _ = half * (half * (1 - ℓ)) * (1 - ℓ) := by rw [h_comm1]
    _ = (half * half) * ((1 - ℓ) * (1 - ℓ)) := by simp only [mul_assoc]
    _ = (half * half) * ((1 + 1) * (1 - ℓ)) := by rw [h_sq]
    _ = (half * (half * (1 + 1))) * (1 - ℓ) := by simp only [mul_assoc]
    _ = (half * (half + half)) * (1 - ℓ) := by
        have : half * (1 + 1) = half + half := by
          rw [mul_add, mul_one]
        rw [this]
    _ = (half * 1) * (1 - ℓ) := by rw [h_half_add]
    _ = half * (1 - ℓ) := by rw [mul_one]

/-- Orthogonality $P_+ * P_- = 0$. -/
theorem peirce_orthogonal_pm (half ℓ : A)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hℓ : ℓ * ℓ = 1) :
    peircePlus half ℓ * peirceMinus half ℓ = 0 := by
  dsimp [peircePlus, peirceMinus]
  have h_prod : (1 + ℓ) * (1 - ℓ) = 0 := by
    calc (1 + ℓ) * (1 - ℓ)
      _ = 1 * (1 - ℓ) + ℓ * (1 - ℓ) := by rw [add_mul]
      _ = (1 - ℓ) + (ℓ * 1 - ℓ * ℓ) := by rw [one_mul, mul_sub]
      _ = (1 - ℓ) + (ℓ - 1) := by rw [mul_one, hℓ]
      _ = 0 := by abel
  have h_comm1 : (1 + ℓ) * half = half * (1 + ℓ) := (h_half_comm (1 + ℓ)).symm
  calc (half * (1 + ℓ)) * (half * (1 - ℓ))
    _ = half * ((1 + ℓ) * half) * (1 - ℓ) := by simp only [mul_assoc]
    _ = half * (half * (1 + ℓ)) * (1 - ℓ) := by rw [h_comm1]
    _ = (half * half) * ((1 + ℓ) * (1 - ℓ)) := by simp only [mul_assoc]
    _ = (half * half) * 0 := by rw [h_prod]
    _ = 0 := by rw [mul_zero]

/-- Orthogonality $P_- * P_+ = 0$. -/
theorem peirce_orthogonal_mp (half ℓ : A)
    (h_half_comm : ∀ x : A, half * x = x * half)
    (hℓ : ℓ * ℓ = 1) :
    peirceMinus half ℓ * peircePlus half ℓ = 0 := by
  dsimp [peircePlus, peirceMinus]
  have h_prod : (1 - ℓ) * (1 + ℓ) = 0 := by
    calc (1 - ℓ) * (1 + ℓ)
      _ = 1 * (1 + ℓ) - ℓ * (1 + ℓ) := by rw [sub_mul]
      _ = (1 + ℓ) - (ℓ * 1 + ℓ * ℓ) := by rw [one_mul, mul_add]
      _ = (1 + ℓ) - (ℓ + 1) := by rw [mul_one, hℓ]
      _ = 0 := by abel
  have h_comm1 : (1 - ℓ) * half = half * (1 - ℓ) := (h_half_comm (1 - ℓ)).symm
  calc (half * (1 - ℓ)) * (half * (1 + ℓ))
    _ = half * ((1 - ℓ) * half) * (1 + ℓ) := by simp only [mul_assoc]
    _ = half * (half * (1 - ℓ)) * (1 + ℓ) := by rw [h_comm1]
    _ = (half * half) * ((1 - ℓ) * (1 + ℓ)) := by simp only [mul_assoc]
    _ = (half * half) * 0 := by rw [h_prod]
    _ = 0 := by rw [mul_zero]

/-- Completeness / Partition of Unity: $P_+ + P_- = 1$. -/
theorem peirce_sum (half ℓ : A)
    (h_half_add : half + half = 1) :
    peircePlus half ℓ + peirceMinus half ℓ = 1 := by
  dsimp [peircePlus, peirceMinus]
  calc half * (1 + ℓ) + half * (1 - ℓ)
    _ = half * ((1 + ℓ) + (1 - ℓ)) := by rw [← mul_add]
    _ = half * (1 + 1) := by
        have : (1 + ℓ) + (1 - ℓ) = 1 + 1 := by abel
        rw [this]
    _ = half + half := by rw [mul_add, mul_one]
    _ = 1 := h_half_add

end SplitPeircePolarization

/-! ### Square-Zero Products from Orthogonal Idempotents -/

section OffDiagonalNilpotence

variable {A : Type*} [Ring A]

/-- Off-diagonal product from the positive to the negative projector slot. -/
def offDiagonalPlus (P_plus P_minus X : A) : A :=
  P_plus * X * P_minus

/-- Off-diagonal product from the negative to the positive projector slot. -/
def offDiagonalMinus (P_plus P_minus Y : A) : A :=
  P_minus * Y * P_plus

/-- The positive-to-negative off-diagonal product squares to zero. -/
theorem offDiagonalPlus_sq (P_plus P_minus X : A)
    (h_orth : P_minus * P_plus = 0) :
    offDiagonalPlus P_plus P_minus X * offDiagonalPlus P_plus P_minus X = 0 := by
  dsimp [offDiagonalPlus]
  calc (P_plus * X * P_minus) * (P_plus * X * P_minus)
    _ = (P_plus * X) * (P_minus * P_plus) * (X * P_minus) := by simp only [mul_assoc]
    _ = (P_plus * X) * 0 * (X * P_minus) := by rw [h_orth]
    _ = 0 := by simp only [mul_zero, zero_mul]

/-- The negative-to-positive off-diagonal product squares to zero. -/
theorem offDiagonalMinus_sq (P_plus P_minus Y : A)
    (h_orth : P_plus * P_minus = 0) :
    offDiagonalMinus P_plus P_minus Y * offDiagonalMinus P_plus P_minus Y = 0 := by
  dsimp [offDiagonalMinus]
  calc (P_minus * Y * P_plus) * (P_minus * Y * P_plus)
    _ = (P_minus * Y) * (P_plus * P_minus) * (Y * P_plus) := by simp only [mul_assoc]
    _ = (P_minus * Y) * 0 * (Y * P_plus) := by rw [h_orth]
    _ = 0 := by simp only [mul_zero, zero_mul]

end OffDiagonalNilpotence

/-! ### Scalar Incidence Identities -/

section ScalarIdentities

variable {R : Type*} [Ring R]

/-- Distributivity transports `ω = x * π` to `(x + v) * π`. -/
theorem rightFactor_addition_identity (ω π x v : R) (h_inc : ω = x * π) :
    ω + v * π = (x + v) * π := by
  rw [h_inc, add_mul]

/-- Subtraction transports two scalar equations with a common right factor. -/
theorem rightFactor_subtraction_identity (ω₁ ω₂ π x₁ x₂ : R)
    (h1 : ω₁ = x₁ * π) (h2 : ω₂ = x₂ * π) :
    ω₁ - ω₂ = (x₁ - x₂) * π := by
  rw [h1, h2, sub_mul]


end ScalarIdentities


end InfoGeometry.Canonical.RingInvolutionIdentities
