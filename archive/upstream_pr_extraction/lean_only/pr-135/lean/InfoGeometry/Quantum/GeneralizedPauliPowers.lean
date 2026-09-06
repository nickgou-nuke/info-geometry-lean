import InfoGeometry.Quantum.GeneralizedPauli

/-!
# Power calculus for finite generalized Pauli pairs

This module derives the power commutation and ordered-monomial multiplication
laws from the existing `FiniteWeylPair` relation `Z X = q • X Z`. The proofs are
structural and apply in every algebra represented by that owner; no matrix-entry
enumeration is used.
-/

noncomputable section

namespace InfoGeometry.Physics.HestenesCuntzPhaseSpace

variable {N : ℕ} {A : Type*} [Ring A] [Algebra ℂ A]

/-- Moving momentum through a coordinate power accumulates the expected Weyl phase. -/
theorem FiniteWeylPair.momentum_mul_coordinate_pow
    (W : FiniteWeylPair N A) (n : ℕ) :
    W.momentum * W.coordinate ^ n =
      (W.q ^ n : ℂ) • (W.coordinate ^ n * W.momentum) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        W.momentum * W.coordinate ^ (n + 1) =
            (W.momentum * W.coordinate ^ n) * W.coordinate := by
              rw [pow_succ, ← mul_assoc]
        _ = (W.q ^ n • (W.coordinate ^ n * W.momentum)) * W.coordinate := by
              rw [ih]
        _ = W.q ^ n • ((W.coordinate ^ n * W.momentum) * W.coordinate) := by
              rw [smul_mul_assoc]
        _ = W.q ^ n • (W.coordinate ^ n * (W.momentum * W.coordinate)) := by
              rw [mul_assoc]
        _ = W.q ^ (n + 1) • (W.coordinate ^ (n + 1) * W.momentum) := by
              rw [W.weyl_relation, mul_smul_comm, smul_smul, pow_succ]
              rw [pow_succ W.coordinate n]
              rw [mul_assoc]

/-- Moving a momentum power through a coordinate power accumulates `q^(m*n)`. -/
theorem FiniteWeylPair.momentum_pow_mul_coordinate_pow
    (W : FiniteWeylPair N A) (m n : ℕ) :
    W.momentum ^ m * W.coordinate ^ n =
      (W.q ^ (m * n) : ℂ) • (W.coordinate ^ n * W.momentum ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc,
        W.momentum_mul_coordinate_pow, smul_mul_assoc, smul_smul]
      rw [Nat.succ_mul, pow_add]
      simp only [← mul_assoc]

/-- The ordered generalized-Pauli monomial `X^a Z^b`. -/
def FiniteWeylPair.monomial (W : FiniteWeylPair N A) (a b : ℕ) : A :=
  W.coordinate ^ a * W.momentum ^ b

/-- Multiplication law for ordered generalized-Pauli monomials. -/
theorem FiniteWeylPair.monomial_mul
    (W : FiniteWeylPair N A) (a b c d : ℕ) :
    W.monomial a b * W.monomial c d =
      (W.q ^ (b * c) : ℂ) • W.monomial (a + c) (b + d) := by
  change (W.coordinate ^ a * W.momentum ^ b) *
      (W.coordinate ^ c * W.momentum ^ d) =
    (W.q ^ (b * c) : ℂ) •
      (W.coordinate ^ (a + c) * W.momentum ^ (b + d))
  simp only [mul_assoc]
  rw [← mul_assoc (W.momentum ^ b), W.momentum_pow_mul_coordinate_pow]
  simp only [mul_smul_comm, smul_mul_assoc]
  simp only [← mul_assoc]
  rw [pow_add W.momentum b d]
  rw [mul_assoc]
  rw [pow_add W.coordinate a c]

end InfoGeometry.Physics.HestenesCuntzPhaseSpace
