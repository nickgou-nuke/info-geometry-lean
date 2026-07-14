import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

/-!
# Ring-hom transport of finite algebraic relations

This file states transport facts directly in mathlib's canonical language:
ring homomorphisms, multiplication, addition, zero, and finite induction over
`ℕ`.  There are no local anticommutator wrapper definitions and no proof-carrying
stage structure.

The results are finite algebraic transport lemmas only; they do not assert a
direct-limit completion, Hilbert/Krein completion, analytic boundary theorem, or
physical validation claim.
-/

set_option autoImplicit false

universe u

namespace RingHomTransport

variable {A B : Type*} [Ring A] [Ring B]
variable (φ : A →+* B)

/-- A ring homomorphism preserves idempotents. -/
theorem ringHom_preserves_idempotent (P : A) (hP : P * P = P) :
    φ P * φ P = φ P := by
  rw [← RingHom.map_mul, hP]

/-- A ring homomorphism preserves square-zero elements. -/
theorem ringHom_preserves_square_zero (Q : A) (hQ : Q * Q = 0) :
    φ Q * φ Q = 0 := by
  rw [← RingHom.map_mul, hQ, RingHom.map_zero]

/-- A ring homomorphism preserves the anticommutator expression `Q * R + R * Q`. -/
theorem ringHom_preserves_superbracket (Q R Z : A) (h : Q * R + R * Q = Z) :
    φ Q * φ R + φ R * φ Q = φ Z := by
  rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add, h]

section InductiveSystem

variable (Stage : ℕ → Type u) [∀ n, Ring (Stage n)]
variable (bond : ∀ n, Stage n →+* Stage (n + 1))
variable (Q R_op H Z : ∀ n, Stage n)

/--
If a square-zero element is transported by the stage maps, then it remains
square-zero at every finite stage.
-/
theorem nilpotent_transport_induction
    (h_Q_step : ∀ n, Q (n + 1) = bond n (Q n))
    (hQ0 : Q 0 * Q 0 = 0) (n : ℕ) :
    Q n * Q n = 0 := by
  induction n with
  | zero =>
      exact hQ0
  | succ k ih =>
      rw [h_Q_step k, ← RingHom.map_mul, ih, RingHom.map_zero]

/--
If `Q * R + R * Q = H + Z` holds initially and all four terms are transported
by the stage maps, then the relation holds at every finite stage.
-/
theorem superbracket_transport_induction
    (h_Q_step : ∀ n, Q (n + 1) = bond n (Q n))
    (h_R_step : ∀ n, R_op (n + 1) = bond n (R_op n))
    (h_H_step : ∀ n, H (n + 1) = bond n (H n))
    (h_Z_step : ∀ n, Z (n + 1) = bond n (Z n))
    (h_init : Q 0 * R_op 0 + R_op 0 * Q 0 = H 0 + Z 0) (n : ℕ) :
    Q n * R_op n + R_op n * Q n = H n + Z n := by
  induction n with
  | zero =>
      exact h_init
  | succ k ih =>
      rw [h_Q_step k, h_R_step k, h_H_step k, h_Z_step k]
      rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_add, ih, RingHom.map_add]

end InductiveSystem

end RingHomTransport
