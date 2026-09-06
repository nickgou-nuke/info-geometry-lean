import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical.Drazin

/-- Structure `IsDrazinInverse`. -/
structure IsDrazinInverse {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop where
  comm       : a * b = b * a
  idempotent : b * a * b = b
  power      : a^(k + 1) * b = a^k

namespace IsDrazinInverse

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- Definition `projection`. -/
def projection (a b : R) : R := a * b

/-- Theorem `projection_is_idempotent`. -/
theorem projection_is_idempotent (h : IsDrazinInverse a b k) : 
    (projection a b) * (projection a b) = projection a b := by
  unfold projection
  rw [mul_assoc, ← mul_assoc b a b, h.idempotent]

/-- Theorem `projection_comm`. -/
theorem projection_comm (h : IsDrazinInverse a b k) : 
    (projection a b) * b = b * (projection a b) := by
  unfold projection
  calc
    (a * b) * b = (b * a) * b := by rw [h.comm]
    _ = b * (a * b) := by rw [mul_assoc]

/-- Theorem `power_le`. -/
theorem power_le (h : IsDrazinInverse a b k) {m : ℕ} (hm : k ≤ m) : 
    a^(m + 1) * b = a^m := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm
  calc
    a^(k + t + 1) * b = a^(t + (k + 1)) * b := by
      simp [Nat.add_assoc, Nat.add_left_comm]
    _ = (a^t * a^(k + 1)) * b := by rw [pow_add]
    _ = a^t * (a^(k + 1) * b) := by rw [mul_assoc]
    _ = a^t * a^k := by rw [h.power]
    _ = a^(t + k) := by rw [← pow_add]
    _ = a^(k + t) := by simp [Nat.add_comm]

/-- Lemma `inverse_eq_pow_mul_pow`. -/
lemma inverse_eq_pow_mul_pow (h : IsDrazinInverse a b k) (n : ℕ) :
    b = b^(n + 1) * a^n := by
  have hba : Commute b a := h.comm.symm
  have hbase : b * b * a = b := by
    calc
      b * b * a = b * (b * a) := by rw [mul_assoc]
      _ = b * (a * b) := by rw [h.comm.symm]
      _ = (b * a) * b := by rw [← mul_assoc]
      _ = b := h.idempotent
  have hpow : ∀ n : ℕ, b^(n + 1) * a^n = b := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          b^(n + 2) * a^(n + 1)
              = (b^(n + 1) * b) * (a^n * a) := by simp [pow_succ]
          _ = b^(n + 1) * (b * a^n) * a := by simp [mul_assoc]
          _ = b^(n + 1) * (a^n * b) * a := by rw [(hba.pow_right n).eq]
          _ = (b^(n + 1) * a^n) * b * a := by simp [mul_assoc]
          _ = b * b * a := by rw [ih]
          _ = b := hbase
  exact (hpow n).symm

/-- Definition `core`. -/
def core (a b : R) : R := a * a * b
/-- Definition `nilpotent`. -/
def nilpotent (a b : R) : R := a - (core a b)

/-- Theorem `nilpotent_comm_self`. -/
theorem nilpotent_comm_self (h : IsDrazinInverse a b k) :
    a * (nilpotent a b) = (nilpotent a b) * a := by
  have hcore : a * core a b = core a b * a := by
    unfold core
    calc
      a * (a * a * b) = a * a * (a * b) := by simp [mul_assoc]
      _ = a * a * (b * a) := by rw [h.comm]
      _ = (a * a * b) * a := by simp [mul_assoc]
  unfold nilpotent
  calc
    a * (a - core a b) = a * a - a * core a b := by rw [mul_sub]
    _ = a * a - core a b * a := by rw [hcore]
    _ = (a - core a b) * a := by rw [sub_mul]

/-- Theorem `fitting_decomposition`. -/
theorem fitting_decomposition (_h : IsDrazinInverse a b k) :
    a = (core a b) + (nilpotent a b) := by
  have hrhs : core a b + nilpotent a b = a := by
    unfold core nilpotent
    calc
      a * a * b + (a - (a * a * b))
          = a * a * b + (a + -(a * a * b)) := by rw [sub_eq_add_neg]
      _ = a + (a * a * b + -(a * a * b)) := by
            simp [add_left_comm]
      _ = a := by simp
  exact hrhs.symm

end IsDrazinInverse
end InfoGeometry.Canonical.Drazin
