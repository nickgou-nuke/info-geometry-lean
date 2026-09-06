import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture
import InfoGeometry.Singular.Drazin

namespace InfoGeometry.Canonical.Drazin

/-- Predicate encoding the Drazin inverse laws. -/
@[rep_depth krein]
def IsDrazinInverse {R : Type*} [Ring R] (a b : R) (k : ℕ) : Prop :=
  a * b = b * a ∧ b * a * b = b ∧ a^(k + 1) * b = a^k

namespace IsDrazinInverse

variable {R : Type*} [Ring R] {a b c : R} {k : ℕ}

/-- Constructor for the Drazin laws predicate. -/
@[rep_depth krein]
theorem mk
    (hcomm : a * b = b * a)
    (hidempotent : b * a * b = b)
    (hpower : a^(k + 1) * b = a^k) :
    IsDrazinInverse a b k :=
  ⟨hcomm, hidempotent, hpower⟩

/-- Commutation law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem comm (h : IsDrazinInverse a b k) : a * b = b * a := h.1

/-- Idempotent law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem idempotent (h : IsDrazinInverse a b k) : b * a * b = b := h.2.1

/-- Power law for a Drazin inverse witness. -/
@[rep_depth krein]
theorem power (h : IsDrazinInverse a b k) : a^(k + 1) * b = a^k := h.2.2

/-- Definition `projection`. -/
@[rep_depth krein]
def projection (a b : R) : R := a * b

/-- Complementary Drazin projector `Q = 1 - P`. -/
@[rep_depth krein]
def complementaryProjection (a b : R) : R := 1 - projection a b

/-- Theorem `projection_is_idempotent`. -/
@[rep_depth krein]
theorem projection_is_idempotent (h : IsDrazinInverse a b k) :
    (projection a b) * (projection a b) = projection a b := by
  unfold projection
  rw [mul_assoc, ← mul_assoc b a b, h.idempotent]

/-- The complementary Drazin projector is idempotent. -/
@[rep_depth krein]
theorem complementaryProjection_is_idempotent (h : IsDrazinInverse a b k) :
    (complementaryProjection a b) * (complementaryProjection a b) =
      complementaryProjection a b := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- The Drazin projector and its complement are left-orthogonal. -/
@[rep_depth krein]
theorem projection_mul_complementaryProjection (h : IsDrazinInverse a b k) :
    projection a b * complementaryProjection a b = 0 := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- The Drazin projector and its complement are right-orthogonal. -/
@[rep_depth krein]
theorem complementaryProjection_mul_projection (h : IsDrazinInverse a b k) :
    complementaryProjection a b * projection a b = 0 := by
  have hP : (projection a b) * (projection a b) = projection a b :=
    projection_is_idempotent h
  unfold complementaryProjection
  noncomm_ring [hP]

/-- Drazin projector decomposition of identity: `P + Q = 1`. -/
@[rep_depth krein]
theorem projection_add_complementaryProjection :
    projection a b + complementaryProjection a b = (1 : R) := by
  unfold complementaryProjection
  noncomm_ring

/-- Theorem `projection_comm`. -/
@[rep_depth krein]
theorem projection_comm (h : IsDrazinInverse a b k) :
    (projection a b) * b = b * (projection a b) := by
  unfold projection
  calc
    (a * b) * b = (b * a) * b := by rw [h.comm]
    _ = b * (a * b) := by rw [mul_assoc]

/-- Theorem `power_le`. -/
@[rep_depth krein]
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

/-- Transport a canonical Drazin witness to the singular Drazin API. -/
private theorem toSingular (h : IsDrazinInverse a b k) :
    InfoGeometry.Singular.Drazin.IsDrazinInverse a b k := by
  exact InfoGeometry.Singular.Drazin.IsDrazinInverse.mk
    h.idempotent h.comm h.power.symm

/-- Fixed-index uniqueness of the canonical Drazin inverse witness. -/
@[rep_depth krein]
theorem unique (hB : IsDrazinInverse a b k) (hC : IsDrazinInverse a c k) :
    b = c := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique (toSingular hB) (toSingular hC)

/--
Index-independent uniqueness of the canonical Drazin inverse witness.
-/
@[rep_depth krein]
theorem unique_of_indices {ℓ : ℕ}
    (hB : IsDrazinInverse a b k) (hC : IsDrazinInverse a c ℓ) :
    b = c := by
  exact InfoGeometry.Singular.Drazin.Drazin_unique_of_indices
    (toSingular hB) (toSingular hC)

/-- Lemma `inverse_eq_pow_mul_pow`. -/
@[rep_depth krein]
lemma inverse_eq_pow_mul_pow (h : IsDrazinInverse a b k) (n : ℕ) :
    b = b^(n + 1) * a^n := by
  have hba : Commute b a := by
    show b * a = a * b
    exact h.comm.symm
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
@[rep_depth krein]
def core (a b : R) : R := a * a * b
/-- Definition `nilpotent`. -/
@[rep_depth krein]
def nilpotent (a b : R) : R := a - (core a b)

/-- Theorem `nilpotent_comm_self`. -/
@[rep_depth krein]
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
@[rep_depth krein]
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
