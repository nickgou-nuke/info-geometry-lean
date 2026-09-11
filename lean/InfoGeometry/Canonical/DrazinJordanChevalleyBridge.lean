import Mathlib.Tactic
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinSpectralFittingBridge

/-!
# Drazin Jordan-Chevalley Spectral Splitting Bridge

This module formalizes the universal Jordan-Chevalley / Fitting decomposition
derived unconditionally from the Drazin generalized inverse in arbitrary rings and modules:
1. `a_semisimple` and `a_nilpotent`: Canonical splitting `a = a_s + a_n` where
   `a_s = a * P = P * a` and `a_n = a * (1 - P) = (1 - P) * a`.
2. `jordan_chevalley_sum`: `a_s + a_n = a`.
3. `a_semisimple_mul_a_nilpotent` and `a_nilpotent_mul_a_semisimple`:
   Left and right mutual annihilation: `a_s * a_n = 0` and `a_n * a_s = 0`.
4. `jordan_chevalley_comm`: Commutation `[a_s, a_n] = 0`.
5. `a_comm_a_semisimple` and `a_comm_a_nilpotent`: Commutation with base element `[a, a_s] = 0` and `[a, a_n] = 0`.
6. `a_nilpotent_pow`: Power formula `(a_n)^m = a^m * (1 - P)` for all `m ≥ 1`.
7. `a_nilpotent_pow_k`: Exact nilpotency `(a_n)^k = 0` for `k ≥ 1`.
8. `a_nilpotent_pow_succ_k`: Universal nilpotency `(a_n)^(k + 1) = 0` for all `k ∈ ℕ`.
9. `a_semisimple_mul_drazin` and `drazin_mul_a_semisimple`:
   Regular sector inversion `a_s * b = P` and `b * a_s = P`.
10. Module state-level actions:
    `jordan_chevalley_smul_sum`, `a_semisimple_annihilates_nilpotent_state`,
    `a_nilpotent_annihilates_regular_state`, `a_nilpotent_pow_k_smul`, `a_nilpotent_pow_succ_k_smul`.
11. `CertifiedDrazinJordanChevalleySynthesis` & `master_drazin_jordan_chevalley_synthesis`.
-/

namespace InfoGeometry.Canonical.DrazinJordanChevalleyBridge

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Canonical.DrazinSpectralFittingBridge

variable {R : Type*} [Ring R] {a b : R} {k : ℕ}

/-- The regular / semisimple Jordan-Chevalley component: `a_s = a * P = P * a`. -/
def a_semisimple (a b : R) : R :=
  a * projection a b

/-- The nilpotent Jordan-Chevalley component: `a_n = a * (1 - P) = a - a_s`. -/
def a_nilpotent (a b : R) : R :=
  a * complementaryProjection a b

/-- Commutation of `a` with Drazin projection `P`. -/
theorem commute_a_projection (h : IsDrazinInverse a b k) :
    Commute a (projection a b) :=
  (projection_comm_self h).symm

/-- Commutation of `a` with complementary projection `Q = 1 - P`. -/
theorem commute_a_complementaryProjection (h : IsDrazinInverse a b k) :
    Commute a (complementaryProjection a b) :=
  (complementaryProjection_comm_self h).symm

/-- `projection a b * a = a * projection a b`. -/
theorem proj_mul_a (h : IsDrazinInverse a b k) :
    projection a b * a = a * projection a b :=
  projection_comm_self h

/-- `a_semisimple` equals `projection a b * a`. -/
theorem a_semisimple_eq_proj_mul (h : IsDrazinInverse a b k) :
    a_semisimple a b = projection a b * a := by
  dsimp [a_semisimple]
  rw [proj_mul_a h]

/-- `complementaryProjection a b * a = a * complementaryProjection a b`. -/
theorem comp_proj_mul_a (h : IsDrazinInverse a b k) :
    complementaryProjection a b * a = a * complementaryProjection a b :=
  complementaryProjection_comm_self h

/-- `a_nilpotent` equals `complementaryProjection a b * a`. -/
theorem a_nilpotent_eq_comp_proj_mul (h : IsDrazinInverse a b k) :
    a_nilpotent a b = complementaryProjection a b * a := by
  dsimp [a_nilpotent]
  rw [comp_proj_mul_a h]

/-- `a_nilpotent = a - a_semisimple`. -/
theorem a_nilpotent_eq_sub (a b : R) :
    a_nilpotent a b = a - a_semisimple a b := by
  dsimp [a_nilpotent, a_semisimple, complementaryProjection]
  rw [mul_sub, mul_one]

/-- **Theorem (Jordan-Chevalley Sum)**:
    `a_semisimple + a_nilpotent = a`. -/
theorem jordan_chevalley_sum (a b : R) :
    a_semisimple a b + a_nilpotent a b = a := by
  rw [a_nilpotent_eq_sub, add_sub_cancel]

/-- **Theorem (Left Mutual Annihilation)**:
    `a_s * a_n = 0`. -/
theorem a_semisimple_mul_a_nilpotent (h : IsDrazinInverse a b k) :
    a_semisimple a b * a_nilpotent a b = 0 := by
  rw [a_nilpotent_eq_comp_proj_mul h]
  dsimp [a_semisimple]
  calc (a * projection a b) * (complementaryProjection a b * a)
    _ = a * (projection a b * (complementaryProjection a b * a)) := by rw [mul_assoc]
    _ = a * ((projection a b * complementaryProjection a b) * a) := by rw [← mul_assoc (projection a b)]
    _ = a * (0 * a) := by rw [projection_mul_complementaryProjection h]
    _ = 0 := by simp

/-- **Theorem (Right Mutual Annihilation)**:
    `a_n * a_s = 0`. -/
theorem a_nilpotent_mul_a_semisimple (h : IsDrazinInverse a b k) :
    a_nilpotent a b * a_semisimple a b = 0 := by
  rw [a_semisimple_eq_proj_mul h]
  dsimp [a_nilpotent]
  calc (a * complementaryProjection a b) * (projection a b * a)
    _ = a * (complementaryProjection a b * (projection a b * a)) := by rw [mul_assoc]
    _ = a * ((complementaryProjection a b * projection a b) * a) := by rw [← mul_assoc (complementaryProjection a b)]
    _ = a * (0 * a) := by rw [complementaryProjection_mul_projection h]
    _ = 0 := by simp

/-- **Theorem (Jordan-Chevalley Commutativity)**:
    `[a_s, a_n] = 0`. -/
theorem jordan_chevalley_comm (h : IsDrazinInverse a b k) :
    Commute (a_semisimple a b) (a_nilpotent a b) := by
  have hl := a_semisimple_mul_a_nilpotent h
  have hr := a_nilpotent_mul_a_semisimple h
  exact hl.trans hr.symm

/-- Commutation with base element: `[a, a_s] = 0`. -/
theorem a_comm_a_semisimple (h : IsDrazinInverse a b k) :
    Commute a (a_semisimple a b) := by
  dsimp [a_semisimple]
  exact (Commute.refl a).mul_right (commute_a_projection h)

/-- Commutation with base element: `[a, a_n] = 0`. -/
theorem a_comm_a_nilpotent (h : IsDrazinInverse a b k) :
    Commute a (a_nilpotent a b) := by
  dsimp [a_nilpotent]
  exact (Commute.refl a).mul_right (commute_a_complementaryProjection h)

/-- Power formula for the nilpotent part: `(a_n)^m = a^m * (1 - P)` for all `m ≥ 1`. -/
theorem a_nilpotent_pow (h : IsDrazinInverse a b k) (m : ℕ) (hm : 1 ≤ m) :
    (a_nilpotent a b)^m = a^m * complementaryProjection a b := by
  rcases Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm) with ⟨n, rfl⟩
  clear hm
  induction n with
  | zero =>
    simp only [pow_one]
    rfl
  | succ n ih =>
    have h_pow_succ : (a_nilpotent a b)^(n + 2) = a_nilpotent a b * (a_nilpotent a b)^(n + 1) :=
      pow_succ' (a_nilpotent a b) (n + 1)
    have h_a_pow_succ : a^(n + 2) = a * a^(n + 1) := pow_succ' a (n + 1)
    have h_comm_pow : Commute (a^(n + 1)) (complementaryProjection a b) :=
      (commute_a_complementaryProjection h).pow_left (n + 1)
    have h_idem : complementaryProjection a b * complementaryProjection a b =
        complementaryProjection a b := complementaryProjection_is_idempotent h
    calc (a_nilpotent a b)^(n + 2)
      _ = a_nilpotent a b * (a_nilpotent a b)^(n + 1) := h_pow_succ
      _ = a_nilpotent a b * (a^(n + 1) * complementaryProjection a b) := by rw [ih]
      _ = (a * complementaryProjection a b) * (a^(n + 1) * complementaryProjection a b) := rfl
      _ = a * (complementaryProjection a b * (a^(n + 1) * complementaryProjection a b)) := by
        rw [mul_assoc]
      _ = a * ((complementaryProjection a b * a^(n + 1)) * complementaryProjection a b) := by
        rw [← mul_assoc (complementaryProjection a b) (a^(n + 1)) (complementaryProjection a b)]
      _ = a * ((a^(n + 1) * complementaryProjection a b) * complementaryProjection a b) := by
        rw [h_comm_pow.symm.eq]
      _ = a * (a^(n + 1) * (complementaryProjection a b * complementaryProjection a b)) := by
        rw [mul_assoc (a^(n + 1)) (complementaryProjection a b) (complementaryProjection a b)]
      _ = a * (a^(n + 1) * complementaryProjection a b) := by rw [h_idem]
      _ = (a * a^(n + 1)) * complementaryProjection a b := by rw [← mul_assoc a (a^(n + 1))]
      _ = a^(n + 2) * complementaryProjection a b := by rw [← h_a_pow_succ]

/-- **Theorem (Nilpotency of a_n for k ≥ 1)**:
    `(a_n)^k = 0`. -/
theorem a_nilpotent_pow_k (h : IsDrazinInverse a b k) (hk : 1 ≤ k) :
    (a_nilpotent a b)^k = 0 := by
  rw [a_nilpotent_pow h k hk]
  have h_comm_k : Commute (a^k) (complementaryProjection a b) :=
    (commute_a_complementaryProjection h).pow_left k
  calc a^k * complementaryProjection a b = complementaryProjection a b * a^k := h_comm_k.eq
    _ = 0 := complementaryProjection_mul_power_eq_zero h

/-- **Theorem (Universal Nilpotency of a_n for any k ∈ ℕ)**:
    `(a_n)^(k + 1) = 0`. -/
theorem a_nilpotent_pow_succ_k (h : IsDrazinInverse a b k) :
    (a_nilpotent a b)^(k + 1) = 0 := by
  have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  rw [a_nilpotent_pow h (k + 1) hk1]
  have h_split : a^(k + 1) = a * a^k := pow_succ' a k
  have h_comm_k : Commute (a^k) (complementaryProjection a b) :=
    (commute_a_complementaryProjection h).pow_left k
  calc a^(k + 1) * complementaryProjection a b
    _ = (a * a^k) * complementaryProjection a b := by rw [h_split]
    _ = a * (a^k * complementaryProjection a b) := by rw [mul_assoc]
    _ = a * (complementaryProjection a b * a^k) := by rw [h_comm_k.eq]
    _ = a * 0 := by rw [complementaryProjection_mul_power_eq_zero h]
    _ = 0 := mul_zero a

/-- **Theorem (Invertibility of a_s on regular sector)**:
    `a_s * b = P`. -/
theorem a_semisimple_mul_drazin (h : IsDrazinInverse a b k) :
    a_semisimple a b * b = projection a b := by
  rw [a_semisimple_eq_proj_mul h]
  dsimp [projection]
  calc (projection a b * a) * b = projection a b * (a * b) := by rw [mul_assoc]
    _ = projection a b * projection a b := rfl
    _ = projection a b := projection_is_idempotent h

/-- `b * a_s = P`. -/
theorem drazin_mul_a_semisimple (h : IsDrazinInverse a b k) :
    b * a_semisimple a b = projection a b := by
  dsimp [a_semisimple]
  calc b * (a * projection a b) = (b * a) * projection a b := by rw [← mul_assoc]
    _ = (a * b) * projection a b := by rw [h.comm]
    _ = projection a b * projection a b := rfl
    _ = projection a b := projection_is_idempotent h

/-! ## Module State Level -/

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- State action Jordan-Chevalley splitting: `a • v = a_s • v + a_n • v`. -/
theorem jordan_chevalley_smul_sum (v : M) :
    a_semisimple a b • v + a_nilpotent a b • v = a • v := by
  rw [← add_smul, jordan_chevalley_sum]

/-- Nilpotent sector annihilation: if `a^k • v = 0`, then `a_s • v = 0`. -/
theorem a_semisimple_annihilates_nilpotent_state
    (h : IsDrazinInverse a b k) (v : M) (h_ghost : (a^k) • v = 0) :
    a_semisimple a b • v = 0 := by
  dsimp [a_semisimple]
  calc (a * projection a b) • v = a • ((projection a b) • v) := mul_smul a _ v
    _ = a • ((a * b) • v) := rfl
    _ = a • (a • (b • v)) := by rw [mul_smul]
    _ = a • (a • (0 : M)) := by rw [drazin_annihilates_nilpotent h v h_ghost]
    _ = 0 := by simp

/-- Regular image annihilation: if `v = a^k • u`, then `a_n • v = 0`. -/
theorem a_nilpotent_annihilates_regular_state
    (h : IsDrazinInverse a b k) (v : M) (u : M) (h_im : v = (a^k) • u) :
    a_nilpotent a b • v = 0 := by
  dsimp [a_nilpotent]
  have h_comp_pow : complementaryProjection a b * a^k = 0 :=
    complementaryProjection_mul_power_eq_zero h
  rw [h_im]
  calc (a * complementaryProjection a b) • ((a^k) • u)
    _ = ((a * complementaryProjection a b) * a^k) • u := (mul_smul _ _ u).symm
    _ = (a * (complementaryProjection a b * a^k)) • u := by rw [mul_assoc]
    _ = (a * 0) • u := by rw [h_comp_pow]
    _ = (0 : R) • u := by rw [mul_zero]
    _ = 0 := zero_smul R u

/-- Nilpotency on module states: `(a_n^k) • v = 0` for `k ≥ 1`. -/
theorem a_nilpotent_pow_k_smul (h : IsDrazinInverse a b k) (hk : 1 ≤ k) (v : M) :
    ((a_nilpotent a b)^k) • v = 0 := by
  rw [a_nilpotent_pow_k h hk, zero_smul]

/-- Universal nilpotency on module states: `(a_n^(k+1)) • v = 0` for all `k ∈ ℕ`. -/
theorem a_nilpotent_pow_succ_k_smul (h : IsDrazinInverse a b k) (v : M) :
    ((a_nilpotent a b)^(k + 1)) • v = 0 := by
  rw [a_nilpotent_pow_succ_k h, zero_smul]

/-! ## Certified Synthesis Structure -/

/-- Certified Jordan-Chevalley Drazin Synthesis structure. -/
structure CertifiedDrazinJordanChevalleySynthesis (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] where
  sum_identity : ∀ (a b : R), a_semisimple a b + a_nilpotent a b = a
  left_annihilation : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → a_semisimple a b * a_nilpotent a b = 0
  right_annihilation : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → a_nilpotent a b * a_semisimple a b = 0
  commutation : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → Commute (a_semisimple a b) (a_nilpotent a b)
  nilpotent_pow_k : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → 1 ≤ k → (a_nilpotent a b)^k = 0
  nilpotent_pow_succ : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → (a_nilpotent a b)^(k + 1) = 0
  semisimple_inverted : ∀ (a b : R) (k : ℕ), IsDrazinInverse a b k → a_semisimple a b * b = projection a b
  state_sum : ∀ (a b : R) (v : M), a_semisimple a b • v + a_nilpotent a b • v = a • v
  ghost_annihilated : ∀ (a b : R) (k : ℕ) (v : M), IsDrazinInverse a b k → (a^k) • v = 0 → a_semisimple a b • v = 0
  regular_annihilated : ∀ (a b : R) (k : ℕ) (v u : M), IsDrazinInverse a b k → v = (a^k) • u → a_nilpotent a b • v = 0

/-- Master constructor for Certified Jordan-Chevalley Drazin Synthesis. -/
def makeCertifiedDrazinJordanChevalleySynthesis :
    CertifiedDrazinJordanChevalleySynthesis R M := {
  sum_identity := fun a b => jordan_chevalley_sum a b
  left_annihilation := fun _ _ _ h => a_semisimple_mul_a_nilpotent h
  right_annihilation := fun _ _ _ h => a_nilpotent_mul_a_semisimple h
  commutation := fun _ _ _ h => jordan_chevalley_comm h
  nilpotent_pow_k := fun _ _ _ h hk => a_nilpotent_pow_k h hk
  nilpotent_pow_succ := fun _ _ _ h => a_nilpotent_pow_succ_k h
  semisimple_inverted := fun _ _ _ h => a_semisimple_mul_drazin h
  state_sum := fun _ _ v => jordan_chevalley_smul_sum v
  ghost_annihilated := fun _ _ _ v h h_gh => a_semisimple_annihilates_nilpotent_state h v h_gh
  regular_annihilated := fun _ _ _ v u h h_im => a_nilpotent_annihilates_regular_state h v u h_im
}

/-- Master theorem synthesizing the complete Jordan-Chevalley decomposition from the Drazin inverse. -/
theorem master_drazin_jordan_chevalley_synthesis
    (h : IsDrazinInverse a b k) (hk : 1 ≤ k) (v : M) :
    (a_semisimple a b + a_nilpotent a b = a) ∧
    (a_semisimple a b * a_nilpotent a b = 0) ∧
    (a_nilpotent a b * a_semisimple a b = 0) ∧
    (Commute (a_semisimple a b) (a_nilpotent a b)) ∧
    ((a_nilpotent a b)^k = 0) ∧
    ((a_nilpotent a b)^(k + 1) = 0) ∧
    (a_semisimple a b * b = projection a b) ∧
    (b * a_semisimple a b = projection a b) ∧
    (a_semisimple a b • v + a_nilpotent a b • v = a • v) := ⟨
  jordan_chevalley_sum a b,
  a_semisimple_mul_a_nilpotent h,
  a_nilpotent_mul_a_semisimple h,
  jordan_chevalley_comm h,
  a_nilpotent_pow_k h hk,
  a_nilpotent_pow_succ_k h,
  a_semisimple_mul_drazin h,
  drazin_mul_a_semisimple h,
  jordan_chevalley_smul_sum v
⟩

end InfoGeometry.Canonical.DrazinJordanChevalleyBridge
