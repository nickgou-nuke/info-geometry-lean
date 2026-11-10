/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus

/-!
# Exact sheet commutators and their finite recursive hierarchy

The iteration is native `Function.iterate` of the actual inner commutator.
All finite levels are proved by induction. Neither nonvanishing of the
quadratic defect nor physical time evolution is inferred from these formulas.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

section Algebra

variable {B : Type*} [Ring B] [Algebra ℝ B]

theorem comm_real_smul_right (X Y : B) (r : ℝ) :
    comm X (r • Y) = r • comm X Y := by
  simp only [comm, mul_smul_comm, smul_mul_assoc, smul_sub]

omit [Algebra ℝ B] in
theorem genJ_eq_zero_iff_genPhi (P : B) (hP : P * P = P) (A C : B) :
    genJ P A C = 0 ↔ genPhi P A C = 0 := by
  have hJ : invS P * genPhi P A C = genJ P A C := by peirce_nf hP
  have hΦ : invS P * genJ P A C = genPhi P A C := by peirce_nf hP
  constructor
  · intro h
    rw [← hΦ, h, mul_zero]
  · intro h
    rw [← hJ, h, mul_zero]

/-- A coefficient asymmetry acts nontrivially exactly on nonzero odd input. -/
theorem comm_twoSheet_phi_eq_zero_iff (P : B) (hP : P * P = P)
    (A C : B) (a b : ℝ) :
    comm (twoSheet P a b) (genPhi P A C) = 0 ↔
      a = b ∨ genPhi P A C = 0 := by
  rw [comm_twoSheet_phi P hP, smul_eq_zero, sub_eq_zero,
    genJ_eq_zero_iff_genPhi P hP]

/-- Every even iterate returns to the original odd operator. -/
theorem iterate_twoSheet_phi_even (P : B) (hP : P * P = P)
    (A C : B) (a b : ℝ) (n : ℕ) :
    (comm (twoSheet P a b))^[2 * n] (genPhi P A C) =
      (a - b) ^ (2 * n) • genPhi P A C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega,
      Function.iterate_add_apply, ih]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      comm_real_smul_right, comm_twoSheet_phi P hP,
      comm_twoSheet_current P hP, smul_smul]
    congr 1
    ring

/-- Every odd iterate changes from the sum to the directed current. -/
theorem iterate_twoSheet_phi_odd (P : B) (hP : P * P = P)
    (A C : B) (a b : ℝ) (n : ℕ) :
    (comm (twoSheet P a b))^[2 * n + 1] (genPhi P A C) =
      (a - b) ^ (2 * n + 1) • genJ P A C := by
  rw [Function.iterate_succ_apply', iterate_twoSheet_phi_even P hP,
    comm_real_smul_right, comm_twoSheet_phi P hP, smul_smul, pow_succ]

end Algebra

section FunctionalCalculus

variable {B : Type*} [CStarAlgebra B] {P : B}

/-- Exact action of the actual negative operator logarithm. -/
theorem comm_neg_log_twoSheet_phi (hP : IsStarProjection P)
    (A C : B) (p q : ℝ) :
    comm (-CFC.log (twoSheet P p q)) (genPhi P A C) =
      (-(Real.log p - Real.log q)) • genJ P A C := by
  rw [neg_log_twoSheet hP, comm_twoSheet_phi P hP.isIdempotentElem.eq]
  congr 1
  ring

/-- Equal positive weights or zero odd input are the exact stopped-action cases. -/
theorem comm_neg_log_twoSheet_phi_eq_zero_iff (hP : IsStarProjection P)
    (A C : B) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    comm (-CFC.log (twoSheet P p q)) (genPhi P A C) = 0 ↔
      p = q ∨ genPhi P A C = 0 := by
  rw [neg_log_twoSheet hP,
    comm_twoSheet_phi_eq_zero_iff P hP.isIdempotentElem.eq]
  have hlog : -Real.log p = -Real.log q ↔ p = q := by
    constructor
    · intro h
      exact Real.log_injOn_pos hp hq (neg_injective h)
    · rintro rfl
      rfl
  rw [hlog]

/-- Even recursive action of the native sheet surprisal. -/
theorem iterate_neg_log_twoSheet_phi_even (hP : IsStarProjection P)
    (A C : B) (p q : ℝ) (n : ℕ) :
    (comm (-CFC.log (twoSheet P p q)))^[2 * n] (genPhi P A C) =
      (Real.log p - Real.log q) ^ (2 * n) • genPhi P A C := by
  rw [neg_log_twoSheet hP, iterate_twoSheet_phi_even P hP.isIdempotentElem.eq]
  have hsign : -Real.log p - -Real.log q = -(Real.log p - Real.log q) := by ring
  simp only [hsign, pow_mul, neg_sq]

/-- Odd recursive action retains the orientation sign of the current. -/
theorem iterate_neg_log_twoSheet_phi_odd (hP : IsStarProjection P)
    (A C : B) (p q : ℝ) (n : ℕ) :
    (comm (-CFC.log (twoSheet P p q)))^[2 * n + 1] (genPhi P A C) =
      (-(Real.log p - Real.log q) ^ (2 * n + 1)) • genJ P A C := by
  rw [neg_log_twoSheet hP, iterate_twoSheet_phi_odd P hP.isIdempotentElem.eq]
  have hsign : -Real.log p - -Real.log q = -(Real.log p - Real.log q) := by ring
  have heven : (-(Real.log p - Real.log q)) ^ (2 * n) =
      (Real.log p - Real.log q) ^ (2 * n) := by
    simp only [pow_mul, neg_sq]
  rw [hsign, pow_succ, heven, mul_neg, ← pow_succ]

end FunctionalCalculus

end InfoGeometry.OperatorAlgebra.PeirceSpine
