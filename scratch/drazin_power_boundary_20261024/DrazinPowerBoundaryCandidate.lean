/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DrazinJordanChevalleyBridge
import InfoGeometry.Core.NilpotentCartanRegression

/-!
# The missing power law for a commuting outer inverse

Contract: commutation and the outer-inverse law alone make `1-a*b` an
idempotent commuting with `a`; they do not make the residual nilpotent.
Residual nilpotence is exactly the missing existence of a Drazin index.
The regression uses the existing genuinely off-diagonal oblique matrix.

Reuse audit: DrazinCoreFlow and DrazinJordanChevalleyBridge already prove
residual power identities assuming all three Drazin laws. The weaker converse
was not found in the searched Canonical/Drazin*, Singular/Drazin*, nor in the
repository-wide residual-nilpotence/Drazin searches. Positive idempotent powers
reuse Singular.Drazin.pow_succ_eq_of_idempotent.
-/

namespace InfoGeometry.Canonical.Drazin

variable {R : Type*} [Ring R] {a b : R}

theorem outer_inverse_complement_idempotent (houter : b * a * b = b) :
    (1 - a * b) * (1 - a * b) = 1 - a * b := by
  have hp : (a * b) * (a * b) = a * b := by
    calc
      (a * b) * (a * b) = a * (b * a * b) := by noncomm_ring
      _ = a * b := by rw [houter]
  calc
    (1 - a * b) * (1 - a * b) = 1 - a * b - a * b + (a * b) * (a * b) := by
      noncomm_ring
    _ = 1 - a * b := by rw [hp]; abel

theorem commuting_outer_residual_pow_succ
    (hcomm : a * b = b * a) (houter : b * a * b = b) (n : ℕ) :
    (a * (1 - a * b)) ^ (n + 1) = a ^ (n + 1) * (1 - a * b) := by
  have hc : Commute a (1 - a * b) := by
    change a * (1 - a * b) = (1 - a * b) * a
    calc
      a * (1 - a * b) = a - a * (a * b) := by noncomm_ring
      _ = a - a * (b * a) := by rw [hcomm]
      _ = (1 - a * b) * a := by noncomm_ring
  rw [hc.mul_pow]
  rw [InfoGeometry.Singular.Drazin.pow_succ_eq_of_idempotent
    (outer_inverse_complement_idempotent houter) n]

theorem residual_isNilpotent_iff_exists_drazinIndex
    (hcomm : a * b = b * a) (houter : b * a * b = b) :
    IsNilpotent (a * (1 - a * b)) ↔ ∃ k, IsDrazinInverse a b k := by
  constructor
  · rintro ⟨n, hn⟩
    have hs : (a * (1 - a * b)) ^ (n + 1) = 0 := by
      rw [pow_succ, hn, zero_mul]
    rw [commuting_outer_residual_pow_succ hcomm houter n,
      mul_sub, mul_one, ← mul_assoc, ← pow_succ] at hs
    exact ⟨n + 1, hcomm, houter, (sub_eq_zero.mp hs).symm⟩
  · rintro ⟨k, h⟩
    exact ⟨k + 1,
      DrazinJordanChevalleyBridge.a_nilpotent_pow_succ_k h⟩

end InfoGeometry.Canonical.Drazin

namespace InfoGeometry.Core.NilpotentCartanRegression

theorem oblique_not_isNilpotent : ¬ IsNilpotent oblique := by
  have hp : oblique * oblique = oblique := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [oblique, Matrix.mul_apply, Fin.sum_univ_two]
  rintro ⟨n, hn⟩
  have hs : oblique ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  rw [InfoGeometry.Singular.Drazin.pow_succ_eq_of_idempotent hp n] at hs
  have he := congrArg (fun x : RationalMatrix => x 0 1) hs
  norm_num [oblique] at he

theorem oblique_zero_commutes : oblique * (0 : RationalMatrix) = 0 * oblique := by simp

theorem oblique_zero_outer_inverse : (0 : RationalMatrix) * oblique * 0 = 0 := by simp

theorem oblique_zero_residual_not_isNilpotent :
    ¬ IsNilpotent (oblique * (1 - oblique * (0 : RationalMatrix))) := by
  simpa using oblique_not_isNilpotent

end InfoGeometry.Core.NilpotentCartanRegression
