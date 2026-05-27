import InfoGeometry.Canonical.Drazin
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinSum

Theorem-safe Drazin inverse readbacks for sums.

This file proves the finite algebraic orthogonal-sum case over an arbitrary
ring.  Banach-algebra generalized Drazin formulas involving quasinilpotents and
infinite series are exposed only as witness packets, because their correctness
requires analytic convergence/spectral hypotheses not present in `Ring`.
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinSum

open InfoGeometry.Canonical.Drazin

section Ring

variable {R : Type*} [Ring R]

/-- Orthogonality data sufficient to add two Drazin inverse pairs. -/
@[rep_depth operator]
structure DrazinPairOrthogonal (a ad b bd : R) where
  a_mul_b : a * b = 0
  b_mul_a : b * a = 0
  a_mul_bd : a * bd = 0
  bd_mul_a : bd * a = 0
  ad_mul_b : ad * b = 0
  b_mul_ad : b * ad = 0
  ad_mul_bd : ad * bd = 0
  bd_mul_ad : bd * ad = 0

namespace DrazinPairOrthogonal

variable {a ad b bd : R}
/-- The original summands are mutually orthogonal. -/
@[rep_depth operator]
theorem base_left (h : DrazinPairOrthogonal a ad b bd) : a * b = 0 :=
  DrazinPairOrthogonal.a_mul_b h

/-- The original summands are mutually orthogonal in the reverse order. -/
@[rep_depth operator]
theorem base_right (h : DrazinPairOrthogonal a ad b bd) : b * a = 0 :=
  DrazinPairOrthogonal.b_mul_a h

end DrazinPairOrthogonal

/-- If `a * b = 0`, then every positive power of `a` kills `b` on the right. -/
@[rep_depth operator]
theorem pow_succ_mul_eq_zero_of_mul_eq_zero
    {a b : R} (hab : a * b = 0) (n : ℕ) :
    a ^ (n + 1) * b = 0 := by
  induction n with
  | zero =>
      simpa using hab
  | succ n ih =>
      calc
        a ^ (Nat.succ n + 1) * b
            = (a ^ (n + 1) * a) * b := by
                rw [show Nat.succ n + 1 = n + 1 + 1 by omega]
                rw [pow_succ]
        _ = a ^ (n + 1) * (a * b) := by rw [mul_assoc]
        _ = 0 := by rw [hab, mul_zero]

/-- If `a * b = 0`, then `a` kills every positive power of `b` on the left. -/
@[rep_depth operator]
theorem mul_pow_succ_eq_zero_of_mul_eq_zero
    {a b : R} (hab : a * b = 0) (n : ℕ) :
    a * b ^ (n + 1) = 0 := by
  induction n with
  | zero =>
      simpa using hab
  | succ n ih =>
      calc
        a * b ^ (Nat.succ n + 1)
            = a * (b * b ^ (n + 1)) := by
                rw [show Nat.succ n + 1 = n + 1 + 1 by omega]
                rw [pow_succ']
        _ = (a * b) * b ^ (n + 1) := by rw [mul_assoc]
        _ = 0 := by rw [hab, zero_mul]

/-- Positive powers of orthogonal summands add without mixed terms. -/
@[rep_depth operator]
theorem orthogonal_add_pow_succ
    {a b : R} (hab : a * b = 0) (hba : b * a = 0) (n : ℕ) :
    (a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have haPow_b : a ^ (n + 1) * b = 0 :=
        pow_succ_mul_eq_zero_of_mul_eq_zero hab n
      have hbPow_a : b ^ (n + 1) * a = 0 :=
        pow_succ_mul_eq_zero_of_mul_eq_zero hba n
      calc
        (a + b) ^ (Nat.succ n + 1)
            = (a + b) ^ (n + 1) * (a + b) := by
                rw [show Nat.succ n + 1 = n + 1 + 1 by omega]
                rw [pow_succ]
        _ = (a ^ (n + 1) + b ^ (n + 1)) * (a + b) := by rw [ih]
        _ = a ^ (n + 1) * a + a ^ (n + 1) * b
              + (b ^ (n + 1) * a + b ^ (n + 1) * b) := by
                noncomm_ring
        _ = a ^ (n + 1) * a + 0 + (0 + b ^ (n + 1) * b) := by
                rw [haPow_b, hbPow_a]
        _ = a ^ (n + 2) + b ^ (n + 2) := by
                rw [show n + 2 = n + 1 + 1 by omega]
                rw [pow_succ, pow_succ]
                noncomm_ring

/--
Koliha-style algebraic orthogonal sum formula with a common Drazin index.

If `ad` is a Drazin inverse of `a`, `bd` is a Drazin inverse of `b`, and the two
Drazin pairs are mutually orthogonal, then `ad + bd` is a Drazin inverse of
`a + b`.  The index is shifted to `k + 1` to avoid the degenerate zero-power
case while retaining a finite algebraic statement.
-/
@[rep_depth operator]
theorem orthogonal_sum_isDrazinInverse
    {a ad b bd : R} {k : ℕ}
    (ha : IsDrazinInverse a ad k)
    (hb : IsDrazinInverse b bd k)
    (horth : DrazinPairOrthogonal a ad b bd) :
    IsDrazinInverse (a + b) (ad + bd) (k + 1) := by
  refine IsDrazinInverse.mk ?comm ?idem ?power
  · calc
      (a + b) * (ad + bd)
          = a * ad + a * bd + (b * ad + b * bd) := by noncomm_ring
      _ = a * ad + 0 + (0 + b * bd) := by rw [horth.a_mul_bd, horth.b_mul_ad]
      _ = ad * a + 0 + (0 + bd * b) := by rw [ha.comm, hb.comm]
      _ = ad * a + ad * b + (bd * a + bd * b) := by
            rw [horth.ad_mul_b, horth.bd_mul_a]
      _ = (ad + bd) * (a + b) := by noncomm_ring
  · calc
      (ad + bd) * (a + b) * (ad + bd)
          = ad * a * ad + ad * a * bd + ad * b * ad + ad * b * bd
              + (bd * a * ad + bd * a * bd + bd * b * ad + bd * b * bd) := by
              noncomm_ring
      _ = ad * a * ad + bd * b * bd := by
              noncomm_ring [horth.a_mul_bd, horth.ad_mul_b, horth.b_mul_ad,
                horth.bd_mul_a, horth.bd_mul_ad, horth.ad_mul_bd]
      _ = ad + bd := by rw [ha.idempotent, hb.idempotent]
  · have hpowA : a ^ ((k + 1) + 1) * ad = a ^ (k + 1) := by
      simpa [Nat.add_assoc] using IsDrazinInverse.power_le ha (Nat.le_succ k)
    have hpowB : b ^ ((k + 1) + 1) * bd = b ^ (k + 1) := by
      simpa [Nat.add_assoc] using IsDrazinInverse.power_le hb (Nat.le_succ k)
    have hsumLow :
        (a + b) ^ ((k + 1) + 1)
          = a ^ ((k + 1) + 1) + b ^ ((k + 1) + 1) := by
      simpa [Nat.add_assoc] using
        orthogonal_add_pow_succ horth.a_mul_b horth.b_mul_a (k + 1)
    calc
      (a + b) ^ ((k + 1) + 1) * (ad + bd)
          = (a ^ ((k + 1) + 1) + b ^ ((k + 1) + 1)) * (ad + bd) := by
              rw [hsumLow]
      _ = a ^ ((k + 1) + 1) * ad + a ^ ((k + 1) + 1) * bd
            + (b ^ ((k + 1) + 1) * ad + b ^ ((k + 1) + 1) * bd) := by
              noncomm_ring
      _ = a ^ ((k + 1) + 1) * ad + 0 + (0 + b ^ ((k + 1) + 1) * bd) := by
              have ha_bd : a ^ ((k + 1) + 1) * bd = 0 :=
                pow_succ_mul_eq_zero_of_mul_eq_zero horth.a_mul_bd (k + 1)
              have hb_ad : b ^ ((k + 1) + 1) * ad = 0 :=
                pow_succ_mul_eq_zero_of_mul_eq_zero horth.b_mul_ad (k + 1)
              rw [ha_bd, hb_ad]
      _ = a ^ (k + 2) * ad + b ^ (k + 2) * bd := by simp
      _ = a ^ (k + 1) + b ^ (k + 1) := by
              simpa [Nat.add_assoc] using congrArg₂ HAdd.hAdd hpowA hpowB
      _ = (a + b) ^ (k + 1) := by
              symm
              simpa [Nat.add_assoc] using
                orthogonal_add_pow_succ horth.a_mul_b horth.b_mul_a k

/-- Readback formula: in the orthogonal finite case, the Drazin inverse candidate is additive. -/
@[rep_depth operator]
theorem orthogonal_sum_drazin_candidate_eq
    {a ad b bd : R} {k : ℕ}
    (ha : IsDrazinInverse a ad k)
    (hb : IsDrazinInverse b bd k)
    (horth : DrazinPairOrthogonal a ad b bd) :
    IsDrazinInverse (a + b) (ad + bd) (k + 1) :=
  orthogonal_sum_isDrazinInverse ha hb horth

end Ring

/--
Witness packet for Banach/generalized-Drazin sum formulas.

This deliberately does not live as a `Ring` theorem: quasinilpotence, spectral
idempotents, and infinite series need analytic convergence and Banach-algebra
hypotheses.
-/
@[rep_depth operator]
structure GeneralizedDrazinBanachSumFormula
    (Alg : Type*) where
  a : Alg
  b : Alg
  ad : Alg
  bd : Alg
  spectralIdempotentA : Alg
  spectralIdempotentB : Alg
  candidate : Alg
  hypotheses : Prop
  convergenceWitness : Prop
  generalizedDrazinInverseWitness : Prop

namespace GeneralizedDrazinBanachSumFormula

variable {Alg : Type*}
variable (F : GeneralizedDrazinBanachSumFormula Alg)

end GeneralizedDrazinBanachSumFormula

/-- Pierce/Koliha block decomposition packet for computing generalized Drazin inverses. -/
@[rep_depth operator]
structure KolihaPierceDrazinBlockPacket
    (Alg Block11 Block12 Block21 Block22 : Type*) where
  a : Alg
  ad : Alg
  projector : Alg
  regularBlock : Block11
  upperRightBlock : Block12
  lowerLeftBlock : Block21
  singularBlock : Block22
  regularBlockInvertibleWitness : Prop
  singularBlockQuasinilpotentWitness : Prop
  blockFormulaWitness : Prop

namespace KolihaPierceDrazinBlockPacket

variable {Alg Block11 Block12 Block21 Block22 : Type*}
variable (P : KolihaPierceDrazinBlockPacket Alg Block11 Block12 Block21 Block22)

end KolihaPierceDrazinBlockPacket

end InfoGeometry.Canonical.DrazinSum
