/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceParityClosure
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Singular.MetricAlgebraicProjectionDefect

/-!
# Native Drazin parity and directed projection defects

Uncompiled scratch adaptation of upstream/feat/cartan-drazin-mp-cycle,
6a2dd21237e949f8fb8ffc75bf90e996e0cb65c2, Canonical/DrazinMPCartan.
Uses native evenPart/oddPart/grading and commutatorDefect; no new carrier.
Write P = projection a d, L = a*m, R = m*a. The parity statements allow
arbitrary m: L and R are not claimed to be MP projections without a witness.
The directed commutators are [P,L] and [P,R]; projectionDefect uses [L,P].
All parity statements hold in an arbitrary ring, without division by two.
-/

namespace InfoGeometry.Canonical.DrazinPeirceParityCandidate

open InfoGeometry.Algebra.PeirceDeWittChiralSplit
open InfoGeometry.Singular.MetricAlgebraicProjectionDefect
open Drazin Drazin.IsDrazinInverse

variable {A : Type*} [Ring A]

/-- Recover the even part from the native odd-zero centralizer criterion. -/
theorem evenPart_eq_self_of_commute {p x : A} (hp : IsIdempotent p)
    (hx : p * x = x * p) : evenPart p x = x := by
  have ho := (oddPart_zero_iff_commute hp x).2 hx
  have hs := peirce_even_odd_decomposition p x
  rw [ho, add_zero] at hs
  exact hs.symm

/-- An idempotent's ordinary commutator is itself in its odd Peirce part. -/
theorem commutatorDefect_is_odd {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p (commutatorDefect p x) = commutatorDefect p x := by
  rw [oddPart_eq_double_commutator hp]
  have hp' : p * p = p := hp
  unfold commutatorDefect
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

/-- The spectral projector commutes with the actual Fitting nilpotent part. -/
theorem projection_comm_fittingNilpotentPart {a d : A} {k : ℕ}
    (h : IsDrazinInverse a d k) :
    projection a d * fittingNilpotentPart a d =
      fittingNilpotentPart a d * projection a d := by
  unfold fittingNilpotentPart
  calc
    projection a d * (a * complementaryProjection a d) =
        a * (projection a d * complementaryProjection a d) := by
      rw [← mul_assoc, projection_comm_self h, mul_assoc]
    _ = 0 := by rw [projection_mul_complementaryProjection h, mul_zero]
    _ = (a * complementaryProjection a d) * projection a d := by
      rw [mul_assoc, complementaryProjection_mul_projection h, mul_zero]

theorem operator_even {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) :
    evenPart (projection a d) a = a :=
  evenPart_eq_self_of_commute (projection_is_idempotent h) (projection_comm_self h)

theorem operator_odd_zero {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) :
    oddPart (projection a d) a = 0 :=
  (oddPart_zero_iff_commute (projection_is_idempotent h) a).2 (projection_comm_self h)

theorem inverse_even {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) :
    evenPart (projection a d) d = d :=
  evenPart_eq_self_of_commute (projection_is_idempotent h) (projection_comm h)

theorem inverse_odd_zero {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) :
    oddPart (projection a d) d = 0 :=
  (oddPart_zero_iff_commute (projection_is_idempotent h) d).2 (projection_comm h)

theorem fittingNilpotentPart_even {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) :
    evenPart (projection a d) (fittingNilpotentPart a d) = fittingNilpotentPart a d :=
  evenPart_eq_self_of_commute (projection_is_idempotent h)
    (projection_comm_fittingNilpotentPart h)

theorem fittingNilpotentPart_odd_zero {a d : A} {k : ℕ}
    (h : IsDrazinInverse a d k) :
    oddPart (projection a d) (fittingNilpotentPart a d) = 0 :=
  (oddPart_zero_iff_commute (projection_is_idempotent h) _).2
    (projection_comm_fittingNilpotentPart h)

/-- Spectral-first left defect is odd, for arbitrary m. -/
theorem left_defect_odd {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) (m : A) :
    oddPart (projection a d) (commutatorDefect (projection a d) (a * m)) =
      commutatorDefect (projection a d) (a * m) :=
  commutatorDefect_is_odd (projection_is_idempotent h) (a * m)

/-- Spectral-first right defect is odd, for arbitrary m. -/
theorem right_defect_odd {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) (m : A) :
    oddPart (projection a d) (commutatorDefect (projection a d) (m * a)) =
      commutatorDefect (projection a d) (m * a) :=
  commutatorDefect_is_odd (projection_is_idempotent h) (m * a)

theorem left_oddPart_recovery {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) (m : A) :
    oddPart (projection a d) (a * m) =
      grading (projection a d) * commutatorDefect (projection a d) (a * m) :=
  oddPart_eq_grading_mul_commutator (projection_is_idempotent h) (a * m)

theorem right_oddPart_recovery {a d : A} {k : ℕ} (h : IsDrazinInverse a d k) (m : A) :
    oddPart (projection a d) (m * a) =
      grading (projection a d) * commutatorDefect (projection a d) (m * a) :=
  oddPart_eq_grading_mul_commutator (projection_is_idempotent h) (m * a)

/-- The support-order difference uses right defect minus left defect. -/
theorem difference_oddPart_recovery {a d : A} {k : ℕ}
    (h : IsDrazinInverse a d k) (m : A) :
    oddPart (projection a d) (m * a - a * m) = grading (projection a d) *
      (commutatorDefect (projection a d) (m * a) -
        commutatorDefect (projection a d) (a * m)) := by
  rw [oddPart_eq_grading_mul_commutator (projection_is_idempotent h)]
  unfold commutatorDefect
  noncomm_ring

/-- Doubling, not division by two; even a Drazin witness is unnecessary here. -/
theorem grading_commutator_difference (a d m : A) :
    commutatorDefect (grading (projection a d)) (m * a - a * m) =
      (2 : ℕ) • (commutatorDefect (projection a d) (m * a) -
        commutatorDefect (projection a d) (a * m)) := by
  simp only [commutatorDefect, grading, compIdempotent, two_nsmul]
  noncomm_ring

section MetricWitness

variable [StarRing A]

/-- The native metric defect has the opposite sign. Its own MP and singular
Drazin witnesses remain explicit; the earlier arbitrary-m results need neither
an MP witness nor star structure. -/
theorem left_defect_eq_neg_projectionDefect {a d m : A} {k : ℕ}
    (hMP : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse a m)
    (hD : InfoGeometry.Singular.Drazin.IsDrazinInverse a d k) :
    commutatorDefect (projection a d) (a * m) =
      -projectionDefect a m d k hMP hD := by
  change (a * d) * (a * m) - (a * m) * (a * d) =
    -((a * m) * (a * d) - (a * d) * (a * m))
  abel

end MetricWitness

end InfoGeometry.Canonical.DrazinPeirceParityCandidate
