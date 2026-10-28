import InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
import InfoGeometry.OperatorAlgebra.LieJordanTraceDuality

/-!
# Peirce trace pairings without an unsupported metric identification

The ordinary bilinear trace pairs opposite off-diagonal corners. Weighting by
`p - (1-p)` reverses one of those two terms. The weighted form is symmetric
on the existing even part and skew on the existing odd part. In general it
is not a symmetric metric on the whole matrix algebra.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceTracePairing

open Matrix LieJordanTraceDuality
open InfoGeometry.Algebra.PeirceDeWittChiralSplit

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Cyclic trace removes the two repeated endpoint projectors. -/
theorem trace_sandwich_product {p q : Matrix n n R}
    (hp : p * p = p) (hq : q * q = q) (X Y : Matrix n n R) :
    trace ((p * X * q) * (q * Y * p)) = trace (p * X * q * Y) := by
  calc
    _ = trace ((p * X * (q * q) * Y) * p) := by
      congr 1
      noncomm_ring
    _ = trace (p * (p * X * (q * q) * Y)) := trace_mul_comm _ _
    _ = trace ((p * p) * X * (q * q) * Y) := by
      congr 1
      noncomm_ring
    _ = _ := by rw [hp, hq]

/-- Correct four-block decomposition: off-diagonal sectors pair oppositely. -/
theorem trace_peirce_split {p : Matrix n n R} (hp : p * p = p)
    (X Y : Matrix n n R) :
    trace (X * Y) =
      trace (peirce11 p X * peirce11 p Y) +
      trace (peirce00 p X * peirce00 p Y) +
      trace (peirce10 p X * peirce01 p Y) +
      trace (peirce01 p X * peirce10 p Y) := by
  have hq : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  simp only [peirce11, peirce00, peirce10, peirce01]
  rw [trace_sandwich_product hp hp, trace_sandwich_product hq hq,
    trace_sandwich_product hp hq, trace_sandwich_product hq hp]
  rw [← trace_add, ← trace_add, ← trace_add]
  congr 1
  simp only [compIdempotent]
  noncomm_ring

/-- Signed four-block split. It is a weighted bilinear form, not a metric claim. -/
theorem weighted_peirce_split {p : Matrix n n R} (hp : p * p = p)
    (X Y : Matrix n n R) :
    trace (grading p * X * Y) =
      trace (peirce11 p X * peirce11 p Y) -
      trace (peirce00 p X * peirce00 p Y) +
      trace (peirce10 p X * peirce01 p Y) -
      trace (peirce01 p X * peirce10 p Y) := by
  have hq : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  simp only [peirce11, peirce00, peirce10, peirce01]
  rw [trace_sandwich_product hp hp, trace_sandwich_product hq hq,
    trace_sandwich_product hp hq, trace_sandwich_product hq hp]
  rw [← trace_sub, ← trace_add, ← trace_sub]
  congr 1
  simp only [grading, compIdempotent]
  noncomm_ring

/-- The grade-weighted trace is symmetric when its first input is even. -/
theorem weighted_even_symmetric {p : Matrix n n R} (hp : p * p = p)
    (X Y : Matrix n n R) :
    trace (grading p * evenPart p X * Y) = trace (grading p * Y * evenPart p X) := by
  have h := weighted_symmetry_defect (grading p) (evenPart p X) Y
  rw [grading_commutes_evenPart p hp X, sub_self, zero_mul, trace_zero] at h
  exact sub_eq_zero.mp h

/-- The grade-weighted trace is skew when its first input is odd. -/
theorem weighted_odd_skew {p : Matrix n n R} (hp : p * p = p)
    (X Y : Matrix n n R) :
    trace (grading p * oddPart p X * Y) = -trace (grading p * Y * oddPart p X) := by
  have h : grading p * oddPart p X = -(oddPart p X * grading p) :=
    eq_neg_of_add_eq_zero_left (grading_anticommutes_oddPart p hp X)
  rw [h, neg_mul, trace_neg, trace_cycle3 (oddPart p X) (grading p) Y,
    mul_assoc (grading p) Y (oddPart p X)]

/-- On a characteristic-zero coefficient field the odd restriction is alternating. -/
theorem weighted_odd_self (p X : Matrix n n ℚ) (hp : p * p = p) :
    trace (grading p * oddPart p X * oddPart p X) = 0 := by
  have h := weighted_odd_skew hp X (oddPart p X)
  linarith

end InfoGeometry.OperatorAlgebra.PeirceTracePairing
