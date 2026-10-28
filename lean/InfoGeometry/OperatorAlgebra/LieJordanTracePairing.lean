/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceLieJordanResolution
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Cyclic trace duality and the Peirce weighted bilinear form

`tau (x*y)` is a bilinear trace pairing, not by definition a Hilbert--Schmidt
or Bogoliubov--Kubo--Mori metric. The weighted form has an exact symmetry
defect. Its odd restriction is skew, so no global symmetric metric or fixed
signature is inferred. The dual product identity needs no `[h,s] = 0` premise.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanTracePairing

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.JordanAssociator
open InfoGeometry.OperatorAlgebra.LieJordanDualTransport

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup G]

section Cyclic

variable (tau : A →+ G) (hcyc : ∀ x y : A, tau (x * y) = tau (y * x))
include hcyc

theorem jordan_trace_adjoint (s x y : A) :
    tau (jordanLeft (R := R) s x * y) = tau (x * jordanLeft (R := R) s y) := by
  change tau ((s * x + x * s) * y) = tau (x * (s * y + y * s))
  rw [add_mul, mul_add, map_add, map_add]
  have hc : tau (s * x * y) = tau (x * (y * s)) := by
    rw [mul_assoc, hcyc s (x * y), mul_assoc]
  rw [hc, mul_assoc x s y]
  abel

/-- Opposite Jordan perturbations are dual for the cyclic bilinear pairing. -/
theorem trace_dual (h s x y : A) :
    tau (plus (R := R) h s x * y) + tau (x * minus (R := R) h s y) = 0 := by
  change tau ((LieAlgebra.ad R A h x + jordanLeft (R := R) s x) * y) +
    tau (x * (LieAlgebra.ad R A h y - jordanLeft (R := R) s y)) = 0
  rw [add_mul, mul_sub, map_add, map_sub, ← jordan_trace_adjoint (R := R) tau hcyc s x y]
  calc
    _ = tau (x * (h * y - y * h)) + tau ((h * x - x * h) * y) := by
      change (tau ((h * x - x * h) * y) + tau ((s * x + x * s) * y)) +
        (tau (x * (h * y - y * h)) - tau ((s * x + x * s) * y)) = _
      abel
    _ = 0 := trace_adjoint_identity tau hcyc h x y

theorem trace_plus (h s x : A) :
    tau (plus (R := R) h s x) = 2 • tau (s * x) := by
  rw [plus_apply, map_add, trace_commutator tau hcyc,
    trace_symm tau hcyc, zero_add]

theorem trace_minus (h s x : A) :
    tau (minus (R := R) h s x) = -(2 • tau (s * x)) := by
  rw [minus_apply, map_sub, trace_commutator tau hcyc,
    trace_symm tau hcyc, zero_sub]

/-- Both order-sensitive products are formally symmetric; commutation of
`h` and `s` is not necessary for this bilinear adjoint statement. -/
theorem minus_plus_trace_symmetric (h s x y : A) :
    tau (minus (R := R) h s (plus (R := R) h s x) * y) =
      tau (x * minus (R := R) h s (plus (R := R) h s y)) := by
  have hl := trace_dual (R := R) tau hcyc h s y (plus (R := R) h s x)
  rw [hcyc (plus (R := R) h s y) (plus (R := R) h s x),
    hcyc y (minus (R := R) h s (plus (R := R) h s x))] at hl
  have hr := trace_dual (R := R) tau hcyc h s x (plus (R := R) h s y)
  exact add_left_cancel (hl.trans hr.symm)

/-- The exact negative-square pairing, with no positivity interpretation. -/
theorem minus_plus_trace_factor (h s x y : A) :
    tau (minus (R := R) h s (plus (R := R) h s x) * y) =
      -tau (plus (R := R) h s x * plus (R := R) h s y) := by
  have hz := trace_dual (R := R) tau hcyc h s y (plus (R := R) h s x)
  rw [hcyc (plus (R := R) h s y) (plus (R := R) h s x),
    hcyc y (minus (R := R) h s (plus (R := R) h s x))] at hz
  calc
    _ = (tau (plus (R := R) h s x * plus (R := R) h s y) +
          tau (minus (R := R) h s (plus (R := R) h s x) * y)) -
          tau (plus (R := R) h s x * plus (R := R) h s y) := by abel
    _ = _ := by rw [hz, zero_sub]

/-- Exact obstruction to symmetry of a weighted bilinear trace pairing. -/
theorem weighted_symmetry_defect (w x y : A) :
    tau (w * x * y) - tau (w * y * x) = tau ((w * x - x * w) * y) := by
  have hc : tau (w * y * x) = tau (x * w * y) := by
    rw [hcyc (w * y) x, ← mul_assoc]
  rw [hc, ← map_sub]
  congr 1
  noncomm_ring

theorem weighted_symmetric_of_commute (w x y : A) (hx : w * x = x * w) :
    tau (w * x * y) = tau (w * y * x) := by
  apply sub_eq_zero.mp
  rw [weighted_symmetry_defect tau hcyc, hx, sub_self, zero_mul, map_zero]

theorem weighted_skew_of_anticommute (w x y : A) (hx : w * x + x * w = 0) :
    tau (w * x * y) + tau (w * y * x) = 0 := by
  have hc : tau (w * y * x) = tau (x * w * y) := by
    rw [hcyc (w * y) x, ← mul_assoc]
  rw [hc, ← map_add, ← add_mul, hx, zero_mul, map_zero]

/-- Removing repeated endpoints in a paired pair of corners uses cyclicity. -/
theorem trace_corner_pair {p q : A} (hp : p * p = p) (hq : q * q = q) (x y : A) :
    tau ((p * x * q) * (q * y * p)) = tau (p * x * q * y) := by
  calc
    _ = tau ((p * x * (q * q) * y) * p) := by
      congr 1
      simp only [mul_assoc]
    _ = tau (p * (p * x * (q * q) * y)) := hcyc _ _
    _ = tau ((p * p) * x * (q * q) * y) := by
      congr 1
      simp only [mul_assoc]
    _ = _ := by rw [hp, hq]

/-- The ordinary trace pairs opposite off-diagonal corners. -/
theorem trace_peirce_split {p : A} (hp : p * p = p) (x y : A) :
    tau (x * y) = tau (peirce11 p x * peirce11 p y) +
      tau (peirce00 p x * peirce00 p y) +
      tau (peirce10 p x * peirce01 p y) + tau (peirce01 p x * peirce10 p y) := by
  have hq : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  have h11 := trace_corner_pair tau hcyc hp hp x y
  have h00 := trace_corner_pair tau hcyc hq hq x y
  have h10 := trace_corner_pair tau hcyc hp hq x y
  have h01 := trace_corner_pair tau hcyc hq hp x y
  change tau (x * y) = tau ((p * x * p) * (p * y * p)) +
    tau ((compIdempotent p * x * compIdempotent p) *
      (compIdempotent p * y * compIdempotent p)) +
    tau ((p * x * compIdempotent p) * (compIdempotent p * y * p)) +
    tau ((compIdempotent p * x * p) * (p * y * compIdempotent p))
  rw [h11, h00, h10, h01]
  calc
    _ = tau (p * x * p * y + compIdempotent p * x * compIdempotent p * y +
          p * x * compIdempotent p * y + compIdempotent p * x * p * y) := by
          congr 1
          unfold compIdempotent
          noncomm_ring
    _ = _ := by simp only [map_add]

/-- The signed four-corner expansion is not a claim of a symmetric metric. -/
theorem weighted_peirce_split {p : A} (hp : p * p = p) (x y : A) :
    tau ((p - compIdempotent p) * x * y) =
      tau (peirce11 p x * peirce11 p y) - tau (peirce00 p x * peirce00 p y) +
      tau (peirce10 p x * peirce01 p y) - tau (peirce01 p x * peirce10 p y) := by
  have hq : compIdempotent p * compIdempotent p = compIdempotent p :=
    compIdempotent_isIdempotent hp
  change tau ((p - compIdempotent p) * x * y) =
    tau ((p * x * p) * (p * y * p)) -
    tau ((compIdempotent p * x * compIdempotent p) *
      (compIdempotent p * y * compIdempotent p)) +
    tau ((p * x * compIdempotent p) * (compIdempotent p * y * p)) -
    tau ((compIdempotent p * x * p) * (p * y * compIdempotent p))
  rw [trace_corner_pair tau hcyc hp hp, trace_corner_pair tau hcyc hq hq,
    trace_corner_pair tau hcyc hp hq, trace_corner_pair tau hcyc hq hp]
  calc
    _ = tau (p * x * p * y - compIdempotent p * x * compIdempotent p * y +
          p * x * compIdempotent p * y - compIdempotent p * x * p * y) := by
          congr 1
          unfold compIdempotent
          noncomm_ring
    _ = _ := by simp only [map_add, map_sub]

end Cyclic

section Star

variable [StarRing A]

/-- The self-adjoint carrier is preserved with a skew-adjoint Lie generator
and self-adjoint Jordan generator. These hypotheses cannot be dropped. -/
theorem star_plus (h s x : A) (hh : star h = -h) (hs : star s = s) :
    star (plus (R := R) h s x) = plus (R := R) h s (star x) := by
  simp only [plus_apply, star_add, star_sub, star_mul, hh, hs]
  noncomm_ring

theorem trace_star_dual (tau : A →+ G)
    (hcyc : ∀ x y : A, tau (x * y) = tau (y * x))
    (h s x y : A) (hh : star h = -h) (hs : star s = s) :
    tau (star (plus (R := R) h s x) * y) +
      tau (star x * minus (R := R) h s y) = 0 := by
  rw [star_plus h s x hh hs]
  exact trace_dual (R := R) tau hcyc h s (star x) y

end Star

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Instantiation on full matrices, not a commuting subalgebra. -/
theorem matrix_trace_dual (h s x y : Matrix n n R) :
    Matrix.trace (plus (R := R) h s x * y) +
      Matrix.trace (x * minus (R := R) h s y) = 0 :=
  trace_dual (R := R) (Matrix.traceAddMonoidHom n R) Matrix.trace_mul_comm h s x y

end Matrix

end InfoGeometry.OperatorAlgebra.LieJordanTracePairing
