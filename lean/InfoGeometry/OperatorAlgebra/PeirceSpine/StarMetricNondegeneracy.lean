/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Faithful star pairing of a square-zero Peirce channel

For a square-zero operator `N`, properness of the star pairing implies that
`N * star N + star N * N` vanishes exactly when `N` vanishes. The algebraic
proof needs neither an order nor a norm. Native C-star properness supplies a
specialization, while a star order separately supplies nonnegativity.

Nonvanishing of this Gram sum does not assert invertibility, a positive
uniform lower bound, or a physical spectral gap. For a general amplitude `A`,
the Peirce specialization detects the selected upper corner, not the whole
commutator `[P,A]`.
-/

set_option autoImplicit false

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy

section Ring

variable {B : Type*} [Ring B] [StarRing B]

/-- A proper star pairing detects a square-zero operator from its symmetric
Gram sum. Properness is the explicit implication used twice in the proof. -/
theorem sqZero_gramSum_eq_zero_iff {N : B} (hN : N * N = 0)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) :
    N * star N + star N * N = 0 ↔ N = 0 := by
  constructor
  · intro hV
    have hNs : star N * star N = 0 := by
      simpa only [star_mul, star_zero] using congrArg star hN
    have hSquare : star (N + star N) * (N + star N) = 0 := by
      simp only [star_add, star_star]
      calc
        (star N + N) * (N + star N) = N * star N + star N * N := by
          noncomm_ring [hN, hNs]
        _ = 0 := hV
    have hPhi : N + star N = 0 := hproper (N + star N) hSquare
    apply hproper N
    have hProd := congrArg (fun X : B => star N * X) hPhi
    simpa only [mul_add, hNs, add_zero, mul_zero] using hProd
  · rintro rfl
    simp

/-- Proper star pairing rules out zero coupling for a nonzero upper Peirce
channel. This statement is valid in an arbitrary noncommutative ring. -/
theorem genV_eq_zero_iff_conePlus_eq_zero {P : B}
    (hP : P * P = P) (hPs : star P = P)
    (hproper : ∀ X : B, star X * X = 0 → X = 0) (A : B) :
    genV P A (star A) = 0 ↔ conePlus P A = 0 := by
  unfold genV anticomm
  rw [← star_conePlus hPs A]
  exact sqZero_gramSum_eq_zero_iff (conePlus_mul_conePlus hP A A) hproper

end Ring

section Ordered

variable {B : Type*} [Ring B] [StarRing B] [PartialOrder B] [StarOrderedRing B]

/-- The star order makes the adjoint-paired Peirce coupling nonnegative.
Self-adjointness of `P` suffices here; idempotency is not needed. -/
theorem genV_nonneg {P : B} (hPs : star P = P) (A : B) :
    0 ≤ genV P A (star A) := by
  unfold genV anticomm
  rw [← star_conePlus hPs A]
  exact add_nonneg (mul_star_self_nonneg _) (star_mul_self_nonneg _)

end Ordered

section CStar

variable {B : Type*} [NormedRing B] [StarRing B] [CStarRing B]

/-- Native C-star properness discharges the algebraic faithfulness
hypothesis without finite-dimensionality or an order assumption. -/
theorem sqZero_gramSum_eq_zero_iff_cstar {N : B} (hN : N * N = 0) :
    N * star N + star N * N = 0 ↔ N = 0 :=
  sqZero_gramSum_eq_zero_iff hN
    (fun X h => (CStarRing.star_mul_self_eq_zero_iff X).mp h)

/-- The Peirce zero-coupling criterion in a native C-star ring. -/
theorem genV_eq_zero_iff_conePlus_eq_zero_cstar {P : B}
    (hP : P * P = P) (hPs : star P = P) (A : B) :
    genV P A (star A) = 0 ↔ conePlus P A = 0 :=
  genV_eq_zero_iff_conePlus_eq_zero hP hPs
    (fun X h => (CStarRing.star_mul_self_eq_zero_iff X).mp h) A

end CStar

end InfoGeometry.OperatorAlgebra.PeirceSpine.StarMetricNondegeneracy
