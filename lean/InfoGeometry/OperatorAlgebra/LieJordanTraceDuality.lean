/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanEndomorphisms
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Bilinear trace duality and the distinct sesquilinear statement

`trace (X * Y)` is the bilinear trace pairing. It is not the BKM metric and,
over complex matrices, is not the Hilbert--Schmidt inner product. The latter
uses `Xᴴ`; its duality theorem below has explicit skew-Hermitian/Hermitian
hypotheses. Neither theorem assumes `H * S = S * H`.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordan

open Matrix
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Skew-transpose identity for the bilinear trace pairing. -/
theorem trace_lie_skew (H X Y : Matrix n n R) :
    trace (lieOp R H X * Y) + trace (X * lieOp R H Y) = 0 := by
  simp only [lieOp_apply, sub_mul, mul_sub, trace_sub]
  have hcyc : trace (H * X * Y) = trace (X * (Y * H)) := by
    rw [mul_assoc, trace_mul_comm H (X * Y), mul_assoc]
  rw [hcyc, mul_assoc X H Y]
  abel

/-- Self-transpose identity for Jordan multiplication under the bilinear pairing. -/
theorem trace_jordan_symmetric (S X Y : Matrix n n R) :
    trace (jordanOp R S X * Y) = trace (X * jordanOp R S Y) := by
  simp only [jordanOp_apply, add_mul, mul_add, trace_add]
  have hcyc : trace (S * X * Y) = trace (X * (Y * S)) := by
    rw [mul_assoc, trace_mul_comm S (X * Y), mul_assoc]
  rw [hcyc, mul_assoc X S Y]
  abel

/-- The two algebraic operators are negative transposes for the trace pairing. -/
theorem trace_dual (H S X Y : Matrix n n R) :
    trace (plus R H S X * Y) + trace (X * minus R H S Y) = 0 := by
  have hskew := trace_lie_skew H X Y
  have hsymm := trace_jordan_symmetric S X Y
  change trace ((lieOp R H X + jordanOp R S X) * Y) +
    trace (X * (lieOp R H Y - jordanOp R S Y)) = 0
  rw [add_mul, mul_sub, trace_add, trace_sub, ← hsymm]
  calc
    (trace (lieOp R H X * Y) + trace (jordanOp R S X * Y)) +
        (trace (X * lieOp R H Y) - trace (jordanOp R S X * Y)) =
      trace (lieOp R H X * Y) + trace (X * lieOp R H Y) := by abel
    _ = 0 := hskew

/-- The metric defect of the plus operator is exactly the Jordan contribution. -/
theorem trace_plus_defect (H S X Y : Matrix n n R) :
    trace (plus R H S X * Y) + trace (X * plus R H S Y) =
      trace (jordanOp R S X * Y) + trace (jordanOp R S X * Y) := by
  have hskew := trace_lie_skew H X Y
  have hsymm := trace_jordan_symmetric S X Y
  change trace ((lieOp R H X + jordanOp R S X) * Y) +
    trace (X * (lieOp R H Y + jordanOp R S Y)) = _
  rw [add_mul, mul_add, trace_add, trace_add, ← hsymm]
  calc
    (trace (lieOp R H X * Y) + trace (jordanOp R S X * Y)) +
        (trace (X * lieOp R H Y) + trace (jordanOp R S X * Y)) =
      (trace (lieOp R H X * Y) + trace (X * lieOp R H Y)) +
        (trace (jordanOp R S X * Y) + trace (jordanOp R S X * Y)) := by abel
    _ = _ := by rw [hskew, zero_add]

theorem trace_plus (H S X : Matrix n n R) :
    trace (plus R H S X) = trace (S * X) + trace (S * X) := by
  simp only [plus_apply, trace_add, trace_sub]
  rw [trace_mul_comm X H, trace_mul_comm X S]
  abel

theorem trace_minus (H S X : Matrix n n R) :
    trace (minus R H S X) = -(trace (S * X) + trace (S * X)) := by
  simp only [minus_apply, trace_sub, trace_add]
  rw [trace_mul_comm X H, trace_mul_comm X S]
  abel

/-- The cubic trace expression is symmetric in its first two arguments. -/
theorem cubic_swap_first (S X Y : Matrix n n R) :
    trace (jordanOp R S X * Y) = trace (jordanOp R X S * Y) := by
  simp only [jordanOp_apply, add_comm]

/-- Cyclicity supplies the other generating transposition of the cubic form. -/
theorem cubic_swap_last (S X Y : Matrix n n R) :
    trace (jordanOp R S X * Y) = trace (jordanOp R S Y * X) := by
  rw [trace_jordan_symmetric, trace_mul_comm]

section Star

variable [StarRing R]

/-- The plus action preserves conjugate transpose with the correct hypotheses. -/
theorem plus_conjTranspose {H S : Matrix n n R}
    (hH : Hᴴ = -H) (hS : Sᴴ = S) (X : Matrix n n R) :
    (plus R H S X)ᴴ = plus R H S Xᴴ := by
  simp only [plus_apply, conjTranspose_add, conjTranspose_sub,
    conjTranspose_mul, hH, hS]
  noncomm_ring

/-- Sesquilinear duality is a separate theorem, not a reinterpretation of `trace_dual`. -/
theorem trace_star_dual {H S : Matrix n n R}
    (hH : Hᴴ = -H) (hS : Sᴴ = S) (X Y : Matrix n n R) :
    trace ((plus R H S X)ᴴ * Y) + trace (Xᴴ * minus R H S Y) = 0 := by
  rw [plus_conjTranspose hH hS]
  exact trace_dual H S Xᴴ Y

/-- The exact square-energy identity retains the noncommuting mixed term. -/
theorem trace_star_energy {H S : Matrix n n R}
    (hH : Hᴴ = -H) (hS : Sᴴ = S) (X : Matrix n n R) :
    trace (Xᴴ * (-minus R H S (plus R H S X))) =
      trace ((plus R H S X)ᴴ * plus R H S X) := by
  have h := trace_star_dual hH hS X (plus R H S X)
  rw [mul_neg, trace_neg]
  calc
    -trace (Xᴴ * minus R H S (plus R H S X)) =
      trace ((plus R H S X)ᴴ * plus R H S X) -
        (trace ((plus R H S X)ᴴ * plus R H S X) +
          trace (Xᴴ * minus R H S (plus R H S X))) := by abel
    _ = _ := by rw [h, sub_zero]

end Star
end InfoGeometry.OperatorAlgebra.LieJordan
