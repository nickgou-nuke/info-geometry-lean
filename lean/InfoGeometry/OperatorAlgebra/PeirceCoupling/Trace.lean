/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceCoupling.Algebra
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Cyclic trace and signed sector compressions of opposite Peirce products -/

namespace InfoGeometry.OperatorAlgebra.PeirceCoupling

open Matrix InfoGeometry.Core.PeirceDecomposition InfoGeometry.Core.PeirceGrading

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
variable {p : Matrix n n R} (hp : IsIdempotentElem p) (a b : Matrix n n R)

local notation "U" => component10 p a
local notation "V" => component01 p b

theorem opposite_lie_trace : trace ⁅U, V⁆ = 0 := by
  rw [Ring.lie_def, trace_sub, trace_mul_comm, sub_self]

theorem opposite_jordan_trace : trace (U * V + V * U) = 2 * trace (U * V) := by
  rw [trace_add, trace_mul_comm V U, two_mul]

include hp

/-- Weighting by the grading converts the cancelling trace into the Jordan trace. -/
theorem weighted_lie_trace :
    trace (reflection p * ⁅U, V⁆) = 2 * trace (U * V) := by
  rw [reflection_mul_lie hp a b, opposite_jordan_trace]

theorem jordan_sector_traces :
    trace (p * (U * V + V * U) * p) =
      trace ((1 - p) * (U * V + V * U) * (1 - p)) := by
  rw [upper_jordan_compression hp a b, lower_jordan_compression hp a b, trace_mul_comm]

theorem lie_sector_traces :
    trace (p * ⁅U, V⁆ * p) =
      -trace ((1 - p) * ⁅U, V⁆ * (1 - p)) := by
  rw [upper_lie_compression hp a b, lower_lie_compression hp a b,
    trace_neg, neg_neg, trace_mul_comm]

end InfoGeometry.OperatorAlgebra.PeirceCoupling
