/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Ring.CharZero

/-!
# Native trace of a product of anticommuting endomorphisms

The cyclic-trace argument works over any characteristic-zero field on a
finite-dimensional module. This generalizes the real-field theorem in
`DAGCellDoubledExterior3Bridge` without importing its DAG applications.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.TraceAnticommutation

theorem linearMap_trace_mul_zero_of_anticommute
    {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A B : Module.End K M)
    (h : A * B + B * A = 0) :
    LinearMap.trace K M (A * B) = 0 := by
  have htrace := congrArg (LinearMap.trace K M) h
  rw [map_add, map_zero, LinearMap.trace_mul_comm K B A] at htrace
  exact add_self_eq_zero.mp htrace

end InfoGeometry.LinearAlgebra.TraceAnticommutation
