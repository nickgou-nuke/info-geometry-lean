/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CornerCompressionTraceCounterexample

/-!
# Global criterion for cyclic compression

Contract: for an arbitrary finite square matrix algebra over a commutative
coefficient ring and an idempotent P, the functional X ↦ trace (P X P)
is cyclic on the entire algebra exactly when P commutes with every matrix.
No commutativity of the matrix algebra is assumed.
Dependency: trace-pairing nondegeneracy → fixed-factor criterion → global criterion.
-/

namespace InfoGeometry.Algebra.CornerCompressionTraceCounterexample

/-- Over any non-commutative ring `B` with cyclic additive trace `τ : B →+ M`,
if `P` is a central idempotent (`∀ Y : B, Y * P = P * Y`), then the compressed
trace `X ↦ τ (P * X * P)` is globally cyclic on `B`. -/
theorem compressed_cyclic_trace_globally_cyclic_of_central_ring
    {B M : Type*} [Ring B] [AddCommGroup M]
    (τ : B →+ M) (hcyc : ∀ a b : B, τ (a * b) = τ (b * a))
    (P : B) (hP : P * P = P) (hcentral : ∀ Y : B, Y * P = P * Y)
    (X Y : B) :
    τ (P * (X * Y) * P) = τ (P * (Y * X) * P) :=
  compressed_cyclic_trace_of_commutes_ring τ hcyc P X Y hP (hcentral Y)

variable {R ι : Type*} [CommRing R] [Fintype ι]

theorem compressed_trace_globally_cyclic_iff
    (P : Matrix ι ι R) (hP : P * P = P) :
    (∀ X Y : Matrix ι ι R,
      Matrix.trace (P * (X * Y) * P) = Matrix.trace (P * (Y * X) * P)) ↔
    ∀ Y : Matrix ι ι R, Y * P = P * Y := by
  constructor
  · intro h Y
    exact (compressed_trace_cyclic_iff_commutes P Y hP).mp (fun X => h X Y)
  · intro h X Y
    exact (compressed_trace_cyclic_iff_commutes P Y hP).mpr (h Y) X

end InfoGeometry.Algebra.CornerCompressionTraceCounterexample
