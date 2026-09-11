import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFProjectionRankTailSystem

namespace InfoGeometry.Canonical

/-!
# Transporting one finite projection along an unanchored tail

Given an idempotent at an arbitrary finite anchor, this owner constructs its
entire coherent tail by repeatedly applying the existing binary transport.
It deliberately does not manufacture arbitrary-rank seed projections; those
remain a separate finite-stage construction problem.
-/

noncomputable def tailTransportStep
    (anchor n : ℕ)
    (p : IdempotentProjection ℝ (RealStageVector (anchor + n))) :
    IdempotentProjection ℝ (RealStageVector (anchor + (n + 1))) :=
  cast (by rw [Nat.add_assoc]) (nextStageProjectionData p)

noncomputable def transportedTailProjection
    (anchor : ℕ)
    (p : IdempotentProjection ℝ (RealStageVector anchor)) :
    ∀ n : ℕ, IdempotentProjection ℝ (RealStageVector (anchor + n))
  | 0 => p
  | n + 1 => tailTransportStep anchor n (transportedTailProjection anchor p n)

noncomputable def transportedTailSystem
    (anchor : ℕ)
  (p : IdempotentProjection ℝ (RealStageVector anchor)) :
    RealUHFProjectionRankTailSystem anchor where
  projection n := transportedTailProjection anchor p n
  coherent n := by
    change nextStageProjectionData
        (transportedTailProjection anchor p n) =
      transportedTailProjection anchor p (n + 1)
    rfl

theorem transportedTailSystem_anchor
    (anchor : ℕ)
    (p : IdempotentProjection ℝ (RealStageVector anchor)) :
    (transportedTailSystem anchor p).projection
        0 = p := by
  change transportedTailProjection anchor p 0 = p
  rfl

theorem transportedTailSystem_readout_anchor
    (anchor : ℕ)
    (p : IdempotentProjection ℝ (RealStageVector anchor)) :
    (transportedTailSystem anchor p).normalizedReadout
        0 = normalizedProjectionRankDyadic p := by
  change normalizedProjectionRankDyadic
      (transportedTailProjection anchor p 0) =
    normalizedProjectionRankDyadic p
  rfl

theorem transportedTailSystem_readout_add
    (anchor : ℕ)
    (p : IdempotentProjection ℝ (RealStageVector anchor))
    (n : RealUHFProjectionRankTailIndex anchor) :
    (transportedTailSystem anchor p).normalizedReadout n =
      normalizedProjectionRankDyadic p := by
  simpa [RealUHFProjectionRankTailIndex.add] using
    (RealUHFProjectionRankTailSystem.normalizedReadout_add
      (transportedTailSystem anchor p) 0 n)

end InfoGeometry.Canonical
