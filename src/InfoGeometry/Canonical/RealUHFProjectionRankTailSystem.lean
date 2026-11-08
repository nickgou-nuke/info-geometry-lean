import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealStageProjectionDyadicCocone

namespace InfoGeometry.Canonical

/-!
# Tail projection-rank systems for the real binary tower

`RealUHFProjectionRankSystem` is anchored at stage `0`.  Its coherence then
forces the normalized readout to agree with the one-dimensional stage-zero
readout.  This owner provides the correct unanchored alternative: a coherent
system starts at an arbitrary finite stage and continues along the tail of the
binary tower.

This is still a finite algebraic/dimension-group owner.  It does not claim a
`K₀`, `KO₀`, or completed UHF identification.
-/

abbrev RealUHFProjectionRankTailIndex (_anchor : ℕ) := ℕ

def RealUHFProjectionRankTailIndex.succ
    {anchor : ℕ} (n : RealUHFProjectionRankTailIndex anchor) :
    RealUHFProjectionRankTailIndex anchor := n + 1

def RealUHFProjectionRankTailIndex.add
    {anchor : ℕ} (n : RealUHFProjectionRankTailIndex anchor) (k : ℕ) :
    RealUHFProjectionRankTailIndex anchor := n + k

structure RealUHFProjectionRankTailSystem (anchor : ℕ) where
  projection : ∀ n : RealUHFProjectionRankTailIndex anchor,
    IdempotentProjection ℝ (RealStageVector (anchor + n))
  coherent : ∀ n : RealUHFProjectionRankTailIndex anchor,
    nextStageProjectionData (projection n) =
      projection n.succ

namespace RealUHFProjectionRankTailSystem

noncomputable def normalizedReadout
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) : DyadicRational :=
  normalizedProjectionRankDyadic (S.projection n)

theorem normalizedReadout_succ
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) :
    S.normalizedReadout n.succ =
      S.normalizedReadout n := by
  unfold normalizedReadout
  rw [← S.coherent n]
  apply Subtype.ext
  exact normalizedProjectionRank_nextStage (S.projection n)

theorem normalizedReadout_mem_unitInterval
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) :
    ((S.normalizedReadout n : DyadicRational) : ℚ) ∈ Set.Icc (0 : ℚ) 1 := by
  change normalizedProjectionRank (S.projection n) ∈ Set.Icc (0 : ℚ) 1
  exact ⟨normalizedProjectionRank_nonneg (S.projection n),
    normalizedProjectionRank_le_one (S.projection n)⟩

theorem normalizedReadout_isDyadic
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) :
    ((S.normalizedReadout n : DyadicRational) : ℚ) ∈ dyadicRational := by
  exact (S.normalizedReadout n).property

theorem normalizedReadout_add
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) (k : ℕ) :
    S.normalizedReadout (n.add k) = S.normalizedReadout n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hstep := S.normalizedReadout_succ (n.add k)
      calc
        S.normalizedReadout (n.add (Nat.succ k)) =
            S.normalizedReadout (n.add k).succ := by
              simp [RealUHFProjectionRankTailIndex.add,
                RealUHFProjectionRankTailIndex.succ, Nat.add_assoc] at hstep ⊢
        _ = S.normalizedReadout (n.add k) := hstep
        _ = S.normalizedReadout n := ih

end RealUHFProjectionRankTailSystem

end InfoGeometry.Canonical
