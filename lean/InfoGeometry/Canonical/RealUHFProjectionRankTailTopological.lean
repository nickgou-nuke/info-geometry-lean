import InfoGeometry.Canonical.RealUHFProjectionRankTailSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

/-!
# Topological readout of an unanchored projection-rank tail

The finite tail system is read into the already-established real compact
interval.  Since the tail index is a subtype of `ℕ`, its topology is discrete;
continuity here is therefore a genuine native topological statement without
introducing an analytic completion of the operator system.
-/

namespace RealUHFProjectionRankTailSystem

noncomputable def realReadout
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) : RealUnitInterval :=
  dyadicToRealInterval
    ⟨(S.normalizedReadout n : ℚ), S.normalizedReadout_mem_unitInterval n⟩

theorem realReadout_succ
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor)
    (n : RealUHFProjectionRankTailIndex anchor) :
    S.realReadout n.succ = S.realReadout n := by
  unfold realReadout
  apply Subtype.ext
  change (((S.normalizedReadout n.succ : DyadicRational) : ℚ) : ℝ) =
    (((S.normalizedReadout n : DyadicRational) : ℚ) : ℝ)
  exact congrArg (fun q : DyadicRational => ((q : ℚ) : ℝ))
    (S.normalizedReadout_succ n)

noncomputable def realReadoutMap
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor) :
    RealUHFProjectionRankTailIndex anchor → RealUnitInterval :=
  fun n => S.realReadout n

theorem continuous_realReadoutMap
    {anchor : ℕ} (S : RealUHFProjectionRankTailSystem anchor) :
    Continuous S.realReadoutMap := by
  exact continuous_of_discreteTopology

end RealUHFProjectionRankTailSystem

end InfoGeometry.Canonical
