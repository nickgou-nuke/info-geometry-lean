import Mathlib.Data.Real.Basic
import Omega.Discussion.FramepotentialSffToHszk
import Omega.Discussion.TwoDesignDecouplingHSZK

namespace Omega.Discussion

/-- Numerical carriers for the comparison between the frame-potential and Thouless thresholds. -/
structure ZkVsThoulessData where
  frameData : FramepotentialHSZKData
  decouplingData : TwoDesignDecouplingHSZKData
  thoulessThreshold : ℝ

/-- The frame-potential threshold is bounded by the Thouless threshold plus the explicit
decoupling-to-HSZK overhead. -/
theorem paper_discussion_zk_vs_thouless
    (D : ZkVsThoulessData)
    (framePotentialGapSmall : D.frameData.framePotentialGapSmall)
    (approxTwoDesign : D.frameData.approxTwoDesign)
    (hszkBridge :
      D.frameData.hszkError ≤ D.decouplingData.hszkTolerance)
    (thoulessControlsDecoupling :
      D.decouplingData.decouplingError ≤ D.thoulessThreshold) :
    D.frameData.framePotentialGap ≤
      D.thoulessThreshold +
        (D.decouplingData.hszkTolerance - D.decouplingData.decouplingError) := by
  have hFrame : D.frameData.hszkErrorControlled :=
    paper_discussion_framepotential_sff_to_hszk D.frameData
      framePotentialGapSmall approxTwoDesign
  have hZkToOverhead :
      D.frameData.framePotentialGap ≤
        D.decouplingData.decouplingError +
          (D.decouplingData.hszkTolerance - D.decouplingData.decouplingError) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      le_trans hFrame hszkBridge
  have hThoulessWithOverhead :
      D.decouplingData.decouplingError +
          (D.decouplingData.hszkTolerance - D.decouplingData.decouplingError) ≤
        D.thoulessThreshold +
          (D.decouplingData.hszkTolerance - D.decouplingData.decouplingError) :=
    by
      simpa [add_comm] using
        add_le_add_right thoulessControlsDecoupling
          (D.decouplingData.hszkTolerance - D.decouplingData.decouplingError)
  exact le_trans hZkToOverhead hThoulessWithOverhead

end Omega.Discussion
