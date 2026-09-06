import Mathlib.Data.Real.Basic
import Omega.Discussion.FramepotentialSffToHszk
import Omega.Discussion.TwoDesignDecouplingHSZK

namespace Omega.Discussion

/-- The frame-potential threshold is bounded by the Thouless threshold plus the explicit
decoupling-to-HSZK overhead. -/
theorem paper_discussion_zk_vs_thouless
    (framePotentialGap twoDesignError frameHSZKError thoulessThreshold : ℝ)
    (D : TwoDesignDecouplingHSZKData)
    (framePotentialGapSmall : framePotentialGap ≤ twoDesignError)
    (approxTwoDesign : twoDesignError ≤ frameHSZKError)
    (hszkBridge : frameHSZKError ≤ D.hszkTolerance)
    (thoulessControlsDecoupling : D.decouplingError ≤ thoulessThreshold) :
    framePotentialGap ≤
      thoulessThreshold + (D.hszkTolerance - D.decouplingError) := by
  have hFrame : framePotentialGap ≤ frameHSZKError :=
    paper_discussion_framepotential_sff_to_hszk framePotentialGap twoDesignError
      frameHSZKError framePotentialGapSmall approxTwoDesign
  have hZkToOverhead :
      framePotentialGap ≤
        D.decouplingError + (D.hszkTolerance - D.decouplingError) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      le_trans hFrame hszkBridge
  have hThoulessWithOverhead :
      D.decouplingError + (D.hszkTolerance - D.decouplingError) ≤
        thoulessThreshold + (D.hszkTolerance - D.decouplingError) :=
    by
      simpa [add_comm] using
        add_le_add_right thoulessControlsDecoupling
          (D.hszkTolerance - D.decouplingError)
  exact le_trans hZkToOverhead hThoulessWithOverhead

end Omega.Discussion
