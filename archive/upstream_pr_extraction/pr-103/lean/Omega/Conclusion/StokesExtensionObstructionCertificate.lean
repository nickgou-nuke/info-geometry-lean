import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-stokes-extension-obstruction-certificate`. The realizable-image
upper bound is incompatible with the stated strict inequality, so no filling can exist. -/
theorem paper_conclusion_stokes_extension_obstruction_certificate
    (sampledImageValue phaseSamplingUpperBound : ℝ)
    (exceeds_sampling_bound : phaseSamplingUpperBound < sampledImageValue) :
    ¬ sampledImageValue ≤ phaseSamplingUpperBound := by
  exact not_le_of_gt exceeds_sampling_bound

end Omega.Conclusion
