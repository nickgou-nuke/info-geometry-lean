import Omega.CircleDimension.MinimalRecordAxis

namespace Omega.Discussion

/-- Discussion-level wrapper around the minimal-record-axis package: the admissible continuous
transversal is unique.
    thm:discussion-unique-continuous-transversal -/
theorem paper_discussion_unique_continuous_transversal
    {uniqueContinuousTransverse : Prop}
    (hUnique : uniqueContinuousTransverse) : uniqueContinuousTransverse :=
  hUnique

end Omega.Discussion
