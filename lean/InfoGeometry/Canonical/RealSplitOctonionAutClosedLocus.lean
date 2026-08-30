/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealSplitOctonionAutCandidateConstraint

/-!
# Closedness of the existing split-octonion automorphism locus

The subgroup carrier is assembled from the already-proved closed unit and
multiplicativity constraints.  No second subgroup is introduced.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

noncomputable section

theorem isClosed_splitOctonionAutSet :
    IsClosed (SplitOctonionAutSet (R := ℝ)) := by
  have hunit : IsClosed {f : Candidate | f (1 : CZ) = 1} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (isClosed_singleton.preimage (continuous_candidate_apply (1 : CZ)))
  have hmul : IsClosed {f : Candidate |
      ∀ X Y : CZ, f (zMul X Y) - zMul (f X) (f Y) = 0} := by
    rw [show {f : Candidate |
        ∀ X Y : CZ, f (zMul X Y) - zMul (f X) (f Y) = 0} =
      ⋂ X : CZ, ⋂ Y : CZ, {f : Candidate |
        f (zMul X Y) - zMul (f X) (f Y) = 0} by
      ext f
      simp]
    apply isClosed_iInter
    intro X
    apply isClosed_iInter
    intro Y
    exact isClosed_candidate_multiplicativity_constraint X Y
  have hinter : IsClosed ({f : Candidate | f (1 : CZ) = 1} ∩
      {f : Candidate | ∀ X Y : CZ,
        f (zMul X Y) - zMul (f X) (f Y) = 0}) :=
    hunit.inter hmul
  convert hinter using 1
  ext f
  simp only [SplitOctonionAutSet, IsSplitOctonionAut,
    PreservesZornOne, PreservesZornMul, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, hmul⟩
    refine ⟨h1, ?_⟩
    intro X Y
    exact sub_eq_zero.mpr (hmul X Y)
  · rintro ⟨h1, hmul⟩
    refine ⟨h1, ?_⟩
    intro X Y
    exact sub_eq_zero.mp (hmul X Y)

end
end InfoGeometry.Canonical
