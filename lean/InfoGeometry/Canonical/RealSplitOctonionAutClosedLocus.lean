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
  have hunit : IsClosed {f : SplitAutCandidate | f (1 : CZ) = 1} := by
    rw [show {f : SplitAutCandidate | f (1 : CZ) = 1} =
        {f : SplitAutCandidate | f (1 : CZ) - (1 : CZ) = 0} by
      ext f
      constructor
      · intro h
        exact sub_eq_zero.mpr h
      · intro h
        exact sub_eq_zero.mp h
      ]
    exact isClosed_candidate_unit_constraint
  have hmul : IsClosed {f : SplitAutCandidate |
      ∀ X Y : CZ, f (zMul X Y) - zMul (f X) (f Y) = 0} := by
    rw [show {f : SplitAutCandidate |
        ∀ X Y : CZ, f (zMul X Y) - zMul (f X) (f Y) = 0} =
      ⋂ X : CZ, ⋂ Y : CZ, {f : SplitAutCandidate |
        f (zMul X Y) - zMul (f X) (f Y) = 0} by
      ext f
      simp]
    apply isClosed_iInter
    intro X
    apply isClosed_iInter
    intro Y
    exact isClosed_candidate_multiplicativity_constraint X Y
  have hinter : IsClosed ({f : SplitAutCandidate | f (1 : CZ) = 1} ∩
      {f : SplitAutCandidate | ∀ X Y : CZ,
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
