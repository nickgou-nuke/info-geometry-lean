/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Combinatorics.LeechEvenIntegral

/-!
# A metric statement for Golay words in the Leech numerator

This file uses the repository's actual extended Golay code and its
Construction-B/neighbor numerator. For a codeword `c`, the vector `2 c` is in
the even numerator branch. Its squared norm after the `1 / sqrt 8` scaling is
`hammingWeight c / 2`. Consequently, a minimum-weight lower bound of eight
implies scaled squared norm at least four for every nonzero codeword lift.

The minimum-weight bound remains an explicit hypothesis here: the owner
`ExtendedBinaryGolay.minimumWeight_eq_eight` is conditional on its QR injection
input. This file does not claim a proof of Leech rootlessness or unimodularity.
-/

namespace InfoGeometry.Canonical.GolayToLeech

open InfoGeometry.Combinatorics.ExtendedBinaryGolay
open InfoGeometry.Combinatorics.LeechLattice

/-- The even-branch numerator lift of a binary Golay word. -/
def golayNumeratorLift (c : Word24) :
    InfoGeometry.Combinatorics.GolayConstructionA.IntegerWord24 :=
  evenNumerator c 0

/-- Every codeword lift belongs to the actual Leech numerator carrier. -/
theorem golayNumeratorLift_mem
    (c : Word24) (hc : c ∈ codeSubmodule) :
    golayNumeratorLift c ∈ numerator := by
  change evenNumerator c 0 ∈ numerator
  exact Or.inl ⟨c, hc, 0, by simp [coordinateSum], rfl⟩

/-- The integral squared norm of `2 c` is four times the binary Hamming
weight of `c`. -/
theorem golayNumeratorLift_normSq
    (c : Word24) :
    InfoGeometry.Combinatorics.LeechLattice.normSqNumerator
      (golayNumeratorLift c) = 4 * hammingWeight c := by
  rw [golayNumeratorLift, InfoGeometry.Combinatorics.LeechEvenIntegral.normSq_even]
  simp

/-- The scaled realization of the lift has squared norm exactly half the
binary Hamming weight. -/
theorem golayNumeratorLift_scaled_normSq
    (c : Word24) :
    (∑ i, InfoGeometry.Combinatorics.LeechLattice.scaledRealization
      (golayNumeratorLift c) i *
      InfoGeometry.Combinatorics.LeechLattice.scaledRealization
        (golayNumeratorLift c) i) =
        (hammingWeight c : ℝ) / 2 := by
  rw [InfoGeometry.Combinatorics.LeechLattice.scaledRealization_normSq,
    golayNumeratorLift_normSq]
  push_cast
  ring

/-- A conditional nonzero norm bound obtained from a genuine codeword
weight bound, rather than from a vacuous lattice-membership predicate. -/
theorem golayNumeratorLift_norm_ge_four
    (c : Word24) (hc : c ∈ codeSubmodule) (hc0 : c ≠ 0)
    (hMin : ∀ w ∈ code, w ≠ 0 → 8 ≤ hammingWeight w) :
    (4 : ℝ) ≤
      ∑ i, InfoGeometry.Combinatorics.LeechLattice.scaledRealization
        (golayNumeratorLift c) i *
        InfoGeometry.Combinatorics.LeechLattice.scaledRealization
          (golayNumeratorLift c) i := by
  have hCode : c ∈ code :=
    (InfoGeometry.Combinatorics.ExtendedBinaryGolay.mem_code_iff_mem_codeSubmodule c).2 hc
  have hWeight := hMin c hCode hc0
  rw [golayNumeratorLift_scaled_normSq]
  have hWeightReal : (8 : ℝ) ≤ (hammingWeight c : ℝ) := by
    exact_mod_cast hWeight
  linarith

end InfoGeometry.Canonical.GolayToLeech
