/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.NoncommRing

/-! # An ordered transform from two anticommuting involutions

For involutions `J` and `K` in an arbitrary ring, the sum of conjugation by
`K` and left multiplication by `J` squares to twice the identity when `J`
and `K` anticommute. The product order is retained throughout.

The transform is unnormalized: its square is `2 • X`, not `X`. No scalar
normalization, characteristic restriction, or physical interpretation is
part of this ring-level statement.
-/

namespace InfoGeometry.LinearAlgebra.SplitHadamard

variable {R : Type*} [Ring R]

/-- Two-sided multiplication by `K` plus left multiplication by `J`. -/
def splitHadamard (J K X : R) : R := K * X * K + J * X

theorem splitHadamard_add (J K X Y : R) :
    splitHadamard J K (X + Y) =
      splitHadamard J K X + splitHadamard J K Y := by
  dsimp [splitHadamard]
  noncomm_ring

/-- The mixed terms cancel by anticommutation, without commuting any factors. -/
theorem splitHadamard_sq (J K X : R)
    (hJ : J * J = 1) (hK : K * K = 1) (hanti : K * J + J * K = 0) :
    splitHadamard J K (splitHadamard J K X) = 2 • X := by
  calc
    splitHadamard J K (splitHadamard J K X) =
        (K * K) * X * (K * K) + (K * J + J * K) * X * K + (J * J) * X := by
      dsimp [splitHadamard]
      noncomm_ring
    _ = 2 • X := by simp [hK, hanti, hJ, two_nsmul]

theorem splitHadamard_one (J K : R) (hK : K * K = 1) :
    splitHadamard J K 1 = 1 + J := by
  simp [splitHadamard, hK]

theorem splitHadamard_left (J K : R)
    (hJ : J * J = 1) (hK : K * K = 1) (hanti : K * J + J * K = 0) :
    splitHadamard J K J = 1 - J := by
  have hKJ : K * J = -(J * K) := add_eq_zero_iff_eq_neg.mp hanti
  calc
    splitHadamard J K J = -(J * (K * K)) + J * J := by
      simp only [splitHadamard, hKJ, neg_mul, mul_assoc]
    _ = 1 - J := by simp [hK, hJ, sub_eq_add_neg, add_comm]

theorem splitHadamard_right (J K : R) (hK : K * K = 1) :
    splitHadamard J K K = K + J * K := by
  simp [splitHadamard, mul_assoc, hK]

/-- With `Ω = J * K`, the fourth readout is `K - Ω`. -/
theorem splitHadamard_left_mul_right (J K : R)
    (hJ : J * J = 1) (hK : K * K = 1) (hanti : K * J + J * K = 0) :
    splitHadamard J K (J * K) = K - J * K := by
  have hKJ : K * J = -(J * K) := add_eq_zero_iff_eq_neg.mp hanti
  calc
    splitHadamard J K (J * K) = (K * J) * (K * K) + (J * J) * K := by
      dsimp [splitHadamard]
      noncomm_ring
    _ = K - J * K := by simp [hK, hJ, hKJ, sub_eq_add_neg, add_comm]

/-- Ring homomorphisms transport the ordered formula without additional relations. -/
theorem map_splitHadamard {S : Type*} [Ring S]
    (f : R →+* S) (J K X : R) :
    f (splitHadamard J K X) = splitHadamard (f J) (f K) (f X) := by
  simp only [splitHadamard, map_add, map_mul]

end InfoGeometry.LinearAlgebra.SplitHadamard
