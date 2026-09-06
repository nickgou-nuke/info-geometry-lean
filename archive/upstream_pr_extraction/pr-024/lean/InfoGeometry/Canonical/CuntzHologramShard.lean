import Mathlib
import InfoGeometry.Topology.CuntzCantorSpectralTriple
import InfoGeometry.Topology.CuntzMap

/-!
# Cuntz hologram shard readback

Finite theorem-safe readback of the classical hologram intuition:
local Cuntz branches carry isometric copies of the whole observable lane, and
under the Cuntz range-sum relation the two branch projections reassemble the
identity.

## Closed finite theorems
* Branch recovery from the imported `CuntzO2Carrier` isometry equations.
* Branch projection partition from the imported Cuntz range relation.
* Unitality and half-branch fixed-point readout for the imported Cuntz map.

## Conditional theorem from explicit premises
* `hologram_readout_fixed` depends on the explicit half-branch scaling premises.

## Scope
This file records the exact algebraic facts available from the abstract `O₂`
carrier.
-/

namespace InfoGeometry.Canonical.CuntzHologramShard

open InfoGeometry.Topology

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : InfoGeometry.Topology.CuntzO2Carrier Op)

/-- The left branch is an isometric copy of the whole observable lane. -/
theorem left_branch_recovers_whole (X : Op) :
    star C.S_left * (C.S_left * X) = X := by
  rw [← mul_assoc, C.left_isometry, one_mul]

/-- The right branch is an isometric copy of the whole observable lane. -/
theorem right_branch_recovers_whole (X : Op) :
    star C.S_right * (C.S_right * X) = X := by
  rw [← mul_assoc, C.right_isometry, one_mul]

/-- The two branch range projections reconstruct the identity exactly. -/
theorem branch_projections_sum_identity :
    C.leftRangeProjection + C.rightRangeProjection = 1 :=
  C.range_sum

/-- The Cuntz canonical endomorphism is unital: the whole is redistributed across the shards. -/
theorem whole_redistributed_across_shards :
    InfoGeometry.Topology.CuntzMap.CuntzMap Op C 1 = 1 :=
  InfoGeometry.Topology.CuntzMap.CuntzMap_unital Op C

/-- A half-branch readout is fixed by the Cuntz hologram transfer. -/
theorem hologram_readout_fixed
    (φ : Op →+ ℝ)
    (X : Op)
    (hleft : φ (C.S_left * X * star C.S_left) = (1 / 2 : ℝ) * φ X)
    (hright : φ (C.S_right * X * star C.S_right) = (1 / 2 : ℝ) * φ X) :
    φ (InfoGeometry.Topology.CuntzMap.CuntzMap Op C X) = φ X :=
  InfoGeometry.Topology.CuntzMap.CuntzMap_real_fixed_point_of_half_branch_scaling Op C φ X hleft hright

end InfoGeometry.Canonical.CuntzHologramShard
