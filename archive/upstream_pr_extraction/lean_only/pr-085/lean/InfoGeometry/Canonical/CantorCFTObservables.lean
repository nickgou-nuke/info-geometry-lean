import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

open Real

/-!
# Cantor Boundary Algebraic Readouts

This owner exposes the exact Sugawara central-charge calculation and a finite
boundary readout tuple. It does not construct a CFT, a KMS state, or a
partition-function trace.

**Zero global axioms.** All data is parameterized through the owner bridges.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorCFTObservables

open InfoGeometry.OperatorAlgebra.AffineVirasoroBridge

/-! ### 1. Central charge from the Sugawara bridge -/

/--
The split D₄ / so(4,4) level-one Sugawara readout is `4`.

This is proved in `InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.lean:181`:
  `sugawaraCentralCharge_so44_levelOne : sugawaraCentralCharge 1 28 6 = 4`

This theorem only records the imported algebraic Sugawara calculation.
-/
theorem split_so44_level_one_central_charge :
    InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge 1 28 6 = 4 :=
  InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge_so44_levelOne

/--
Half of the split D₄ level-one Sugawara readout is `2`.

This is an arithmetic consequence of the preceding theorem, not a theorem
about left/right CFT sectors or anomaly cancellation.
-/
theorem split_so44_half_readout :
    InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge 1 28 6 / 2 = 2 := by
  rw [split_so44_level_one_central_charge]
  norm_num

/-! ### 2. Finite boundary readout tuple -/

/--
A finite boundary readout record.

Parameters:
  - `centralCharge` : the Virasoro central charge
  - `temperature`   : a real parameter carried by the readout
  - `partitionValue` : a real scalar carried by the readout
-/
abbrev BoundaryPartitionReadout := ℝ × (ℝ × ℝ)

namespace BoundaryPartitionReadout

abbrev centralCharge (P : BoundaryPartitionReadout) : ℝ := P.1
abbrev temperature (P : BoundaryPartitionReadout) : ℝ := P.2.1
abbrev partitionValue (P : BoundaryPartitionReadout) : ℝ := P.2.2

end BoundaryPartitionReadout

/-/ A concrete finite readout with logarithmic parameter `log 2` and unit
scalar component. No KMS or trace interpretation is included. -/
def boundary_partition_readout (c : ℝ) : BoundaryPartitionReadout :=
  (c, (Real.log 2, 1))

theorem boundary_partition_readout_central_charge (c : ℝ) :
    (boundary_partition_readout c).centralCharge = c := rfl

theorem boundary_partition_readout_temperature (c : ℝ) :
    (boundary_partition_readout c).temperature = Real.log 2 := rfl

theorem boundary_partition_readout_scalar (c : ℝ) :
    (boundary_partition_readout c).partitionValue = 1 := rfl

/-! ### 3. CFT central charge readout table -/

/--
Central charge readout table for the Cantor boundary CFT.

| Current algebra | Level | dim(g) | h∨  | c |
|----------------|-------|--------|------|---|
| E₈(8)          | 1     | 248    | 30   | 8 |
| so(4,4) / D₄   | 1     | 28     | 6    | 4 |
-/
example : InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge 1 248 30 = 8 :=
  InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge_E8_levelOne

example : InfoGeometry.OperatorAlgebra.AffineVirasoroBridge.sugawaraCentralCharge 1 28 6 = 4 :=
  split_so44_level_one_central_charge

theorem diagonal_readout_difference_zero (c : ℝ) : c - c = 0 := by ring

end InfoGeometry.Canonical.CantorCFTObservables
