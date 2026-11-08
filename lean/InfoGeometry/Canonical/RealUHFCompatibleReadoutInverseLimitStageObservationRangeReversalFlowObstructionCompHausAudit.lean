/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus

/-!
# Source audit: scalar obstruction to reversal-flow covariance

Under the stated readout-transport premise, the proposed reversal-flow square
forces `(exp t - exp (-t)) * z = 0` on every observed scalar. For nonzero `t`,
this forces the entire observation range to vanish, contradicting any
nontrivial-range witness. The result is conditional on its explicit square
and readout assumptions.
-/

#print axioms InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus.scalar_obstruction_of_reversal_flow_square
#print axioms InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus.stageObservationRange_zero_of_reversal_flow_square
#print axioms InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeReversalFlowObstructionCompHaus.no_reversal_flow_square_on_nontrivial_range
