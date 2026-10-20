/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationAdditivityWave17
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationScalarLeftWave19

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN

/-- A fixed element of the Clifford-colimit grade involution acts evenly on
its Fock-colimit representation. -/
theorem splitCliffordFockAction_grade_fixed_commutes
    (aInf : SplitCliffordInfinity)
    (ha : splitCliffordInfinityInvolute aInf = aInf)
    (ψInf : FockInfinity) :
    fockInfinityInvolute
        (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction aInf (fockInfinityInvolute ψInf) := by
  rw [splitCliffordFockAction_grade_equivariant, ha]

/-- A negated element of the Clifford-colimit grade involution acts oddly on
its Fock-colimit representation. -/
theorem splitCliffordFockAction_grade_negated_anticommutes
    (aInf : SplitCliffordInfinity)
    (ha : splitCliffordInfinityInvolute aInf = -aInf)
    (ψInf : FockInfinity) :
    fockInfinityInvolute
        (splitCliffordFockAction aInf ψInf) =
      -splitCliffordFockAction aInf (fockInfinityInvolute ψInf) := by
  rw [splitCliffordFockAction_grade_equivariant, ha,
    ← neg_one_smul ℝ aInf, splitCliffordFockAction_smul_left]
  simp

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
