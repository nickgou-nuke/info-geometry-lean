/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzResidualClosure

namespace InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzGeneralized

open BigOperators
open InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitz

variable {ι R Op : Type*} [DecidableEq ι] [Fintype ι]
  [CommRing R] [Ring Op] [StarRing Op] [Algebra R Op]

/-- The finite q-CCR vacuum defect is self-adjoint in every deformation sector. -/
theorem star_P_vac_eq_P_vac (A : QCCROperators ι R Op) :
    star (P_vac A) = P_vac A := by
  unfold P_vac
  rw [star_sub, star_one, star_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_mul, star_star]

end InfoGeometry.OperatorAlgebra.QCCRCuntzToeplitzGeneralized
