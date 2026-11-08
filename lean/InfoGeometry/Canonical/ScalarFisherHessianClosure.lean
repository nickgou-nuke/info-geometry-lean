/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge

noncomputable section

namespace InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge

open SouriauOnsagerBKM
open InfoGeometry.Canonical.BKMScalarGaugeQuotient
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge

variable {n : ℕ}

/-- Scalar gauge directions are null directions of the additive Gibbs Hessian. -/
theorem secondFDeriv_logPartition_scalarGauge_zero
    (exponent : FiniteOperatorAlgebra n)
    (self_adjoint : IsSelfAdjoint exponent)
    (positive_partition : 0 < gibbsPartitionReal exponent)
    (scalar : ℝ) :
    (secondFDerivLogPartitionReadout exponent
      (scalar • (1 : FiniteOperatorAlgebra n))
      (scalar • (1 : FiniteOperatorAlgebra n))).re = 0 := by
  have hscalar : IsSelfAdjoint (scalar • (1 : FiniteOperatorAlgebra n)) := by
    change IsSelfAdjoint ((scalar : ℂ) • (1 : FiniteOperatorAlgebra n))
    rw [isSelfAdjoint_iff, star_smul]
    simp
  rw [secondFDeriv_logPartition_self_eq_zero_iff
    exponent (scalar • (1 : FiniteOperatorAlgebra n))
    self_adjoint positive_partition hscalar]
  exact Submodule.smul_mem (scalarGauge n) scalar
    (Submodule.subset_span (Set.mem_singleton (1 : FiniteOperatorAlgebra n)))

end InfoGeometry.Canonical.GibbsHessianScalarGaugeBridge
