import InfoGeometry.Canonical.ThreeLevelFiniteGibbsVariational
import InfoGeometry.Inference.FisherVariance
import InfoGeometry.Inference.FisherInverse

namespace InfoGeometry.Canonical

namespace ThreeLevelFiniteGibbs

/-- Fisher-inverse sensitivity contract for a three-level Gibbs response slice. -/
abbrev OuterSensitivityContract :=
  {I : Matrix (Fin 2) (Fin 2) ℝ //
    InfoGeometry.Inference.FisherInverseContract I}

abbrev OuterSensitivityContract.fisherInverse
    (C : OuterSensitivityContract) : Matrix (Fin 2) (Fin 2) ℝ :=
  C.1

abbrev OuterSensitivityContract.contract
    (C : OuterSensitivityContract) :
    InfoGeometry.Inference.FisherInverseContract C.fisherInverse :=
  C.2

namespace OuterSensitivityContract

/-- The local covariance readout of the sensitivity contract. -/
noncomputable def localCovariance (C : OuterSensitivityContract) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  InfoGeometry.Inference.localCovariance C.fisherInverse C.contract

/-- The local variance readout of a three-level Gibbs sensitivity vector. -/
noncomputable def outerLocalVariance (C : OuterSensitivityContract) (v : Fin 2 → ℝ) : ℝ :=
  InfoGeometry.Inference.localVariance C.fisherInverse C.contract v

/-- The Fisher matrix times its local covariance is the identity. -/
theorem fisher_mul_localCovariance (C : OuterSensitivityContract) :
    C.fisherInverse * C.localCovariance = 1 := by
  simpa [localCovariance] using
    InfoGeometry.Inference.fisher_mul_localCovariance C.fisherInverse C.contract

/-- The local covariance times the Fisher matrix is the identity. -/
theorem localCovariance_mul_fisher (C : OuterSensitivityContract) :
    C.localCovariance * C.fisherInverse = 1 := by
  simpa [localCovariance] using
    InfoGeometry.Inference.localCovariance_mul_fisher C.fisherInverse C.contract

/-- The local variance is nonnegative. -/
theorem outerLocalVariance_nonneg (C : OuterSensitivityContract) (v : Fin 2 → ℝ) :
    0 ≤ outerLocalVariance C v := by
  simpa [outerLocalVariance] using
    InfoGeometry.Inference.localVariance_nonneg C.fisherInverse C.contract v

/-- The zero direction has zero local variance. -/
theorem outerLocalVariance_zero (C : OuterSensitivityContract) :
    outerLocalVariance C 0 = 0 := by
  simpa [outerLocalVariance] using
    InfoGeometry.Inference.localVariance_zero_direction C.fisherInverse C.contract

/-- Nonzero directions have strictly positive local variance. -/
theorem outerLocalVariance_pos (C : OuterSensitivityContract) {v : Fin 2 → ℝ}
    (hv : v ≠ 0) :
    0 < outerLocalVariance C v := by
  rw [outerLocalVariance, InfoGeometry.Inference.localVariance,
    InfoGeometry.Inference.localCovariance, if_pos C.contract.determinant_isUnit]
  exact C.contract.positiveDefinite.inv.dotProduct_mulVec_pos hv

/-- Local variance vanishes exactly on the zero direction. -/
theorem outerLocalVariance_eq_zero_iff (C : OuterSensitivityContract)
    (v : Fin 2 → ℝ) :
    outerLocalVariance C v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    by_contra hzero
    have hpos : 0 < outerLocalVariance C v := outerLocalVariance_pos C hzero
    linarith
  · intro hv
    simpa [hv] using outerLocalVariance_zero C

end OuterSensitivityContract

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
