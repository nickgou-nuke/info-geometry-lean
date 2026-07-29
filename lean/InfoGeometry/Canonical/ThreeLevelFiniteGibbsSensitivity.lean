import InfoGeometry.Canonical.ThreeLevelFiniteGibbsVariational
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

end OuterSensitivityContract

end ThreeLevelFiniteGibbs

end InfoGeometry.Canonical
