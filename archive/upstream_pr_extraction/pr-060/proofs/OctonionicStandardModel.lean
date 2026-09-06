import proofs.Clifford55AnomalyOSP

/-!
# Octonionic standard-model dimension facts

The external clone contained a small `Cl(5,5)` dimension check.  This module
keeps the useful arithmetic as a theorem-honest compatibility layer over the
active `Clifford55AnomalyOSP` development.  It does not construct octonions or a
physical Standard Model.
-/

noncomputable section

namespace OctonionicStandardModel

/-- Clifford real vector-space dimension, shared with the active split-signature development. -/
def cliffordDim (p q : ℕ) : ℕ := Clifford55AnomalyOSP.cliffordDim p q

/-- The real vector-space dimension of `Cl(5,5)` is `1024`. -/
theorem cliffordDim_55 : cliffordDim 5 5 = 1024 := by
  norm_num [cliffordDim, Clifford55AnomalyOSP.cliffordDim]

/-- Dimension match `dim Cl(5,5)=dim Cl(1,1)·dim Cl(4,4)`. -/
theorem cl_55_factorization_dim :
    cliffordDim 5 5 = cliffordDim 1 1 * cliffordDim 4 4 := by
  norm_num [cliffordDim, Clifford55AnomalyOSP.cliffordDim]

/-- Split-signature anomaly index vanishes for `(5,5)`. -/
theorem absolute_anomaly_cancellation : Clifford55AnomalyOSP.anomalyIndex 5 5 = 0 := by
  norm_num [Clifford55AnomalyOSP.anomalyIndex]

end OctonionicStandardModel
