import InfoGeometry.Jordan.LogDet

/-!
# InfoGeometry.Canonical.LogDet

Canonical facade for log-determinant barrier and Burg/Bregman geometry on SPD
matrices.
-/

namespace InfoGeometry.Canonical.LogDet

export InfoGeometry.Jordan (
  logDetBarrier
  normalizedDistortion
  normalizedDistortion_det_pos
  normalizedDistortion_det
  logDetBregman
  logDetBregman_eq_burg_form
  logdet_square_nonneg_of_posDef
  logDetBregman_nonneg_of_commute
  logDetBregman_nonneg
  logDetBregman_self
)

@[simp] theorem logDetBarrier_eq_neg_log_det
    {n : ℕ} (X : InfoGeometry.Jordan.SPD n) :
    logDetBarrier X = -Real.log (Matrix.det X.mat) := rfl

end InfoGeometry.Canonical.LogDet
