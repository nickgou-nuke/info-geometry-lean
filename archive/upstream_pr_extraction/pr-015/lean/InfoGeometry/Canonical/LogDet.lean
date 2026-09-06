import InfoGeometry.Jordan.LogDet
import InfoGeometry.Jordan.BurgStein

/-!
# InfoGeometry.Canonical.LogDet

Canonical facade for log-determinant barrier and Burg/Bregman geometry on SPD
matrices.
-/

namespace InfoGeometry.Canonical.LogDet

export InfoGeometry.Jordan (
  burgKernel
  burgKernel_nonneg
  burgKernel_one
  steinLoss
  steinLoss_eq_trace_minus_logdet_minus_dim
  steinLoss_self
  steinLoss_eq_trace_add_barrier_diff_sub_dim
  burgKernel_normalizedDistortion_det_nonneg
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

end InfoGeometry.Canonical.LogDet
