/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.TCSSensitivity

/-!
# Directional derivative of the TCS response

The coordinate sensitivity vector is not merely a bookkeeping convention: this
module proves its directional-derivative action on the two-parameter TCS mean.
-/

namespace InfoGeometry.Inference

theorem hasDerivAt_tcsMeanAt_direction
    (liveTime x C K dC dK : ℝ) :
    HasDerivAt
      (fun t => tcsMeanAt liveTime x (C + t * dC) (K + t * dK))
      (dC * tcsSensitivity liveTime x 0 + dK * tcsSensitivity liveTime x 1) 0 := by
  unfold tcsMeanAt tcsSensitivity
  convert
    (((hasDerivAt_const 0 (C * x - K * x ^ 2)).add
      ((hasDerivAt_id' 0).mul_const (dC * x - dK * x ^ 2))).const_mul liveTime)
    using 1 <;> (try funext t) <;> simp <;> ring_nf <;> simp

end InfoGeometry.Inference
