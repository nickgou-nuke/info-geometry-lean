/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ParaKahlerDikinKMS

namespace InfoGeometry.Canonical

/-- The negative-time para-KMS flow is a left inverse of the positive-time
flow, obtained from the existing one-parameter group law and the native
zero-time identity. -/
theorem paraKMSFlow_neg_cancel {n : ℕ}
    (space : DikinParaKahlerSpace n) (t : ℝ) (v : Fin n → ℝ) :
    paraKMSFlow space (-t) (paraKMSFlow space t v) = v := by
  rw [← paraKMSFlow_group space (-t) t v]
  simp

end InfoGeometry.Canonical
