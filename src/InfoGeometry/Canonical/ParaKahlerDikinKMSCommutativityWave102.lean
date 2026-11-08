/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ParaKahlerDikinKMS

noncomputable section

namespace InfoGeometry.Canonical

/-! # Wave 102: commutativity of the para-KMS flow

This file closes a genuine algebraic consequence of the existing one-parameter
group law.  It adds no carrier or wrapper: the theorem acts directly on the
owner's `DikinParaKahlerSpace` and its native flow.
-/

/-- The para-KMS flow maps commute because their parameters add commutatively. -/
theorem paraKMSFlow_commute {n : ℕ} (space : DikinParaKahlerSpace n)
    (s t : ℝ) (v : Fin n → ℝ) :
    paraKMSFlow space s (paraKMSFlow space t v) =
      paraKMSFlow space t (paraKMSFlow space s v) := by
  rw [← paraKMSFlow_group space s t v, ← paraKMSFlow_group space t s v,
    add_comm]

end InfoGeometry.Canonical

#print axioms InfoGeometry.Canonical.paraKMSFlow_commute
