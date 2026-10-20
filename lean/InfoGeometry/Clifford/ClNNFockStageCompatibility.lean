/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Clifford.ClNN

/-- The canonical Fock-colimit injection identifies a representative with its
image at every later finite stage. -/
@[simp] theorem fockToInfinity_stage_map (m n : ℕ) (h : m ≤ n)
    (ψ : FockStage m) :
    fockToInfinity n (fockStageMap m n h ψ) = fockToInfinity m ψ := by
  exact DirectLimit.Module.of_f
    (f := fun i j hij => fockStageMap i j hij)
    (i := m) (j := n) (hij := h) (x := ψ)

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
