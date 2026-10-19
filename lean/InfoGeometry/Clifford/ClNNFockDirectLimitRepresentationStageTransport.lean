/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN

/-- The descended split-Clifford action is independent of the finite stage used
for a compatible pair of algebra and Fock representatives. -/
theorem splitCliffordFockAction_stage_transport (m n : ℕ) (h : m ≤ n)
    (a : SplitClNNAlg m) (ψ : FockStage m) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) m a)
        (fockToInfinity m ψ) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j hij => splitCliffordMap i j hij) n
            (splitCliffordMap m n h a))
        (fockToInfinity n (fockStageMap m n h ψ)) := by
  rw [splitCliffordFockAction_of, splitCliffordFockAction_of]
  rw [← towerSpinorRep_stageMap m n h a ψ]
  exact (DirectLimit.Module.of_f
    (f := fun i j hij => fockStageMap i j hij)
    (i := m) (j := n) (hij := h) (x := towerSpinorRep m a ψ)).symm

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
