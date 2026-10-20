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

/-- The descended Chevalley action is unital: the direct-limit Clifford unit
acts as the identity on the algebraic Fock direct limit. -/
theorem splitCliffordFockAction_one
    (ψInf : FockInfinity) :
    splitCliffordFockAction (1 : SplitCliffordInfinity) ψInf = ψInf := by
  obtain ⟨n, ψ, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψInf
  have hψ' : fockToInfinity n ψ = ψInf := by
    simpa [fockToInfinity] using hψ.symm
  rw [← hψ']
  have hone : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) n (1 : SplitClNNAlg n) =
      (1 : SplitCliffordInfinity) := by
    rw [DirectLimit.one_def n]
    rfl
  rw [← hone]
  rw [splitCliffordFockAction_of]
  change fockToInfinity n (towerSpinorRep n (1 : SplitClNNAlg n) ψ) =
    fockToInfinity n ψ
  rw [map_one]
  rfl

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
