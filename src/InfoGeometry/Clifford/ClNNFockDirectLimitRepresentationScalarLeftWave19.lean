/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationAdditivityWave17

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.ClNN

/-- The descended Chevalley action is real-linear in its Clifford-colimit
argument.  The proof uses a common finite representative and the algebra-map
structure of the native Clifford representation at that stage. -/
theorem splitCliffordFockAction_smul_left
    (r : ℝ) (aInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction (r • aInf) ψInf =
      r • splitCliffordFockAction aInf ψInf := by
  obtain ⟨n, a, ha⟩ := splitCliffordInfinity_exists_of aInf
  obtain ⟨m, ψ, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψInf
  have hψ' : fockToInfinity m ψ = ψInf := by
    simpa [fockToInfinity] using hψ.symm
  let k := max n m
  have hnk : n ≤ k := le_max_left n m
  have hmk : m ≤ k := le_max_right n m
  let aK := splitCliffordMap n k hnk a
  let ψK := fockStageMap m k hmk ψ
  have ha' : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k aK = aInf := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n a := by
            exact DirectLimit.Algebra.of_f
              (f := fun i j h => splitCliffordMap i j h) hnk a
      _ = aInf := ha
  have ha_smul : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k (r • aK) = r • aInf := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k (r • aK) =
        r • DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK := by
            rw [map_smul]
      _ = r • aInf := by rw [ha']
  have hψK : fockToInfinity k ψK = ψInf := by
    calc
      fockToInfinity k ψK = fockToInfinity m ψ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := m) (j := k) (hij := hmk) (x := ψ)
      _ = ψInf := hψ'
  rw [← ha_smul, ← ha', ← hψK]
  have hmap_smul (ξ : FockStage k) :
      r • fockToInfinity k ξ = fockToInfinity k (r • ξ) := by
    change r • DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j h => fockStageMap i j h) k ξ =
      DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j h => fockStageMap i j h) k (r • ξ)
    exact ((DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) k).map_smul r ξ).symm
  simp only [splitCliffordFockAction_of]
  calc
    fockToInfinity k (towerSpinorRep k (r • aK) ψK) =
        fockToInfinity k (r • towerSpinorRep k aK ψK) := by
      exact congrArg (fockToInfinity k) (by
        rw [map_smul]
        change (r • towerSpinorRep k aK) ψK = _
        simp)
    _ = r • fockToInfinity k (towerSpinorRep k aK ψK) :=
      (hmap_smul _).symm

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
