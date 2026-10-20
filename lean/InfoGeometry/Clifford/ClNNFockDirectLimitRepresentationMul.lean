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

/-- The descended Chevalley action is a representation of the Clifford
algebra direct limit: multiplication in the algebra acts by composition on
its algebraic Fock direct limit. -/
theorem splitCliffordFockAction_mul
    (aInf bInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction (aInf * bInf) ψInf =
      splitCliffordFockAction aInf
        (splitCliffordFockAction bInf ψInf) := by
  obtain ⟨n, a, ha⟩ := splitCliffordInfinity_exists_of aInf
  obtain ⟨m, b, hb⟩ := splitCliffordInfinity_exists_of bInf
  obtain ⟨r, ψ, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψInf
  have hψ' : fockToInfinity r ψ = ψInf := by
    simpa [fockToInfinity] using hψ.symm
  let k := max (max n m) r
  have hnk : n ≤ k := le_trans (le_max_left n m) (le_max_left (max n m) r)
  have hmk : m ≤ k := le_trans (le_max_right n m) (le_max_left (max n m) r)
  have hrk : r ≤ k := le_max_right (max n m) r
  let aK := splitCliffordMap n k hnk a
  let bK := splitCliffordMap m k hmk b
  let ψK := fockStageMap r k hrk ψ
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
  have hb' : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k bK = bInf := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k bK =
          DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) m b := by
              exact DirectLimit.Algebra.of_f
                (f := fun i j h => splitCliffordMap i j h) hmk b
      _ = bInf := hb
  have hψK : fockToInfinity k ψK = ψInf := by
    calc
      fockToInfinity k ψK = fockToInfinity r ψ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := r) (j := k) (hij := hrk) (x := ψ)
      _ = ψInf := hψ'
  rw [← ha', ← hb', ← hψK]
  have hab :
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k (aK * bK) =
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK) *
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) k bK) := by
    rw [map_mul]
  rw [← hab]
  simp only [splitCliffordFockAction_of]
  change fockToInfinity k
      (towerSpinorRep k (aK * bK) ψK) =
    fockToInfinity k
      (towerSpinorRep k aK (towerSpinorRep k bK ψK))
  apply congrArg (fockToInfinity k)
  rw [map_mul]
  rfl

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
