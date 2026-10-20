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

/-- The descended Chevalley action is additive in its Clifford-colimit
argument. This is the algebra-linearity law of the actual direct-limit
representation, obtained by moving two algebra representatives and one Fock
representative to a common finite stage. -/
theorem splitCliffordFockAction_add_left
    (aInf bInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction (aInf + bInf) ψInf =
      splitCliffordFockAction aInf ψInf +
        splitCliffordFockAction bInf ψInf := by
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
  have hmap_add (x y : SplitClNNAlg k) :
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k x +
          DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) k y =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k (x + y) := by
    exact ((DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k).map_add x y).symm
  rw [hmap_add]
  simp only [splitCliffordFockAction_of]
  calc
    fockToInfinity k (towerSpinorRep k (aK + bK) ψK) =
        fockToInfinity k ((towerSpinorRep k aK +
          towerSpinorRep k bK) ψK) := by
      exact congrArg (fockToInfinity k)
        (congrArg (fun T : Module.End ℝ (FockStage k) => T ψK)
          ((towerSpinorRep k).map_add aK bK))
    _ = fockToInfinity k
          (towerSpinorRep k aK ψK + towerSpinorRep k bK ψK) := by
      rfl
    _ = fockToInfinity k (towerSpinorRep k aK ψK) +
        fockToInfinity k (towerSpinorRep k bK ψK) := by
      have hmap_fock_add (ξ ζ : FockStage k) :
          fockToInfinity k ξ + fockToInfinity k ζ =
            fockToInfinity k (ξ + ζ) := by
        change DirectLimit.Module.of ℝ ℕ FockStage
            (fun i j h => fockStageMap i j h) k ξ +
            DirectLimit.Module.of ℝ ℕ FockStage
              (fun i j h => fockStageMap i j h) k ζ =
          DirectLimit.Module.of ℝ ℕ FockStage
            (fun i j h => fockStageMap i j h) k (ξ + ζ)
        exact ((DirectLimit.Module.of ℝ ℕ FockStage
          (fun i j h => fockStageMap i j h) k).map_add ξ ζ).symm
      exact (hmap_fock_add _ _).symm

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
