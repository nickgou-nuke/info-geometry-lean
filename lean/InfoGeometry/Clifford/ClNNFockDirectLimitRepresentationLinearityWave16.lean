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

/-- The descended Chevalley action is additive in its Fock-colimit argument.
This is a linearity law of the actual algebraic colimit action, obtained from
finite-stage module linearity and the directed-system readback. -/
theorem splitCliffordFockAction_add_right
    (aInf : SplitCliffordInfinity) (ψInf φInf : FockInfinity) :
    splitCliffordFockAction aInf (ψInf + φInf) =
      splitCliffordFockAction aInf ψInf +
        splitCliffordFockAction aInf φInf := by
  obtain ⟨n, a, ha⟩ := splitCliffordInfinity_exists_of aInf
  obtain ⟨m, ψ, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψInf
  obtain ⟨r, φ, hφ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) φInf
  have hψ' : fockToInfinity m ψ = ψInf := by
    simpa [fockToInfinity] using hψ.symm
  have hφ' : fockToInfinity r φ = φInf := by
    simpa [fockToInfinity] using hφ.symm
  let k := max (max n m) r
  have hnk : n ≤ k := le_trans (le_max_left n m) (le_max_left (max n m) r)
  have hmk : m ≤ k := le_trans (le_max_right n m) (le_max_left (max n m) r)
  have hrk : r ≤ k := le_max_right (max n m) r
  let aK := splitCliffordMap n k hnk a
  let ψK := fockStageMap m k hmk ψ
  let φK := fockStageMap r k hrk φ
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
  have hψK : fockToInfinity k ψK = ψInf := by
    calc
      fockToInfinity k ψK = fockToInfinity m ψ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := m) (j := k) (hij := hmk) (x := ψ)
      _ = ψInf := hψ'
  have hφK : fockToInfinity k φK = φInf := by
    calc
      fockToInfinity k φK = fockToInfinity r φ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := r) (j := k) (hij := hrk) (x := φ)
      _ = φInf := hφ'
  rw [← ha', ← hψK, ← hφK]
  have hmap_add (ξ ζ : FockStage k) :
      fockToInfinity k ξ + fockToInfinity k ζ = fockToInfinity k (ξ + ζ) := by
    change DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) k ξ +
        DirectLimit.Module.of ℝ ℕ FockStage
          (fun i j h => fockStageMap i j h) k ζ =
        DirectLimit.Module.of ℝ ℕ FockStage
          (fun i j h => fockStageMap i j h) k (ξ + ζ)
    exact ((DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) k).map_add ξ ζ).symm
  rw [hmap_add]
  simp only [splitCliffordFockAction_of]
  calc
    fockToInfinity k (towerSpinorRep k aK (ψK + φK)) =
        fockToInfinity k (towerSpinorRep k aK ψK +
          towerSpinorRep k aK φK) := by
      exact congrArg (fockToInfinity k)
        ((towerSpinorRep k aK).map_add ψK φK)
    _ = fockToInfinity k (towerSpinorRep k aK ψK) +
        fockToInfinity k (towerSpinorRep k aK φK) := by
      exact (hmap_add _ _).symm

/-- The descended Chevalley action is real-linear in its Fock-colimit argument.
This is the scalar part of the module structure already present at every
finite Chevalley stage, transported through the actual direct-limit carrier. -/
theorem splitCliffordFockAction_smul_right
    (r : ℝ) (aInf : SplitCliffordInfinity) (ψInf : FockInfinity) :
    splitCliffordFockAction aInf (r • ψInf) =
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
  have hψK : fockToInfinity k ψK = ψInf := by
    calc
      fockToInfinity k ψK = fockToInfinity m ψ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := m) (j := k) (hij := hmk) (x := ψ)
      _ = ψInf := hψ'
  rw [← ha', ← hψK]
  have hmap_smul (c : ℝ) (ξ : FockStage k) :
      c • fockToInfinity k ξ = fockToInfinity k (c • ξ) := by
    change c • DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j h => fockStageMap i j h) k ξ =
      DirectLimit.Module.of ℝ ℕ FockStage
        (fun i j h => fockStageMap i j h) k (c • ξ)
    exact ((DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) k).map_smul c ξ).symm
  calc
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK)
        (r • fockToInfinity k ψK) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK)
        (fockToInfinity k (r • ψK)) := by
          rw [hmap_smul]
    _ = fockToInfinity k (towerSpinorRep k aK (r • ψK)) := by
          rw [splitCliffordFockAction_of]
    _ = fockToInfinity k (r • towerSpinorRep k aK ψK) := by
          exact congrArg (fockToInfinity k) ((towerSpinorRep k aK).map_smul r ψK)
    _ = r • fockToInfinity k (towerSpinorRep k aK ψK) := by
          exact (hmap_smul _ _).symm
    _ = r • splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK)
        (fockToInfinity k ψK) := by
          rw [splitCliffordFockAction_of]

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
