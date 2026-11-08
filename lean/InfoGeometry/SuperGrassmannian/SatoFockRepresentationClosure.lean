/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

namespace InfoGeometry.SuperGrassmannian.SatoColimitTriality

open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford

/-- The descended Fock action is associative with the direct-limit Clifford
multiplication.  This is the representation closure theorem for the actual
algebraic colimit carrier. -/
theorem splitCliffordFockAction_mul_assoc
    (a b : SplitCliffordInfinity) (ψ : FockInfinity) :
    splitCliffordFockAction (a * b) ψ =
      splitCliffordFockAction a (splitCliffordFockAction b ψ) := by
  obtain ⟨n, a₀, ha⟩ := splitCliffordInfinity_exists_of a
  obtain ⟨m, b₀, hb⟩ := splitCliffordInfinity_exists_of b
  obtain ⟨r, ψ₀, hψ⟩ := DirectLimit.exists_eq_mk
    (f := fun i j h => fockStageMap i j h) ψ
  have hψ' : fockToInfinity r ψ₀ = ψ := by
    simpa [fockToInfinity] using hψ.symm
  let k := max (max n m) r
  have hnk : n ≤ k := le_trans (le_max_left n m) (le_max_left (max n m) r)
  have hmk : m ≤ k := le_trans (le_max_right n m) (le_max_left (max n m) r)
  have hrk : r ≤ k := le_max_right (max n m) r
  let aK := splitCliffordMap n k hnk a₀
  let bK := splitCliffordMap m k hmk b₀
  let ψK := fockStageMap r k hrk ψ₀
  have ha' : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k aK = a := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k aK =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n a₀ := by
            exact DirectLimit.Algebra.of_f
              (f := fun i j h => splitCliffordMap i j h) hnk a₀
      _ = a := ha
  have hb' : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k bK = b := by
    calc
      DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) k bK =
        DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) m b₀ := by
            exact DirectLimit.Algebra.of_f
              (f := fun i j h => splitCliffordMap i j h) hmk b₀
      _ = b := hb
  have hψK : fockToInfinity k ψK = ψ := by
    calc
      fockToInfinity k ψK = fockToInfinity r ψ₀ := by
        exact DirectLimit.Module.of_f
          (f := fun i j h => fockStageMap i j h)
          (i := r) (j := k) (hij := hrk) (x := ψ₀)
      _ = ψ := hψ'
  rw [← ha', ← hb', ← hψK]
  have hmul : DirectLimit.Algebra.of SplitClNNAlg
      (fun i j h => splitCliffordMap i j h) k (aK * bK) =
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j h => splitCliffordMap i j h) k aK *
      DirectLimit.Algebra.of SplitClNNAlg
        (fun i j h => splitCliffordMap i j h) k bK := by
    change (⟦⟨k, aK * bK⟩⟧ : SplitCliffordInfinity) =
      (⟦⟨k, aK⟩⟧ : SplitCliffordInfinity) * ⟦⟨k, bK⟩⟧
    exact (DirectLimit.mul_def k aK bK).symm
  rw [← hmul, splitCliffordFockAction_of,
    splitCliffordFockAction_of, splitCliffordFockAction_of]
  change fockToInfinity k (towerSpinorRep k (aK * bK) ψK) =
    fockToInfinity k (towerSpinorRep k aK
      (towerSpinorRep k bK ψK))
  rw [map_mul]
  rfl

end InfoGeometry.SuperGrassmannian.SatoColimitTriality
#print axioms InfoGeometry.SuperGrassmannian.SatoColimitTriality.splitCliffordFockAction_mul_assoc
