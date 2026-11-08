/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationLinearityWave16

noncomputable section

namespace InfoGeometry.SuperGrassmannian.FockProjectorTransport

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Canonical.SplitCliffordTensorBridge

private abbrev oddGenerator (n : ℕ) (x : TowerSpace n) : SplitCliffordInfinity :=
  DirectLimit.Algebra.of SplitClNNAlg
    (fun i j h => splitCliffordMap i j h) n
    (CliffordAlgebra.ι (TowerForm n) x)

/-- An odd finite-stage Clifford generator transports the negative chiral
projector to the positive chiral projector on the actual Fock direct limit. -/
theorem odd_generator_maps_projectorMinus_to_plus
    (n : ℕ) (x : TowerSpace n) (ψ : FockStage n) :
    paraProjectorPlus fockInfinityInvolute
        (splitCliffordFockAction (oddGenerator n x) (fockToInfinity n ψ)) =
      splitCliffordFockAction (oddGenerator n x)
        (paraProjectorMinus fockInfinityInvolute (fockToInfinity n ψ)) := by
  rw [paraProjectorPlus_apply, paraProjectorMinus_apply]
  rw [fockInfinityInvolute_action_generator_anticommutes,
    fockInfinityInvolute_ofStage]
  have hneg :
      -splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (CliffordAlgebra.involute ψ)) =
        splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (-CliffordAlgebra.involute ψ)) := by
    rw [splitCliffordFockAction_of, splitCliffordFockAction_of,
      map_neg, fockToInfinity_neg]
  rw [hneg]
  calc
    (1 / 2 : ℝ) •
          (splitCliffordFockAction (oddGenerator n x) (fockToInfinity n ψ) +
            splitCliffordFockAction (oddGenerator n x)
              (fockToInfinity n (-CliffordAlgebra.involute ψ))) =
        (1 / 2 : ℝ) • splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n ψ - fockToInfinity n (CliffordAlgebra.involute ψ)) := by
            rw [← splitCliffordFockAction_add_right]
            congr 2
            rw [fockToInfinity_neg]
            abel
    _ = splitCliffordFockAction (oddGenerator n x)
          ((1 / 2 : ℝ) •
            (fockToInfinity n ψ - fockToInfinity n (CliffordAlgebra.involute ψ))) := by
            rw [splitCliffordFockAction_smul_right]

/-- The same odd generator transports the positive chiral projector to the
negative chiral projector on the actual Fock direct limit. -/
theorem odd_generator_maps_projectorPlus_to_minus
    (n : ℕ) (x : TowerSpace n) (ψ : FockStage n) :
    paraProjectorMinus fockInfinityInvolute
        (splitCliffordFockAction (oddGenerator n x) (fockToInfinity n ψ)) =
      splitCliffordFockAction (oddGenerator n x)
        (paraProjectorPlus fockInfinityInvolute (fockToInfinity n ψ)) := by
  rw [paraProjectorMinus_apply, paraProjectorPlus_apply]
  rw [fockInfinityInvolute_action_generator_anticommutes,
    fockInfinityInvolute_ofStage]
  have hneg :
      -splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (CliffordAlgebra.involute ψ)) =
        splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (-CliffordAlgebra.involute ψ)) := by
    rw [splitCliffordFockAction_of, splitCliffordFockAction_of,
      map_neg, fockToInfinity_neg]
  rw [hneg]
  have hneg' :
      splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (-CliffordAlgebra.involute ψ)) =
        -splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n (CliffordAlgebra.involute ψ)) := by
    rw [splitCliffordFockAction_of, splitCliffordFockAction_of,
      map_neg, fockToInfinity_neg]
  rw [hneg']
  calc
    (1 / 2 : ℝ) •
          (splitCliffordFockAction (oddGenerator n x) (fockToInfinity n ψ) -
            -splitCliffordFockAction (oddGenerator n x)
              (fockToInfinity n (CliffordAlgebra.involute ψ))) =
        (1 / 2 : ℝ) • splitCliffordFockAction (oddGenerator n x)
          (fockToInfinity n ψ + fockToInfinity n (CliffordAlgebra.involute ψ)) := by
            rw [sub_neg_eq_add]
            rw [← splitCliffordFockAction_add_right]
    _ = splitCliffordFockAction (oddGenerator n x)
          ((1 / 2 : ℝ) •
            (fockToInfinity n ψ + fockToInfinity n (CliffordAlgebra.involute ψ))) := by
            rw [splitCliffordFockAction_smul_right]

end InfoGeometry.SuperGrassmannian.FockProjectorTransport
