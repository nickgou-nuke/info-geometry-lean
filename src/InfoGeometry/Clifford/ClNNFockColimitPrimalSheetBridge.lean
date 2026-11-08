import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
import InfoGeometry.Clifford.ClNNFockRepresentation

/-!
# Primal-sheet Fock action in the recursive Clifford colimit

The recursive Clifford tower already acts on the direct limit of its
Chevalley spinor stages. Each finite stage is linearly equivalent to the
exterior Fock space of the actual primal sheet. This module proves that the
colimit action on the corresponding transported representatives agrees with
the primal-sheet representation, including its quadratic-square relation.
-/

namespace InfoGeometry.Clifford.ClNNFockColimitPrimalSheetBridge

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford.ClNNFockRepresentation
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
open InfoGeometry.Clifford.FockSpaceCAR

variable (n : ℕ)

/-- The direct-limit action on a finite primal-sheet Fock state is the
transport of the recursive Chevalley action along the stage equivalence. -/
theorem splitCliffordFockAction_of_primalSheetFockRep
    (a : SplitClNNAlg n) (ψ : FockSpace (PrimalSheet n)) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n a)
        (fockToInfinity n ((towerSpinorToFock n).symm ψ)) =
      fockToInfinity n
        ((towerSpinorToFock n).symm (towerFockRep n a ψ)) := by
  rw [splitCliffordFockAction_of]
  rw [towerFockRep_apply]
  simp

/-- The colimit action preserves the finite-stage CAR after transporting
states from the actual primal-sheet Fock carrier. Its scalar is the native
neutral pairing, embedded as a finite-stage state. -/
theorem splitCliffordFockAction_neutral_generator_CAR
    (X Y : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y)))
          (fockToInfinity n ((towerSpinorToFock n).symm ψ))) +
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n Y)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)))
          (fockToInfinity n ((towerSpinorToFock n).symm ψ))) =
      fockToInfinity n
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
          (E := Vector n) X Y • ((towerSpinorToFock n).symm ψ)) := by
  have hmap_add (ξ ζ : FockStage n) :
      fockToInfinity n ξ + fockToInfinity n ζ = fockToInfinity n (ξ + ζ) := by
    change DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) n ξ +
        DirectLimit.Module.of ℝ ℕ FockStage
          (fun i j h => fockStageMap i j h) n ζ =
        DirectLimit.Module.of ℝ ℕ FockStage
          (fun i j h => fockStageMap i j h) n (ξ + ζ)
    exact ((DirectLimit.Module.of ℝ ℕ FockStage
      (fun i j h => fockStageMap i j h) n).map_add ξ ζ).symm
  simp only [splitCliffordFockAction_of_primalSheetFockRep]
  rw [hmap_add, ← (towerSpinorToFock n).symm.map_add,
    towerFockRep_neutral_generator_CAR,
    (towerSpinorToFock n).symm.map_smul]

/-- The normalized split-null head pair still has unit CAR after passage to
the algebraic Clifford and Fock direct limits. The finite-stage vacuum-sheet
normalization is preserved by the canonical colimit injections. -/
theorem splitCliffordFockAction_headNull_CAR
    (n : ℕ) (ψ : FockSpace (PrimalSheet (n + 1))) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) (n + 1)
          (CliffordAlgebra.ι (TowerForm (n + 1))
            (InfoGeometry.Clifford.ClNN.headNullMinus n)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) (n + 1)
            (CliffordAlgebra.ι (TowerForm (n + 1))
              (InfoGeometry.Clifford.ClNN.headNullPlus n)))
          (fockToInfinity (n + 1)
            ((towerSpinorToFock (n + 1)).symm ψ))) +
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) (n + 1)
          (CliffordAlgebra.ι (TowerForm (n + 1))
            (InfoGeometry.Clifford.ClNN.headNullPlus n)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) (n + 1)
            (CliffordAlgebra.ι (TowerForm (n + 1))
              (InfoGeometry.Clifford.ClNN.headNullMinus n)))
          (fockToInfinity (n + 1)
            ((towerSpinorToFock (n + 1)).symm ψ))) =
      fockToInfinity (n + 1) ((towerSpinorToFock (n + 1)).symm ψ) := by
  let X : Neutral (n + 1) := (neutralToSplit (n + 1)).symm
    (InfoGeometry.Clifford.ClNN.headNullMinus n)
  let Y : Neutral (n + 1) := (neutralToSplit (n + 1)).symm
    (InfoGeometry.Clifford.ClNN.headNullPlus n)
  have hpolar : QuadraticMap.polar (TowerForm (n + 1))
      (InfoGeometry.Clifford.ClNN.headNullMinus n)
      (InfoGeometry.Clifford.ClNN.headNullPlus n) = 1 := by
    change QuadraticMap.polar (InfoGeometry.Clifford.ClNN.Quad (n + 1))
        (InfoGeometry.Clifford.ClNN.headNullMinus n)
        (InfoGeometry.Clifford.ClNN.headNullPlus n) = 1
    exact InfoGeometry.Clifford.ClNN.polar_headNullMinus_headNullPlus n
  have hpair :
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
        (E := Vector (n + 1)) X Y = 1 := by
    calc
      _ = QuadraticMap.polar
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := Vector (n + 1))) X Y :=
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_polar
              X Y).symm
      _ = QuadraticMap.polar (InfoGeometry.Clifford.Qsplit (Vector (n + 1))) X Y := by
            rw [← chevelleyQsplit_eq_neutralForm]
      _ = QuadraticMap.polar (TowerForm (n + 1))
            (neutralToSplit (n + 1) X) (neutralToSplit (n + 1) Y) :=
            (neutralToSplit_polar (n + 1) X Y).symm
      _ = 1 := by simpa only [X, Y, LinearEquiv.apply_symm_apply] using hpolar
  have hcar := splitCliffordFockAction_neutral_generator_CAR
    (n + 1) X Y ψ
  simpa only [X, Y, LinearEquiv.apply_symm_apply, hpair, one_smul] using hcar

/-- Squaring a neutral Clifford generator in the direct-limit action on a
transported primal-sheet Fock state yields the tower quadratic scalar. -/
theorem splitCliffordFockAction_neutral_generator_sq
    (X : Neutral n) (ψ : FockSpace (PrimalSheet n)) :
    splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun m k h => splitCliffordMap m k h) n
          (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)))
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun m k h => splitCliffordMap m k h) n
            (CliffordAlgebra.ι (TowerForm n) (neutralToSplit n X)))
          (fockToInfinity n ((towerSpinorToFock n).symm ψ))) =
      fockToInfinity n
        ((towerSpinorToFock n).symm (TowerForm n (neutralToSplit n X) • ψ)) := by
  simp only [splitCliffordFockAction_of_primalSheetFockRep]
  rw [towerFockRep_neutral_generator_sq]

end InfoGeometry.Clifford.ClNNFockColimitPrimalSheetBridge
