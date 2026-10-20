/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNFockGradeProjectorTransportWave22

noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.Algebra.SuperGrassmannianClifford

/-- Super-grade-one finite exterior elements exchange the positive Fock
projector, by the canonical grade-one eigenspace theorem. -/
theorem splitCliffordFockAction_superGrade_one_projectorPlus
    (n : ℕ) (x : SplitExteriorStage n)
    (hx : x ∈ superGrade (InfoGeometry.CliffordTower.Qsplit n) (1 : ZMod 2))
    (ψ : FockInfinity) :
    fockInfinityProjectorPlus
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) n
            ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x)) ψ) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n
          ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x))
        (fockInfinityProjectorMinus ψ) := by
  exact splitCliffordFockAction_grade_one_projectorPlus _ _
    (directLimit_of_superGrade_one_negated n x hx)

/-- Super-grade-one finite exterior elements exchange the negative Fock
projector, by the canonical grade-one eigenspace theorem. -/
theorem splitCliffordFockAction_superGrade_one_projectorMinus
    (n : ℕ) (x : SplitExteriorStage n)
    (hx : x ∈ superGrade (InfoGeometry.CliffordTower.Qsplit n) (1 : ZMod 2))
    (ψ : FockInfinity) :
    fockInfinityProjectorMinus
        (splitCliffordFockAction
          (DirectLimit.Algebra.of SplitClNNAlg
            (fun i j h => splitCliffordMap i j h) n
            ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x)) ψ) =
      splitCliffordFockAction
        (DirectLimit.Algebra.of SplitClNNAlg
          (fun i j h => splitCliffordMap i j h) n
          ((cliffordExteriorEquiv (InfoGeometry.CliffordTower.Qsplit n)).symm x))
        (fockInfinityProjectorPlus ψ) := by
  exact splitCliffordFockAction_grade_one_projectorMinus _ _
    (directLimit_of_superGrade_one_negated n x hx)

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
