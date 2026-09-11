import InfoGeometry.Lie.SplitOctonionEllNativeTrifactor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionEllPolarization

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllFlowDecomposition

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
open InfoGeometry.Lie.SplitOctonionEllNativeTrifactor

abbrev CZ := CanonicalZorn

@[simp] def ellWeight : Fin 8 → ℝ
  | 0 | 1 | 2 => -1
  | 3 | 4 => 0
  | 5 | 6 | 7 => 1
  | _ => 0

theorem ellGrading_ellWeightBasisReal (i : Fin 8) :
    ellGrading (ellWeightBasisReal i) =
      ellWeight i • ellWeightBasisReal i := by
  rw [ellWeightBasisReal_apply]
  fin_cases i
  · change ellGrading (rootMinus 0) = (-1 : ℝ) • rootMinus 0
    rw [ellGrading_apply, ellCommutator_rootMinus]
    rw [smul_smul]
    norm_num
  · change ellGrading (rootMinus 1) = (-1 : ℝ) • rootMinus 1
    rw [ellGrading_apply, ellCommutator_rootMinus]
    rw [smul_smul]
    norm_num
  · change ellGrading (rootMinus 2) = (-1 : ℝ) • rootMinus 2
    rw [ellGrading_apply, ellCommutator_rootMinus]
    rw [smul_smul]
    norm_num
  · simp only [ellWeightBasis, ellWeight, zero_smul]
    rw [ellGrading_apply, ellCommutator_apply]
    ext j <;>
      simp [lUnit,
        InfoGeometry.Canonical.ZornMatrix.mul,
        Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
        InfoGeometry.Canonical.ZornMatrix.dot,
        InfoGeometry.Canonical.ZornMatrix.cross]
  · norm_num [ellWeightBasis, ellWeight, ellGrading_apply,
      ellCommutator_apply, sub_self]
  · change ellGrading (rootPlus 0) = (1 : ℝ) • rootPlus 0
    rw [ellGrading_apply, ellCommutator_rootPlus]
    rw [smul_smul]
    norm_num
  · change ellGrading (rootPlus 1) = (1 : ℝ) • rootPlus 1
    rw [ellGrading_apply, ellCommutator_rootPlus]
    rw [smul_smul]
    norm_num
  · change ellGrading (rootPlus 2) = (1 : ℝ) • rootPlus 2
    rw [ellGrading_apply, ellCommutator_rootPlus]
    rw [smul_smul]
    norm_num

theorem flowPlus_ellWeightBasisReal (i : Fin 8) :
    flowPlus (ellWeightBasisReal i) =
      ((ellWeight i * ellWeight i + ellWeight i) / 2) •
        ellWeightBasisReal i := by
  unfold flowPlus
  rw [LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply,
    ellGrading_ellWeightBasisReal, map_smul,
    ellGrading_ellWeightBasisReal]
  module

theorem flowMinus_ellWeightBasisReal (i : Fin 8) :
    flowMinus (ellWeightBasisReal i) =
      ((ellWeight i * ellWeight i - ellWeight i) / 2) •
        ellWeightBasisReal i := by
  unfold flowMinus
  rw [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
    ellGrading_ellWeightBasisReal, map_smul,
    ellGrading_ellWeightBasisReal]
  module

theorem flowZero_ellWeightBasisReal (i : Fin 8) :
    flowZero (ellWeightBasisReal i) =
      (1 - ellWeight i * ellWeight i) • ellWeightBasisReal i := by
  unfold flowZero
  change ellWeightBasisReal i -
      ellGrading (ellGrading (ellWeightBasisReal i)) = _
  rw [ellGrading_ellWeightBasisReal, map_smul,
    ellGrading_ellWeightBasisReal]
  module

end InfoGeometry.Lie.SplitOctonionEllFlowDecomposition
