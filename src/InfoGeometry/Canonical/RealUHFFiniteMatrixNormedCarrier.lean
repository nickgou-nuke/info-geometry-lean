import InfoGeometry.Canonical.CliffordCARTopologicalColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Instances.Matrix

/-!
# Native normed carrier for finite matrix stages

`MatStage n` is a finite matrix, hence a finite product of copies of `ℝ`.
Mathlib's finite-function normed additive-group and normed-space instances can
be reused directly through the reducible matrix definition.
-/

namespace InfoGeometry.Canonical.RealUHFFiniteMatrixNormedCarrier

open InfoGeometry.Clifford.Cl11TensorTower

noncomputable instance matStageNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (MatStage n) :=
  inferInstanceAs
    (NormedAddCommGroup
      (InfoGeometry.Clifford.TowerMatrix.Idx n →
        InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ))

noncomputable instance matStageNormedSpace (n : ℕ) :
    NormedSpace ℝ (MatStage n) :=
  inferInstanceAs
      (NormedSpace ℝ
      (InfoGeometry.Clifford.TowerMatrix.Idx n →
        InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ))

noncomputable instance matStageT2Space (n : ℕ) :
    T2Space (MatStage n) :=
  inferInstanceAs
    (T2Space
      (InfoGeometry.Clifford.TowerMatrix.Idx n →
        InfoGeometry.Clifford.TowerMatrix.Idx n → ℝ))

end InfoGeometry.Canonical.RealUHFFiniteMatrixNormedCarrier
