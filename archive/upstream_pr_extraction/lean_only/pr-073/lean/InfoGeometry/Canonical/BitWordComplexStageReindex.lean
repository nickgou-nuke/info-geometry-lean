import InfoGeometry.Canonical.GenuineMatrixStageMorphism
import InfoGeometry.Canonical.CuntzMatrixTraceTower
import InfoGeometry.Clifford.CliffordBitWordEquivalence

noncomputable section
namespace InfoGeometry.Canonical.BitWordComplexStageReindex

open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Algebra.CliffordBitWordEquivalence

def equiv (n : ℕ) :
    ComplexMatrixStage.Stage n ≃ₐ[ℂ]
      CuntzMatrixTowerInstantiation.MatrixStage n :=
  Matrix.reindexAlgEquiv ℂ ℂ (bitWordFinPowTwoEquiv n)

theorem equiv_apply (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    equiv n A = Matrix.reindex (bitWordFinPowTwoEquiv n)
      (bitWordFinPowTwoEquiv n) A := rfl

theorem equiv_star (n : ℕ) (A : ComplexMatrixStage.Stage n) :
    equiv n (star A) = star (equiv n A) := by
  ext i j
  simp [equiv, Matrix.reindexAlgEquiv, Matrix.star_apply]

theorem finPowTwoEquiv_succ_apply (n : ℕ) (u : BitWord n) (b : Bool) :
    bitWordFinPowTwoEquiv (n + 1)
        (InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordSuccEquiv n (u, b)) =
      stageIndexEquiv n
        (bitWordFinPowTwoEquiv n u, finTwoEquivBool.symm b) := by
  simp [bitWordFinPowTwoEquiv,
    InfoGeometry.Algebra.CliffordBitWordEquivalence.bitWordSuccEquiv,
    prefixSucc_extendSucc]


end InfoGeometry.Canonical.BitWordComplexStageReindex
end noncomputable section
