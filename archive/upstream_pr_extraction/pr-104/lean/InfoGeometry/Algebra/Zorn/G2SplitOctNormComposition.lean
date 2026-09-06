import InfoGeometry.Algebra.Zorn.G2SplitOctZModBoolReadback
import InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
import InfoGeometry.OperatorAlgebra.SplitOctonionNormComposition

namespace InfoGeometry.Algebra.Zorn.G2SplitOctNormComposition

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge
open InfoGeometry.OperatorAlgebra.SplitOctonions.NormComposition

theorem zornNorm_mul (X Y : SplitOctF2) :
    zornNorm (mul X Y) = (zornNorm X && zornNorm Y) := by
  apply boolToZMod_injective
  rw [← detZ_toZornCell (mul X Y)]
  rw [boolToZMod_and]
  rw [← detZ_toZornCell X, ← detZ_toZornCell Y]
  rw [toZornCell_mul]
  exact InfoGeometry.Algebra.Zorn.Concrete.ZornCell.detZ_mulZ _ _

theorem zornNorm_mul_eq_false_of_left (hX : zornNorm X = false) :
    zornNorm (mul X Y) = false := by
  rw [zornNorm_mul, hX]
  rfl

theorem zornNorm_mul_eq_false_of_right (hY : zornNorm Y = false) :
    zornNorm (mul X Y) = false := by
  rw [zornNorm_mul, hY]
  simp

theorem zornNorm_mul_eq_true_iff {X Y : SplitOctF2} :
    zornNorm (mul X Y) = true ↔
      zornNorm X = true ∧ zornNorm Y = true := by
  rw [zornNorm_mul]
  cases hX : zornNorm X <;> cases hY : zornNorm Y <;>
    simp

theorem zornNorm_mul_eq_false_iff {X Y : SplitOctF2} :
    zornNorm (mul X Y) = false ↔
      zornNorm X = false ∨ zornNorm Y = false := by
  rw [zornNorm_mul]
  cases hX : zornNorm X <;> cases hY : zornNorm Y <;>
    simp

end InfoGeometry.Algebra.Zorn.G2SplitOctNormComposition
