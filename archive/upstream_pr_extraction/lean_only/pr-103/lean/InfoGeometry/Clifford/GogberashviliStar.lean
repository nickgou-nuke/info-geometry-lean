import InfoGeometry.Clifford.GogberashviliSplitOctonionBasis

/-!
# The six-vertex chiral star in the native split-octonion carrier

The paper's two triangles are represented by the six explicit generators
`J 0`, `J 1`, `J 2` and `j 0`, `j 1`, `j 2` already defined in
`GogberashviliSplitOctonionBasis`.  This file adds the finite vertex type and
the embedding into that carrier.  It does not identify this labeled star with
the separate `WeylG2` carrier.
-/

namespace InfoGeometry.Clifford.GogberashviliStar

open InfoGeometry.Clifford.GogberashviliSplitOctonionBasis
open InfoGeometry.Algebra.Zorn.ConcreteComposition
open InfoGeometry.Algebra.Zorn.ConcreteComposition.ZornCell

inductive Vertex
  | positive (i : Fin 3)
  | negative (i : Fin 3)
deriving DecidableEq, Fintype

def point : Vertex → ZornCell ℝ
  | .positive i => J i
  | .negative i => j i

theorem point_injective : Function.Injective point := by
  intro u v huv
  cases u with
  | positive i =>
      cases v with
      | positive k =>
          congr
          fin_cases i <;> fin_cases k <;>
            simpa [point, J] using huv
      | negative k =>
          fin_cases i <;> fin_cases k <;>
            (exfalso; norm_num [point, J, j] at huv)
  | negative i =>
      cases v with
      | positive k =>
          fin_cases i <;> fin_cases k <;>
            (exfalso; norm_num [point, J, j] at huv)
      | negative k =>
          congr
          fin_cases i <;> fin_cases k <;>
            simpa [point, j] using huv

theorem positive_square (i : Fin 3) :
    point (.positive i) * point (.positive i) = oneZ := by
  exact J_sq i

theorem negative_square (i : Fin 3) :
    point (.negative i) * point (.negative i) = negZ oneZ := by
  exact j_sq i

theorem positive_positive_product (i k : Fin 3) (hik : i ≠ k) :
    point (.positive i) * point (.positive k) =
      negZ (sumFin3 (fun r => (eps3 i k r : ℝ) • point (.negative r))) := by
  exact J_mul_J i k hik

theorem negative_negative_product (i k : Fin 3) (hik : i ≠ k) :
    point (.negative i) * point (.negative k) =
      negZ (sumFin3 (fun r => (eps3 i k r : ℝ) • point (.negative r))) := by
  exact j_mul_j i k hik

theorem mixed_product (i k : Fin 3) (hik : i ≠ k) :
    point (.negative k) * point (.positive i) =
      negZ (sumFin3 (fun r => (eps3 i k r : ℝ) • point (.positive r))) := by
  exact j_mul_J i k hik

theorem star_vertex_card : Fintype.card Vertex = 6 := by
  decide

end InfoGeometry.Clifford.GogberashviliStar
