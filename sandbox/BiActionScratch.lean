import InfoGeometry.Lie.SplitOctonionImaginaryAction
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionNonmultiplicativity

open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix

def zornConj (Z : CanonicalZorn) : CanonicalZorn :=
  { a := Z.b, b := Z.a, x := -Z.x, y := -Z.y }

abbrev BiSplitOctonions := CanonicalZorn × CanonicalZorn

def zornBiAction (Z : CanonicalZorn) (pq : BiSplitOctonions) : BiSplitOctonions :=
  (Z * pq.2, - (zornConj Z * pq.1))

theorem zornBiAction_sq (Z : CanonicalZorn) (pq : BiSplitOctonions) :
    zornBiAction Z (zornBiAction Z pq) = - ZornMatrix.detZ realCrossProduct3 Z • pq := by
  rcases Z with ⟨Za, Zb, Zx, Zy⟩
  rcases pq with ⟨⟨pa, pb, px, py⟩, ⟨qa, qb, qx, qy⟩⟩
  dsimp [zornBiAction, zornConj, ZornMatrix.detZ, realCrossProduct3, mul, dot, cross]
  refine Prod.ext ?_ ?_
  · ext1
    · simp only [Equiv.smul_def, coordEquiv]; ring
    · simp only [Equiv.smul_def, coordEquiv]; ring
    · ext i
      fin_cases i <;> { simp only [Equiv.smul_def, coordEquiv]; ring }
    · ext i
      fin_cases i <;> { simp only [Equiv.smul_def, coordEquiv]; ring }
  · ext1
    · simp only [Equiv.smul_def, coordEquiv]; ring
    · simp only [Equiv.smul_def, coordEquiv]; ring
    · ext i
      fin_cases i <;> { simp only [Equiv.smul_def, coordEquiv]; ring }
    · ext i
      fin_cases i <;> { simp only [Equiv.smul_def, coordEquiv]; ring }

end InfoGeometry.Lie.SplitOctonionNonmultiplicativity
