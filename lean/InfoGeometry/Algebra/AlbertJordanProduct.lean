import Mathlib.Tactic
import InfoGeometry.Algebra.RealSplitAlbert

/-!
# Jordan product on the real split-Albert carrier

The concrete `CubicJordanOs.AlbertMatrix` uses integral split-octonion
coordinates and therefore is not yet a real Jordan algebra carrier.  The
real carrier in `RealSplitAlbert` does have the coordinate matrix product.
This file exposes its Jordan symmetrization without hiding any obligations
behind an axiom or an unproved algebraic instance.
-/

namespace InfoGeometry.Algebra.RealAlbertMatrix

noncomputable section

/-- The Jordan symmetrization of the displayed Hermitian coordinate product. -/
def jordanProduct (X Y : RealAlbertMatrix) : RealAlbertMatrix :=
  (1 / 2 : ℝ) • (mul X Y + mul Y X)

/-- The Jordan product is commutative by construction. -/
theorem jordanProduct_comm (X Y : RealAlbertMatrix) :
    jordanProduct X Y = jordanProduct Y X := by
  unfold jordanProduct
  rw [add_comm (mul X Y) (mul Y X)]

/-- The Jordan product has zero as an annihilator. -/
theorem jordanProduct_zero_left (X : RealAlbertMatrix) :
    jordanProduct 0 X = 0 := by
  unfold jordanProduct
  rfl

/-- The same zero law on the right, obtained from commutativity. -/
theorem jordanProduct_zero_right (X : RealAlbertMatrix) :
    jordanProduct X 0 = 0 := by
  rw [jordanProduct_comm, jordanProduct_zero_left]

end

end InfoGeometry.Algebra.RealAlbertMatrix
