import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.QuadraticJordanH3Zorn

namespace InfoGeometry.Algebra

noncomputable instance : Mul (H3Zorn ℝ) where
  mul X Y := sorry

noncomputable instance : NonUnitalNonAssocRing (H3Zorn ℝ) where
  mul_add := sorry
  add_mul := sorry
  zero_mul := sorry
  mul_zero := sorry

noncomputable instance : IsScalarTower ℝ (H3Zorn ℝ) (H3Zorn ℝ) where
  smul_assoc := sorry

noncomputable instance : SMulCommClass ℝ (H3Zorn ℝ) (H3Zorn ℝ) where
  smul_comm := sorry

noncomputable def L (x : H3Zorn ℝ) : H3Zorn ℝ →ₗ[ℝ] H3Zorn ℝ where
  toFun y := x * y
  map_add' y z := sorry
  map_smul' c y := sorry

theorem jordan_identity (x y z : H3Zorn ℝ) :
  ⁅L x, ⁅L y, L z⁆⁆ = L (⁅L x, L y⁆ z) := sorry

def splitAlbertDerivations : LieSubalgebra ℝ (Derivation ℝ (H3Zorn ℝ) (H3Zorn ℝ)) := ⊤

end InfoGeometry.Algebra
