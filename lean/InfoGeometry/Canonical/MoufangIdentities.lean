import Mathlib
import InfoGeometry.Canonical.IntegralSplitOctonionAlternativity
import InfoGeometry.Algebra.ZornAlternativeLaws

namespace InfoGeometry.Canonical

/-
These identities remain an explicit proof debt.  The native Zorn owner
`InfoGeometry.Algebra.ZornAlternativeLaws` proves the corresponding laws for
its bundled carrier, but the scalar-extension transport for this canonical
integer presentation still needs an instance-stable bridge.
-/

theorem splitOctonion_moufang_middle
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul x y) (splitOctonionMul z x) =
      splitOctonionMul x (splitOctonionMul (splitOctonionMul y z) x) := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  let Z := zornVectorMatrixRationalEquiv (integralToRational z)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.middle_moufang X Y Z
  apply EquivLike.injective zornVectorMatrixRationalEquiv
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  exact h

theorem splitOctonion_moufang_left
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul x (splitOctonionMul y (splitOctonionMul x z)) =
      splitOctonionMul (splitOctonionMul (splitOctonionMul x y) x) z := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  let Z := zornVectorMatrixRationalEquiv (integralToRational z)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.left_moufang X Y Z
  apply EquivLike.injective zornVectorMatrixRationalEquiv
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  exact h

theorem splitOctonion_moufang_right
    (x y z : StandardIntegralSplitOctonion) :
    splitOctonionMul (splitOctonionMul (splitOctonionMul z x) y) x =
      splitOctonionMul z (splitOctonionMul x (splitOctonionMul y x)) := by
  apply integralToRational_injective
  rw [integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul,
    integralToRational_mul, integralToRational_mul]
  let X := zornVectorMatrixRationalEquiv (integralToRational x)
  let Y := zornVectorMatrixRationalEquiv (integralToRational y)
  let Z := zornVectorMatrixRationalEquiv (integralToRational z)
  have h := InfoGeometry.Algebra.ZornVectorMatrix.right_moufang X Y Z
  apply EquivLike.injective zornVectorMatrixRationalEquiv
  rw [zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul,
    zornVectorMatrixRationalEquiv_map_mul]
  exact h

end InfoGeometry.Canonical
