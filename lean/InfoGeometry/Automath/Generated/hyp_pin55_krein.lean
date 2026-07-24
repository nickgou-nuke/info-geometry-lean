import Mathlib
import Mathlib.Algebra.Lie.Basic

namespace Automath.Generated

set_option linter.unusedVariables false

theorem hyp_pin55_krein {R : Type u} [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
    (x y z : L) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
  lie_jacobi x y z


end Automath.Generated
