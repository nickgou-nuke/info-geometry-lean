import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.Basic

namespace Automath.Generated

set_option linter.unusedVariables false

theorem hyp_pin55_krein {R : Type u} [Ring R] (L : Type v) [LieRing L] [Module R L]
    (x y z : L) :
    ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
  lie_jacobi x y z


end Automath.Generated
