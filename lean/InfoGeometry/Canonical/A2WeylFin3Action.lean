import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.A2WeylFin3Action

abbrev WeylA2 := Equiv.Perm (Fin 3)

def rho3 : WeylA2 := Equiv.swap 0 1
def shiftC3 : WeylA2 := Equiv.swap 0 1 * Equiv.swap 1 2

theorem rho3_sq : rho3 * rho3 = 1 := by
  ext x
  fin_cases x <;> rfl

theorem shiftC3_cube :
    shiftC3 * shiftC3 * shiftC3 = 1 := by
  ext x
  fin_cases x <;> rfl

theorem rho3_shiftC3_rho3 :
    rho3 * shiftC3 * rho3 = shiftC3⁻¹ := by
  ext x
  fin_cases x <;> rfl

end InfoGeometry.Canonical.A2WeylFin3Action
