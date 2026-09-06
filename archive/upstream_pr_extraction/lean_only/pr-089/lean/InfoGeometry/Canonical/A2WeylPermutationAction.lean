import InfoGeometry.Canonical.A2WeylFin3Action

namespace InfoGeometry.Canonical.A2WeylPermutationAction

open InfoGeometry.Canonical.A2WeylFin3Action

/-- The permutation carrier for the Weyl group of type `A₂` on three colours. -/
abbrev WeylA2 := Equiv.Perm (Fin 3)

/-- Forgetful presentation of a colour permutation as a permutation of `Fin 3`. -/
def asPermFin3 (p : WeylA2) : Equiv.Perm (Fin 3) := p

def rho : WeylA2 := rho3
def shiftC : WeylA2 := shiftC3

theorem rho_sq_eq_self : rho * rho = 1 := by
  exact rho3_sq

theorem shiftC_cube_eq_self : shiftC * shiftC * shiftC = 1 := by
  exact shiftC3_cube

theorem rho_c_rho_eq_c_inv : rho * shiftC * rho = shiftC⁻¹ := by
  exact rho3_shiftC3_rho3

end InfoGeometry.Canonical.A2WeylPermutationAction
