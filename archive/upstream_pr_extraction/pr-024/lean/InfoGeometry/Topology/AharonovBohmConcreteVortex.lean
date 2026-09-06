import Mathlib

/-!
# Concrete finite Aharonov--Bohm vortex owner

This file proves only the finite algebraic statement suggested by the SymPy twin:
`ω = exp (2π i / 3)` is a nontrivial third root of unity, and the diagonal
`3 × 3` vortex operator with final eigenvalue `ω` cubes to the identity.

It does not claim physical confinement, Hawking-radiation dynamics, or any
operator-algebraic SU(3) realization.
-/

namespace InfoGeometry.Topology.Parafermion

open Matrix Complex

noncomputable def omega : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 3)

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by norm_num : (3 : ℕ) ≠ 0)

theorem omega_cube_eq_one : omega ^ 3 = 1 :=
  omega_isPrimitiveRoot.pow_eq_one

theorem omega_ne_one : omega ≠ 1 :=
  omega_isPrimitiveRoot.ne_one (by norm_num)

noncomputable def concreteVortexOperator : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, omega]]

theorem concreteVortexOperator_cube_eq_one :
    concreteVortexOperator * concreteVortexOperator * concreteVortexOperator = 1 := by
  have hmul : omega * omega * omega = 1 := by
    simpa [pow_succ, mul_assoc] using omega_cube_eq_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [concreteVortexOperator, Matrix.mul_apply, Fin.sum_univ_three, hmul]

end InfoGeometry.Topology.Parafermion
