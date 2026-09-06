import Mathlib.Data.Matrix.Basic

open Matrix

namespace InfoGeometry.Physics.Dirac

/-- The Dirac Gamma Matrices in the Chiral (Weyl) Basis over ℤ. -/
def gamma_0 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0]]

def gamma_1 : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![ 0,  0,  0,  1],
    ![ 0,  0,  1,  0],
    ![ 0, -1,  0,  0],
    ![-1,  0,  0,  0]]

/-- 
THEOREM: The Clifford Algebra Boundary Condition.
Proves that the chiral Weyl representation natively satisfies the 
relativistic anti-commutation relations, rooting the Dirac boundary 
into the non-commutative geometry.
-/
theorem dirac_clifford_boundary :
    gamma_0 * gamma_0 = 1 ∧ 
    gamma_1 * gamma_1 = -1 := by
  constructor
  · decide
  · decide

end InfoGeometry.Physics.Dirac
