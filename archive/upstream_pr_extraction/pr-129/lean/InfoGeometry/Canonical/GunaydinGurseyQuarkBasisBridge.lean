import InfoGeometry.Algebra.ZornVectorMatrix

/-!
# The Günaydin-Gürsey 1973 Split Octonion Quark Basis

This module provides the formal bridge to the classical paper:
"Quark structure and octonions"
M. Günaydin and F. Gürsey, J. Math. Phys. 14, 1651 (1973)

We explicitly realize the split octonion basis (Eq. 2.5) representing the 
quark/antiquark internal symmetry states ($u_0, u_0^*, u_i, u_i^*$) 
using the canonical Zorn Vector Matrix formalism established in the repository.

## Mapping (Appendix B of Günaydin-Gürsey 1973):
* $u_0 = E_{22}$
* $u_0^* = E_{11}$
* $u_i = V_i$ (Lower off-diagonal vector)
* $u_i^* = -U_i$ (Upper off-diagonal vector)
-/

namespace InfoGeometry.Canonical.GunaydinGursey

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.ZornVec3

variable {R : Type*} [CommRing R]

/-- The antiquark core projector $u_0^*$ -/
def uStarZero : ZornVectorMatrix R := E11

/-- The quark core projector $u_0$ -/
def uZero : ZornVectorMatrix R := E22

/-- The quark states $u_i$ -/
def u (i : Fin 3) : ZornVectorMatrix R := V i

/-- The antiquark states $u_i^*$ -/
def uStar (i : Fin 3) : ZornVectorMatrix R := neg (U i)

/-!
## Multiplication Table (Günaydin-Gürsey Eq. 2.5)
We prove that the canonical Zorn product exactly reproduces the 
split octonion multiplication table for the quark states.
-/

/-- $u_i u_0 = 0$ -/
theorem u_mul_uZero (i : Fin 3) : mul (u i : ZornVectorMatrix R) uZero = zero := by
  ext <;> simp [u, uZero, V, E22, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_i u_0^* = u_i$ -/
theorem u_mul_uStarZero (i : Fin 3) : mul (u i : ZornVectorMatrix R) uStarZero = u i := by
  ext <;> simp [u, uStarZero, V, E11, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_0 u_i = u_i$ -/
theorem uZero_mul_u (i : Fin 3) : mul (uZero : ZornVectorMatrix R) (u i) = u i := by
  ext <;> simp [u, uZero, V, E22, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_0^* u_i = 0$ -/
theorem uStarZero_mul_u (i : Fin 3) : mul (uStarZero : ZornVectorMatrix R) (u i) = zero := by
  ext <;> simp [u, uStarZero, V, E11, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_0^2 = u_0$ -/
theorem uZero_sq : mul (uZero : ZornVectorMatrix R) uZero = uZero := by
  ext <;> simp [uZero, E22, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $(u_0^*)^2 = u_0^*$ -/
theorem uStarZero_sq : mul (uStarZero : ZornVectorMatrix R) uStarZero = uStarZero := by
  ext <;> simp [uStarZero, E11, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_0 u_0^* = 0$ -/
theorem uZero_mul_uStarZero : mul (uZero : ZornVectorMatrix R) uStarZero = zero := by
  ext <;> simp [uZero, uStarZero, E22, E11, mul, zero, ZornVec3.dot, ZornVec3.cross]

/-- $u_0^* u_0 = 0$ -/
theorem uStarZero_mul_uZero : mul (uStarZero : ZornVectorMatrix R) uZero = zero := by
  ext <;> simp [uZero, uStarZero, E22, E11, mul, zero, ZornVec3.dot, ZornVec3.cross]

end InfoGeometry.Canonical.GunaydinGursey
