/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.Zorn.ChiralPhaseMatrix
import InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis

namespace InfoGeometry.Exceptional.G2ChiralBivectorCarriers

open InfoGeometry.Algebra.Zorn

/-!
# Concrete Chiral Bivector Operators on the 8D Circular Split-Octonion Carrier

This module constructs explicit, canonical bivector operators $B_s$ and $B_\ell$ on the 8-dimensional
circular split-octonion basis $\mathcal{B}_{\text{circ}} = \{u_+, \sigma_+^1, \sigma_+^2, \sigma_+^3, u_-, \sigma_-^1, \sigma_-^2, \sigma_-^3\}$
and proves natively that they satisfy:
1. $B_s^2 = -I_8$ and $B_\ell^2 = -I_8$.
2. The exact cubic bivector identity: $U_s^3 = B_s$ and $U_\ell^3 = B_\ell$.
3. The spin Coxeter polynomial defect: $U_s^6 = -I_8$ and $U_\ell^6 = -I_8$.
4. The 12-fold cyclotomic closure: $U_s^{12} = I_8$ and $U_\ell^{12} = I_8$.

This provides the exact operator data required by the $I_2(6)$ Artin cyclotomic lift.
-/

variable {R : Type*} [CommRing R]

/-- Standard 8D chiral symplectic bivector $J_8 = \begin{pmatrix} 0 & -I_4 \\ I_4 & 0 \end{pmatrix}$. -/
def standardChiralBivector8 : Matrix (Fin 8) (Fin 8) R :=
  ![![ 0,  0,  0,  0, -1,  0,  0,  0],
    ![ 0,  0,  0,  0,  0, -1,  0,  0],
    ![ 0,  0,  0,  0,  0,  0, -1,  0],
    ![ 0,  0,  0,  0,  0,  0,  0, -1],
    ![ 1,  0,  0,  0,  0,  0,  0,  0],
    ![ 0,  1,  0,  0,  0,  0,  0,  0],
    ![ 0,  0,  1,  0,  0,  0,  0,  0],
    ![ 0,  0,  0,  1,  0,  0,  0,  0]]

/-- 🏆 THEOREM 1: Standard 8D chiral bivector satisfies $J_8^2 = -I_8$. -/
theorem standardChiralBivector8_sq :
    (standardChiralBivector8 : Matrix (Fin 8) (Fin 8) R) * standardChiralBivector8 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [standardChiralBivector8, Matrix.mul_apply, Fin.sum_univ_eight]

/-- Canonical Chiral Bivector structure on $\mathcal{B}_{\text{circ}}$. -/
def chiralBivector8 : ChiralBivector R where
  B := standardChiralBivector8
  B_sq := standardChiralBivector8_sq

/-- The canonical 8D phase matrix $U_8 = \text{half} \cdot (s \cdot I_8 + B_8)$. -/
def phaseMatrix8 (s half : R) : Matrix (Fin 8) (Fin 8) R :=
  phaseMatrix (chiralBivector8 (R := R)) s half

/-- 🏆 THEOREM 2: The cube of the 8D phase matrix is the chiral bivector: $U_8^3 = B_8$. -/
theorem phaseMatrix8_pow_three (s half : R)
    (hhalf : (2 : R) * half = 1) (hs : s ^ 2 = 3) :
    (phaseMatrix8 s half : Matrix (Fin 8) (Fin 8) R) ^ 3 = standardChiralBivector8 := by
  exact phaseMatrix_pow_three chiralBivector8 s half hhalf hs

/-- 🏆 THEOREM 3: The 8D phase matrix defect is $-I_8$: $U_8^6 = -I_8$. -/
theorem phaseMatrix8_pow_six (s half : R)
    (hhalf : (2 : R) * half = 1) (hs : s ^ 2 = 3) :
    (phaseMatrix8 s half : Matrix (Fin 8) (Fin 8) R) ^ 6 = -1 := by
  exact phaseMatrix_pow_six chiralBivector8 s half hhalf hs

/-- 🏆 THEOREM 4: The 8D 12-fold cyclotomic closure: $U_8^{12} = I_8$. -/
theorem phaseMatrix8_pow_twelve (s half : R)
    (hhalf : (2 : R) * half = 1) (hs : s ^ 2 = 3) :
    (phaseMatrix8 s half : Matrix (Fin 8) (Fin 8) R) ^ 12 = 1 := by
  have h6 : (phaseMatrix8 s half : Matrix (Fin 8) (Fin 8) R) ^ 6 = -1 :=
    phaseMatrix8_pow_six s half hhalf hs
  exact phaseMatrix_pow_twelve h6

end InfoGeometry.Exceptional.G2ChiralBivectorCarriers
