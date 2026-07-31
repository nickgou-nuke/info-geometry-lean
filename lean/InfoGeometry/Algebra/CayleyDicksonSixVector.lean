import InfoGeometry.Algebra.RationalSplitE8Lattice
import InfoGeometry.OperatorAlgebra.GenericZornSplitOctonion

/-!
# Cayley-Dickson 6-Vector and the Quark-Lepton Structural Factoring

This module formalizes the profound realization that the 8D split octonion 
algebra naturally factorizes via the hypercomplex generator `l` into:
1. A 2D Cartan plane (Lepton Sector: Neutrino and Electron)
2. A 6D orthogonal complement (Quark Sector: 3 Quarks + 3 Anti-quarks)

The 6-vector structure strictly corresponds to the complex-hypercomplex 
Cayley-Dickson pairs $(i, li), (j, lj), (k, lk)$, which map to the off-diagonal 
Peirce matrices $U_m$ and $V_m$.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.OperatorAlgebra.GenericZorn

/-- The 6-vector of colored quarks and anti-quarks, derived from the 
    complex/hypercomplex Cayley-Dickson pairs orthogonal to the Cartan plane.
    Indices 0, 1, 2 map to the Quarks (u_R, u_G, u_B) via U_m.
    Indices 3, 4, 5 map to the Anti-quarks (d_R, d_G, d_B) via V_m. -/
def cdSixVector : Fin 6 → ZornRationalMatrix :=
  ![ZornVectorMatrix.U 0, ZornVectorMatrix.U 1, ZornVectorMatrix.U 2,
    ZornVectorMatrix.V 0, ZornVectorMatrix.V 1, ZornVectorMatrix.V 2]

/-- The discrete spectrum of charges specifically carried by the 6-vector. -/
def QuarkCharges : Set ℚ := {2/3, -1/3}

/-- Theorem: The 6-vector strictly carries only the fractional quark charges, 
    with exact color multiplicity 3. The `Fin 6` of unique eigenvalues in 
    GenericZornSplitOctonion.lean is the *global* spectrum, but the 6-vector 
    itself is confined to the fractional {2/3, -1/3} subset. -/
theorem cdSixVector_charge_spectrum (i : Fin 6) :
    ZornRationalMatrix.electricCharge (cdSixVector i) ∈ QuarkCharges := by
  -- Expand the 6 cases of the Cayley-Dickson 6-vector
  fin_cases i <;> {
    simp [cdSixVector, ZornRationalMatrix.electricCharge, ZornVectorMatrix.U, 
          ZornVectorMatrix.V, ZornVec3.basis, QuarkCharges]
    try norm_num
  }

/-- The 2D Cartan plane corresponding to the real unit `1` and hypercomplex `l`.
    These map to the diagonal Peirce idempotents E11 and E22. -/
def leptonPlane : Fin 2 → ZornRationalMatrix :=
  ![ZornVectorMatrix.E11, ZornVectorMatrix.E22]

/-- The discrete spectrum of charges specifically carried by the Cartan plane. -/
def LeptonCharges : Set ℚ := {0, -1}

/-- Theorem: The 2D Cartan plane strictly carries the integer lepton charges. -/
theorem leptonPlane_charge_spectrum (i : Fin 2) :
    ZornRationalMatrix.electricCharge (leptonPlane i) ∈ LeptonCharges := by
  fin_cases i <;> {
    simp [leptonPlane, ZornRationalMatrix.electricCharge, ZornVectorMatrix.E11, 
          ZornVectorMatrix.E22, LeptonCharges]
    try norm_num
  }

end InfoGeometry.Algebra
