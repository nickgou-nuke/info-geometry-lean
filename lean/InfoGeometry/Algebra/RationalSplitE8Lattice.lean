import InfoGeometry.Algebra.IntegerSplitOctonionOrder
import Mathlib.Tactic

/-!
# Rational Split E8 Lattice and Cartan Charge Quantization

This module defines the parametrical rational owner `ZornRationalMatrix`
and formalizes the Cartan electric charge functional over $\mathbb{Q}$. 
It provides the quantization theorem for fractional charges.
-/

namespace InfoGeometry.Algebra

/-- Parametrized Zorn Carrier over ℚ. -/
abbrev ZornRationalMatrix := ZornVectorMatrix ℚ

namespace ZornRationalMatrix

/-- The canonical embedding of the integer order into the rational carrier. -/
def fromInteger (X : ZornIntegerMatrix) : ZornRationalMatrix :=
  ⟨X.a, fun i => X.v i, fun i => X.w i, X.b⟩

/-- The linear functional defining the Cartan electric charge on the split octonion algebra.
    Derived from the Standard Model particle generation mapping:
    - E11 : Neutrino (Q = 0)
    - E22 : Electron (Q = -1)
    - U_i : Up Quarks (Q = 2/3)
    - V_i : Down Quarks (Q = -1/3) -/
def electricCharge (X : ZornRationalMatrix) : ℚ :=
  - X.b + (2/3 : ℚ) * (X.v 0 + X.v 1 + X.v 2) - (1/3 : ℚ) * (X.w 0 + X.w 1 + X.w 2)

/-- The fundamental fermion states forming the Zorn basis of the algebra. -/
def fermionStates : List ZornRationalMatrix :=
  [ ZornVectorMatrix.E11,
    ZornVectorMatrix.E22,
    ZornVectorMatrix.U 0,
    ZornVectorMatrix.U 1,
    ZornVectorMatrix.U 2,
    ZornVectorMatrix.V 0,
    ZornVectorMatrix.V 1,
    ZornVectorMatrix.V 2 ]

/-- The anti-fermion states (conjugates). -/
def antifermionStates : List ZornRationalMatrix :=
  fermionStates.map ZornVectorMatrix.neg

/-- The complete set of 16 fundamental charge states. -/
def chargeStates : List ZornRationalMatrix :=
  fermionStates ++ antifermionStates

/-- Strict finite image set of the allowed Cartan charges. -/
def AllowedCharges : Set ℚ :=
  {0, -1, 1, 2/3, -2/3, 1/3, -1/3}

/-- 
Absolute contract for Charge Quantization:
The image of the Cartan electric charge functional on the discrete fundamental
states is strictly confined to the standard fractional eigenvalues.
-/
theorem charge_quantized (X : ZornRationalMatrix) (hX : X ∈ chargeStates) :
    electricCharge X ∈ AllowedCharges := by
  -- Expand the membership in the finite list of states
  rcases List.mem_iff_get.mp hX with ⟨i, hi⟩
  -- Re-bind the equality
  have hX_eq : X = chargeStates.get i := hi.symm
  rw [hX_eq]
  -- Evaluate the charge for each finite index
  fin_cases i <;> {
    simp [chargeStates, fermionStates, antifermionStates, electricCharge,
          ZornVectorMatrix.E11, ZornVectorMatrix.E22, ZornVectorMatrix.U, ZornVectorMatrix.V,
          ZornVectorMatrix.neg, ZornVec3.basis, AllowedCharges]
    try norm_num
  }

end ZornRationalMatrix

end InfoGeometry.Algebra
