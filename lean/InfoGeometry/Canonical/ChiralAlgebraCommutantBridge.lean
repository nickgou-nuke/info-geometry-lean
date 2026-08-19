import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ChiralAlgebraCommutantBridge

/-- **Definition**: Commutant Operator T in A' satisfying [T, A] = 0 for all A in Chiral Algebra. -/
structure ChiralCommutantData (R : Type*) [Ring R] where
  T : R
  ePlus : R
  eMinus : R

def ChiralCommutantLaws {R : Type*} [Ring R]
    (c : ChiralCommutantData R) : Prop :=
  c.T * c.ePlus = c.ePlus * c.T ∧
  c.T * c.eMinus = c.eMinus * c.T

def ChiralCommutant (R : Type*) [Ring R] :=
  {c : ChiralCommutantData R // ChiralCommutantLaws c}

namespace ChiralCommutant

variable {R : Type*} [Ring R] (c : ChiralCommutant R)

/-- **Theorem**: Commutant Operator Preserves Chiral Projection e+ (T e+ = e+ T). -/
theorem commute_ePlus_id :
    c.1.T * c.1.ePlus = c.1.ePlus * c.1.T :=
  c.2.1

/-- **Theorem**: Commutant Operator Preserves Chiral Projection e- (T e- = e- T). -/
theorem commute_eMinus_id :
    c.1.T * c.1.eMinus = c.1.eMinus * c.1.T :=
  c.2.2

/-- **Theorem**: Commutant Preserves Full Chiral Resolution of Identity e+ + e-. -/
theorem commute_resolution :
    c.1.T * (c.1.ePlus + c.1.eMinus) =
      (c.1.ePlus + c.1.eMinus) * c.1.T := by
  calc c.1.T * (c.1.ePlus + c.1.eMinus)
    _ = c.1.T * c.1.ePlus + c.1.T * c.1.eMinus := by noncomm_ring
    _ = c.1.ePlus * c.1.T + c.1.eMinus * c.1.T := by rw [c.2.1, c.2.2]
    _ = (c.1.ePlus + c.1.eMinus) * c.1.T := by noncomm_ring

end ChiralCommutant

end InfoGeometry.Canonical.ChiralAlgebraCommutantBridge
