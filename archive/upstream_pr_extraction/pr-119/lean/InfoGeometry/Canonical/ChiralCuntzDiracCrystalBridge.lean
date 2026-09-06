import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.ChiralCuntzDiracCrystalBridge

/-- **Definition**: Chiral Cuntz Sublattice Generators S+, S- obeying Isometry and Range Orthogonality. -/
structure ChiralCuntzSublattice (R : Type*) [Ring R] where
  Splus : R
  Sminus : R
  Splus_star : R
  Sminus_star : R
  isometry_plus : Splus_star * Splus = 1
  isometry_minus : Sminus_star * Sminus = 1
  ortho_pm : Splus_star * Sminus = 0
  ortho_mp : Sminus_star * Splus = 0

namespace ChiralCuntzSublattice

variable {R : Type*} [Ring R] (c : ChiralCuntzSublattice R)

/-- **Definition**: Sublattice Projections e+ = S+ S+*, e- = S- S-*. -/
def ePlus : R := c.Splus * c.Splus_star
def eMinus : R := c.Sminus * c.Sminus_star

/-- **Definition**: Pseudo-Spin Pauli Z Operator σ_z = e+ - e-. -/
def sigmaZ : R :=
  c.ePlus - c.eMinus

/-- **Theorem**: Sublattice Projection Orthogonality e+ e- = 0 and e- e+ = 0. -/
theorem projections_ortho :
    c.ePlus * c.eMinus = 0 ∧ c.eMinus * c.ePlus = 0 := by
  constructor
  · dsimp [ePlus, eMinus]
    calc c.Splus * c.Splus_star * (c.Sminus * c.Sminus_star)
      _ = c.Splus * (c.Splus_star * c.Sminus) * c.Sminus_star := by noncomm_ring
      _ = c.Splus * 0 * c.Sminus_star := by rw [c.ortho_pm]
      _ = 0 := by noncomm_ring
  · dsimp [ePlus, eMinus]
    calc c.Sminus * c.Sminus_star * (c.Splus * c.Splus_star)
      _ = c.Sminus * (c.Sminus_star * c.Splus) * c.Splus_star := by noncomm_ring
      _ = c.Sminus * 0 * c.Splus_star := by rw [c.ortho_mp]
      _ = 0 := by noncomm_ring

/-- **Theorem**: Sublattice Projection Idempotency e+² = e+, e-² = e-. -/
theorem projections_idempotent :
    c.ePlus * c.ePlus = c.ePlus ∧ c.eMinus * c.eMinus = c.eMinus := by
  constructor
  · dsimp [ePlus]
    calc c.Splus * c.Splus_star * (c.Splus * c.Splus_star)
      _ = c.Splus * (c.Splus_star * c.Splus) * c.Splus_star := by noncomm_ring
      _ = c.Splus * 1 * c.Splus_star := by rw [c.isometry_plus]
      _ = c.Splus * c.Splus_star := by noncomm_ring
  · dsimp [eMinus]
    calc c.Sminus * c.Sminus_star * (c.Sminus * c.Sminus_star)
      _ = c.Sminus * (c.Sminus_star * c.Sminus) * c.Sminus_star := by noncomm_ring
      _ = c.Sminus * 1 * c.Sminus_star := by rw [c.isometry_minus]
      _ = c.Sminus * c.Sminus_star := by noncomm_ring

/-- **Theorem**: Pseudo-Spin Pauli Z Square Identity (σ_z² = e+ + e-). -/
theorem sigmaZ_sq :
    c.sigmaZ * c.sigmaZ = c.ePlus + c.eMinus := by
  have h_ortho := c.projections_ortho
  have h_id := c.projections_idempotent
  dsimp [sigmaZ]
  calc (c.ePlus - c.eMinus) * (c.ePlus - c.eMinus)
    _ = c.ePlus * c.ePlus - c.ePlus * c.eMinus - c.eMinus * c.ePlus + c.eMinus * c.eMinus := by noncomm_ring
    _ = c.ePlus - 0 - 0 + c.eMinus := by rw [h_id.1, h_id.2, h_ortho.1, h_ortho.2]
    _ = c.ePlus + c.eMinus := by noncomm_ring

end ChiralCuntzSublattice

end InfoGeometry.Canonical.ChiralCuntzDiracCrystalBridge
