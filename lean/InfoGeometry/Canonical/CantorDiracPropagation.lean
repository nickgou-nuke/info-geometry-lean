import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFBoundaryExactSequence
import InfoGeometry.Canonical.UHFColimitRepresentationBridge
import InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-!
# Dirac Operator and Causal Propagation on the Cantor Boundary

This module defines the boundary Dirac operator, proves that its algebraic square is the
identity (Hodge-Dirac Laplacian is unit), and formalizes the boundary Dirac equation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorDiracPropagation

open InfoGeometry.Canonical.UHFBoundaryExactSequence
open InfoGeometry.Canonical.UHFColimitRepresentationBridge
open InfoGeometry.Canonical.OmegaBoundaryRepresentation

/-- The Cuntz partition identity as a linear operator equation. -/
theorem cuntz_partition_linear :
    S_L_linear * star_S_L_linear + S_R_linear * star_S_R_linear = 1 := by
  ext f x
  change (S_L_op (star_S_L_op f) + S_R_op (star_S_R_op f)) x = f x
  rw [cuntz_partition_op]

/-- The boundary Dirac operator `D = ∂ + ∂*`. -/
def DiracOp : CantorOp :=
  (S_L_linear * star_S_R_linear) + (S_R_linear * star_S_L_linear)

/-- The square of the Dirac operator is the identity (Hodge-Dirac Laplacian Δ = 1). -/
theorem DiracOp_sq_eq_one : DiracOp * DiracOp = 1 := by
  dsimp [DiracOp]
  rw [add_mul, mul_add, mul_add]
  rw [S_L_star_S_R_nilpotent, zero_add]
  rw [S_R_star_S_L_nilpotent, add_zero]
  rw [S_L_star_S_R_mul_S_R_star_S_L, S_R_star_S_L_mul_S_L_star_S_R]
  exact cuntz_partition_linear

/-- Massless Dirac Equation eigenstates.
    Since `D^2 = 1`, the only possible eigenvalues of `DiracOp` are 1 and -1. -/
def IsDiracChiralState (f : CantorSpace) (eigenval : ℂ) : Prop :=
  DiracOp f = eigenval • f

/-- The Dirac equation enforces that the chiral eigenvalues must square to 1. -/
theorem Dirac_eigenvalue_sq_eq_one {f : CantorSpace} {eigenval : ℂ}
    (hf_nonzero : f ≠ 0) (h_dirac : IsDiracChiralState f eigenval) :
    eigenval^2 = 1 := by
  dsimp [IsDiracChiralState] at h_dirac
  have h_sq : (DiracOp * DiracOp) f = (eigenval^2) • f := by
    calc
      (DiracOp * DiracOp) f = DiracOp (DiracOp f) := rfl
      _ = DiracOp (eigenval • f) := by rw [h_dirac]
      _ = eigenval • DiracOp f := by rw [LinearMap.map_smul]
      _ = eigenval • (eigenval • f) := by rw [h_dirac]
      _ = (eigenval * eigenval) • f := by rw [smul_smul]
      _ = (eigenval^2) • f := by rw [sq]
  rw [DiracOp_sq_eq_one] at h_sq
  -- We have f = eigenval^2 • f. We want eigenval^2 • f = 1 • f
  have h_eq : eigenval^2 • f = (1 : ℂ) • f := by
    rw [one_smul]
    exact h_sq.symm
  exact smul_left_injective ℂ hf_nonzero h_eq

end InfoGeometry.Canonical.CantorDiracPropagation

end noncomputable section
