import Mathlib.Tactic
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
def DiracOp : (Module.End ℂ ((ℕ → Bool) → ℂ)) :=
  (S_L_linear * star_S_R_linear) + (S_R_linear * star_S_L_linear)

/-- The square of the Dirac operator is the identity (Hodge-Dirac Laplacian Δ = 1). -/
theorem DiracOp_sq_eq_one : DiracOp * DiracOp = 1 := by
  dsimp [DiracOp]
  rw [add_mul, mul_add, mul_add]
  rw [S_L_star_S_R_nilpotent, zero_add]
  rw [S_R_star_S_L_nilpotent, add_zero]
  rw [S_L_star_S_R_mul_S_R_star_S_L, S_R_star_S_L_mul_S_L_star_S_R]
  exact cuntz_partition_linear

theorem DiracOp_apply_apply (f : ((ℕ → Bool) → ℂ)) :
    DiracOp (DiracOp f) = f := by
  have h := congrArg (fun T : (Module.End ℂ ((ℕ → Bool) → ℂ)) => T f) DiracOp_sq_eq_one
  simpa using h

def diracPlusComponent (f : ((ℕ → Bool) → ℂ)) : ((ℕ → Bool) → ℂ) :=
  (1 / 2 : ℂ) • (f + DiracOp f)

def diracMinusComponent (f : ((ℕ → Bool) → ℂ)) : ((ℕ → Bool) → ℂ) :=
  (1 / 2 : ℂ) • (f - DiracOp f)

theorem diracPlusComponent_add_diracMinusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    diracPlusComponent f + diracMinusComponent f = f := by
  dsimp [diracPlusComponent, diracMinusComponent]
  module

theorem DiracOp_diracPlusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    DiracOp (diracPlusComponent f) = diracPlusComponent f := by
  dsimp [diracPlusComponent]
  rw [map_smul, map_add, DiracOp_apply_apply]
  module

theorem DiracOp_diracMinusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    DiracOp (diracMinusComponent f) = -diracMinusComponent f := by
  dsimp [diracMinusComponent]
  rw [map_smul, map_sub, DiracOp_apply_apply]
  module

theorem diracPlusComponent_idempotent
    (f : ((ℕ → Bool) → ℂ)) :
    diracPlusComponent (diracPlusComponent f) = diracPlusComponent f := by
  change (1 / 2 : ℂ) •
      (diracPlusComponent f + DiracOp (diracPlusComponent f)) =
    diracPlusComponent f
  rw [DiracOp_diracPlusComponent]
  module

theorem diracMinusComponent_idempotent
    (f : ((ℕ → Bool) → ℂ)) :
    diracMinusComponent (diracMinusComponent f) = diracMinusComponent f := by
  change (1 / 2 : ℂ) •
      (diracMinusComponent f - DiracOp (diracMinusComponent f)) =
    diracMinusComponent f
  rw [DiracOp_diracMinusComponent]
  module

theorem diracPlusComponent_diracMinusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    diracPlusComponent (diracMinusComponent f) = 0 := by
  change (1 / 2 : ℂ) •
      (diracMinusComponent f + DiracOp (diracMinusComponent f)) = 0
  rw [DiracOp_diracMinusComponent]
  module

theorem diracMinusComponent_diracPlusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    diracMinusComponent (diracPlusComponent f) = 0 := by
  change (1 / 2 : ℂ) •
      (diracPlusComponent f - DiracOp (diracPlusComponent f)) = 0
  rw [DiracOp_diracPlusComponent]
  module

theorem diracPlusComponent_sub_diracMinusComponent
    (f : ((ℕ → Bool) → ℂ)) :
    diracPlusComponent f - diracMinusComponent f = DiracOp f := by
  dsimp [diracPlusComponent, diracMinusComponent]
  module

theorem DiracOp_injective : Function.Injective DiracOp := by
  intro f g hfg
  have h := congrArg DiracOp hfg
  simpa only [DiracOp_apply_apply] using h

theorem DiracOp_surjective : Function.Surjective DiracOp := by
  intro f
  exact ⟨DiracOp f, DiracOp_apply_apply f⟩

theorem DiracOp_bijective : Function.Bijective DiracOp :=
  ⟨DiracOp_injective, DiracOp_surjective⟩

/-- Massless Dirac Equation eigenstates.
    Since `D^2 = 1`, the only possible eigenvalues of `DiracOp` are 1 and -1. -/
def IsDiracChiralState (f : ((ℕ → Bool) → ℂ)) (eigenval : ℂ) : Prop :=
  DiracOp f = eigenval • f

theorem diracPlusComponent_isDiracChiralState
    (f : ((ℕ → Bool) → ℂ)) :
    IsDiracChiralState (diracPlusComponent f) 1 := by
  simpa [IsDiracChiralState] using DiracOp_diracPlusComponent f

theorem diracMinusComponent_isDiracChiralState
    (f : ((ℕ → Bool) → ℂ)) :
    IsDiracChiralState (diracMinusComponent f) (-1) := by
  simpa [IsDiracChiralState] using DiracOp_diracMinusComponent f

/-- The Dirac equation enforces that the chiral eigenvalues must square to 1. -/
theorem Dirac_eigenvalue_sq_eq_one {f : ((ℕ → Bool) → ℂ)} {eigenval : ℂ}
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

theorem Dirac_eigenvalue_eq_one_or_neg_one
    {f : ((ℕ → Bool) → ℂ)} {eigenval : ℂ}
    (hf_nonzero : f ≠ 0) (h_dirac : IsDiracChiralState f eigenval) :
    eigenval = 1 ∨ eigenval = -1 := by
  have hsq : eigenval ^ 2 = 1 :=
    Dirac_eigenvalue_sq_eq_one hf_nonzero h_dirac
  have hfactor : (eigenval - 1) * (eigenval + 1) = 0 := by
    calc
      (eigenval - 1) * (eigenval + 1) = eigenval ^ 2 - 1 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    exact sub_eq_zero.mp hminus
  · right
    exact eq_neg_of_add_eq_zero_left hplus

end InfoGeometry.Canonical.CantorDiracPropagation

end noncomputable section
