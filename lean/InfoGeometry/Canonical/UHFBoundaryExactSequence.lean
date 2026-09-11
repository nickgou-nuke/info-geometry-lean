import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# UHF Boundary Exact Sequence

This module formalizes the concrete representation of the Cuntz isometries
and the nilpotent boundary differential on the Cantor boundary function space `CantorBoundary → ℂ`.

We prove that the resulting Hodge-Dirac Laplacian resolves exactly to the Identity:
`Δ = ∂ ∂* + ∂* ∂ = Id`
proving the exactness of the boundary sequence.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryExactSequence

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- Concrete left Cuntz isometry acting on functions on the Cantor boundary. -/
def S_L_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  fun x => if x 0 = false then f (tail x) else 0

/-- Concrete right Cuntz isometry acting on functions on the Cantor boundary. -/
def S_R_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  fun x => if x 0 = true then f (tail x) else 0

/-- Pullback of the left branch map (concrete S_L^* operator). -/
def star_S_L_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  fun x => f (prependBit false x)

/-- Pullback of the right branch map (concrete S_R^* operator). -/
def star_S_R_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  fun x => f (prependBit true x)

theorem star_S_L_op_S_L_op (f : CantorBoundary → ℂ) :
    star_S_L_op (S_L_op f) = f := by
  funext x
  simp [star_S_L_op, S_L_op, tail_prependBit]

theorem star_S_R_op_S_R_op (f : CantorBoundary → ℂ) :
    star_S_R_op (S_R_op f) = f := by
  funext x
  simp [star_S_R_op, S_R_op, tail_prependBit]

theorem star_S_L_op_S_R_op (f : CantorBoundary → ℂ) :
    star_S_L_op (S_R_op f) = 0 := by
  funext x
  simp [star_S_L_op, S_R_op, prependBit]

theorem star_S_R_op_S_L_op (f : CantorBoundary → ℂ) :
    star_S_R_op (S_L_op f) = 0 := by
  funext x
  simp [star_S_R_op, S_L_op, prependBit]

theorem cuntz_partition_op (f : CantorBoundary → ℂ) :
    S_L_op (star_S_L_op f) + S_R_op (star_S_R_op f) = f := by
  funext x
  dsimp [S_L_op, S_R_op, star_S_L_op, star_S_R_op]
  by_cases h : x 0 = false
  · simp [h, prependBit_tail_of_head]
  · have h_true : x 0 = true := by
      cases hx : x 0
      · contradiction
      · rfl
    simp [h_true, prependBit_tail_of_head]

/-- UHF boundary differential $\partial$ acting on Cantor boundary functions. -/
def UHF_boundary_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  S_L_op (star_S_R_op f)

/-- The adjoint boundary differential $\partial^*$ acting on Cantor boundary functions. -/
def star_UHF_boundary_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  S_R_op (star_S_L_op f)

theorem UHF_boundary_op_sq_zero (f : CantorBoundary → ℂ) :
    UHF_boundary_op (UHF_boundary_op f) = 0 := by
  funext x
  dsimp [UHF_boundary_op, S_L_op, star_S_R_op]
  by_cases h : x 0 = false
  · simp [h]
  · simp [h]

/-- The concrete Hodge-Dirac Laplacian on the Cantor boundary. -/
def UHF_Laplacian_op (f : CantorBoundary → ℂ) : CantorBoundary → ℂ :=
  UHF_boundary_op (star_UHF_boundary_op f) + star_UHF_boundary_op (UHF_boundary_op f)

theorem UHF_Laplacian_op_eq_id (f : CantorBoundary → ℂ) :
    UHF_Laplacian_op f = f := by
  funext x
  dsimp [UHF_Laplacian_op, UHF_boundary_op, star_UHF_boundary_op]
  have hL : (star_S_R_op (S_R_op (star_S_L_op f))) = star_S_L_op f := by
    exact star_S_R_op_S_R_op (star_S_L_op f)
  have hR : (star_S_L_op (S_L_op (star_S_R_op f))) = star_S_R_op f := by
    exact star_S_L_op_S_L_op (star_S_R_op f)
  rw [hL, hR]
  exact congrFun (cuntz_partition_op f) x

end InfoGeometry.Canonical.UHFBoundaryExactSequence

end noncomputable section
