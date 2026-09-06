import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-!
# UHF Boundary Exact Sequence

This module formalizes the concrete representation of the Cuntz isometries
and the nilpotent boundary differential on the Cantor boundary function space `(ℕ → Bool) → ℂ`.

We prove that the resulting Hodge-Dirac Laplacian resolves exactly to the Identity:
`Δ = ∂ ∂* + ∂* ∂ = Id`
proving the exactness of the boundary sequence.
-/

noncomputable section

namespace InfoGeometry.Canonical.UHFBoundaryExactSequence

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CuntzCantorBoundaryShift

/-- Concrete left Cuntz isometry acting on functions on the Cantor boundary. -/
def S_L_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  fun x => if x 0 = false then f (tail x) else 0

/-- Concrete right Cuntz isometry acting on functions on the Cantor boundary. -/
def S_R_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  fun x => if x 0 = true then f (tail x) else 0

/-- Pullback of the left branch map (concrete S_L^* operator). -/
def star_S_L_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  fun x => f (prependBit false x)

/-- Pullback of the right branch map (concrete S_R^* operator). -/
def star_S_R_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  fun x => f (prependBit true x)

theorem star_S_L_op_S_L_op (f : (ℕ → Bool) → ℂ) :
    star_S_L_op (S_L_op f) = f := by
  funext x
  simp [star_S_L_op, S_L_op, tail_prependBit]

theorem star_S_R_op_S_R_op (f : (ℕ → Bool) → ℂ) :
    star_S_R_op (S_R_op f) = f := by
  funext x
  simp [star_S_R_op, S_R_op, tail_prependBit]

theorem star_S_L_op_S_R_op (f : (ℕ → Bool) → ℂ) :
    star_S_L_op (S_R_op f) = 0 := by
  funext x
  simp [star_S_L_op, S_R_op, prependBit]

theorem star_S_R_op_S_L_op (f : (ℕ → Bool) → ℂ) :
    star_S_R_op (S_L_op f) = 0 := by
  funext x
  simp [star_S_R_op, S_L_op, prependBit]

theorem cuntz_partition_op (f : (ℕ → Bool) → ℂ) :
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
def UHF_boundary_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  S_L_op (star_S_R_op f)

/-- The adjoint boundary differential $\partial^*$ acting on Cantor boundary functions. -/
def star_UHF_boundary_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  S_R_op (star_S_L_op f)

def S_L_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) where
  toFun := S_L_op
  map_add' := by
    intro f g
    funext x
    by_cases h : x 0 = false <;> simp [S_L_op, h]
  map_smul' := by
    intro c f
    funext x
    by_cases h : x 0 = false <;> simp [S_L_op, h]

def S_R_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) where
  toFun := S_R_op
  map_add' := by
    intro f g
    funext x
    by_cases h : x 0 = true <;> simp [S_R_op, h]
  map_smul' := by
    intro c f
    funext x
    by_cases h : x 0 = true <;> simp [S_R_op, h]

def star_S_L_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) where
  toFun := star_S_L_op
  map_add' := by
    intro f g
    funext x
    rfl
  map_smul' := by
    intro c f
    funext x
    rfl

def star_S_R_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) where
  toFun := star_S_R_op
  map_add' := by
    intro f g
    funext x
    rfl
  map_smul' := by
    intro c f
    funext x
    rfl

def UHF_boundary_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) :=
  S_L_op_linear.comp star_S_R_op_linear

def star_UHF_boundary_op_linear : Module.End ℂ ((ℕ → Bool) → ℂ) :=
  S_R_op_linear.comp star_S_L_op_linear

@[simp]
theorem UHF_boundary_op_linear_apply (f : (ℕ → Bool) → ℂ) :
    UHF_boundary_op_linear f = UHF_boundary_op f :=
  rfl

@[simp]
theorem star_UHF_boundary_op_linear_apply (f : (ℕ → Bool) → ℂ) :
    star_UHF_boundary_op_linear f = star_UHF_boundary_op f :=
  rfl

theorem UHF_boundary_op_sq_zero (f : (ℕ → Bool) → ℂ) :
    UHF_boundary_op (UHF_boundary_op f) = 0 := by
  funext x
  dsimp [UHF_boundary_op, S_L_op, star_S_R_op]
  by_cases h : x 0 = false
  · simp [h]
  · simp [h]

theorem star_UHF_boundary_op_sq_zero (f : (ℕ → Bool) → ℂ) :
    star_UHF_boundary_op (star_UHF_boundary_op f) = 0 := by
  funext x
  dsimp [star_UHF_boundary_op, S_R_op, star_S_L_op]
  by_cases h : x 0 = true
  · simp [h]
  · simp [h]

theorem UHF_boundary_op_linear_sq_zero :
    UHF_boundary_op_linear.comp UHF_boundary_op_linear = 0 := by
  apply LinearMap.ext
  intro f
  simpa using UHF_boundary_op_sq_zero f

theorem star_UHF_boundary_op_linear_sq_zero :
    star_UHF_boundary_op_linear.comp star_UHF_boundary_op_linear = 0 := by
  apply LinearMap.ext
  intro f
  simpa using star_UHF_boundary_op_sq_zero f

/-- The concrete Hodge-Dirac Laplacian on the Cantor boundary. -/
def UHF_Laplacian_op (f : (ℕ → Bool) → ℂ) : (ℕ → Bool) → ℂ :=
  UHF_boundary_op (star_UHF_boundary_op f) + star_UHF_boundary_op (UHF_boundary_op f)

theorem UHF_Laplacian_op_eq_id (f : (ℕ → Bool) → ℂ) :
    UHF_Laplacian_op f = f := by
  funext x
  dsimp [UHF_Laplacian_op, UHF_boundary_op, star_UHF_boundary_op]
  have hL : (star_S_R_op (S_R_op (star_S_L_op f))) = star_S_L_op f := by
    exact star_S_R_op_S_R_op (star_S_L_op f)
  have hR : (star_S_L_op (S_L_op (star_S_R_op f))) = star_S_R_op f := by
    exact star_S_L_op_S_L_op (star_S_R_op f)
  rw [hL, hR]
  exact congrFun (cuntz_partition_op f) x

theorem UHF_boundary_anticommutator_eq_id (f : (ℕ → Bool) → ℂ) :
    UHF_boundary_op (star_UHF_boundary_op f) +
        star_UHF_boundary_op (UHF_boundary_op f) = f :=
  UHF_Laplacian_op_eq_id f

theorem UHF_boundary_linear_anticommutator_eq_id :
    UHF_boundary_op_linear.comp star_UHF_boundary_op_linear +
        star_UHF_boundary_op_linear.comp UHF_boundary_op_linear =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  simpa [UHF_Laplacian_op] using UHF_Laplacian_op_eq_id f

end InfoGeometry.Canonical.UHFBoundaryExactSequence

end noncomputable section
