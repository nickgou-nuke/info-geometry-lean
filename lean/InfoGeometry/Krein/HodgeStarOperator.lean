import Mathlib.Tactic
import InfoGeometry.Krein.KreinSpace

set_option linter.unusedVariables false
open scoped InnerProductSpace

namespace InfoGeometry.Krein.HodgeStarOperator

open InfoGeometry.Krein

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [hK : InfoGeometry.Krein.KreinSpace V]

def hodgeStar : V →ₗ[ℝ] V :=
  (InfoGeometry.Krein.KreinSpace.J (H := V)).toLinearMap

theorem hodge_star_involutive (x : V) :
    hodgeStar V (hodgeStar V x) = x :=
  by simpa [hodgeStar] using hK.J_invol x

theorem hodge_star_self_adjoint (x y : V) :
    ⟪(hodgeStar V) x, y⟫_ℝ = ⟪x, (hodgeStar V) y⟫_ℝ := by
  simpa [hodgeStar] using hK.J_selfAdj x y

theorem hodge_star_involutive_map :
    hodgeStar V ∘ₗ hodgeStar V = LinearMap.id := by
  ext x
  exact hodge_star_involutive V x

/-! ### Derived codifferential and algebraic Laplacian -/

/-- The Krein-conjugate of a differential operator. -/
def hodgeCodifferential (d : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  hodgeStar V ∘ₗ d ∘ₗ hodgeStar V

def hodgeLaplacian (d : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  d ∘ₗ hodgeCodifferential V d +
    hodgeCodifferential V d ∘ₗ d

theorem hodgeCodifferential_sq_zero
    (d : V →ₗ[ℝ] V)
    (hd : d ∘ₗ d = 0) :
    hodgeCodifferential V d ∘ₗ hodgeCodifferential V d = 0 := by
  ext x
  have hd_apply : ∀ y : V, d (d y) = 0 := by
    intro y
    have h := congrArg (fun f : V →ₗ[ℝ] V => f y) hd
    simpa using h
  simp [hodgeCodifferential, LinearMap.comp_apply,
    hodge_star_involutive V, hd_apply]

theorem hodgeLaplacian_commutes_d
    (d : V →ₗ[ℝ] V)
    (hd : d ∘ₗ d = 0) :
    hodgeLaplacian V d ∘ₗ d = d ∘ₗ hodgeLaplacian V d := by
  ext x
  have hd_apply : ∀ y : V, d (d y) = 0 := by
    intro y
    have h := congrArg (fun f : V →ₗ[ℝ] V => f y) hd
    simpa using h
  simp [hodgeLaplacian, hodgeCodifferential, LinearMap.comp_apply,
    hd_apply, add_comm]

theorem hodgeLaplacian_commutes_codifferential
    (d : V →ₗ[ℝ] V)
    (hd : d ∘ₗ d = 0) :
    hodgeLaplacian V d ∘ₗ hodgeCodifferential V d =
      hodgeCodifferential V d ∘ₗ hodgeLaplacian V d := by
  ext x
  have hd_apply : ∀ y : V, d (d y) = 0 := by
    intro y
    have h := congrArg (fun f : V →ₗ[ℝ] V => f y) hd
    simpa using h
  simp [hodgeLaplacian, hodgeCodifferential, LinearMap.comp_apply,
    hodge_star_involutive V, hd_apply, add_comm]

theorem laplacian_commutes_hodge (d : V →ₗ[ℝ] V) (x : V) :
    hodgeLaplacian V d (hodgeStar V x) =
      hodgeStar V (hodgeLaplacian V d x) := by
  simp [hodgeLaplacian, hodgeStar, LinearMap.comp_apply, LinearMap.add_apply,
    hodgeCodifferential, hK.J_invol, add_comm]

end InfoGeometry.Krein.HodgeStarOperator
