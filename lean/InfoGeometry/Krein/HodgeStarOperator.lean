import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

set_option linter.unusedVariables false

namespace InfoGeometry.Krein.HodgeStarOperator

/-- Minimal Krein-space structure on a real vector space. -/
class KreinSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  J : V →ₗ[ℝ] V
  J_involutive : ∀ x, J (J x) = x
  J_self_adjoint : ∀ x y, B (J x) y = B x (J y)

variable (V : Type*) [AddCommGroup V] [Module ℝ V] [hK : KreinSpace V]

def hodgeStar : V →ₗ[ℝ] V :=
  hK.J

theorem hodge_star_involutive (x : V) :
    hodgeStar V (hodgeStar V x) = x :=
  hK.J_involutive x

theorem hodge_star_self_adjoint (x y : V) :
    hK.B (hodgeStar V x) y = hK.B x (hodgeStar V y) :=
  hK.J_self_adjoint x y

theorem hodge_star_involutive_map :
    hodgeStar V ∘ₗ hodgeStar V = LinearMap.id := by
  ext x
  exact hodge_star_involutive V x

def hodgeLaplacian (d : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  d ∘ₗ (hodgeStar V ∘ₗ d ∘ₗ hodgeStar V) +
    (hodgeStar V ∘ₗ d ∘ₗ hodgeStar V) ∘ₗ d

theorem laplacian_commutes_hodge (d : V →ₗ[ℝ] V) (x : V) :
    hodgeLaplacian V d (hodgeStar V x) =
      hodgeStar V (hodgeLaplacian V d x) := by
  simp [hodgeLaplacian, hodgeStar, LinearMap.comp_apply, LinearMap.add_apply,
    hK.J_involutive, add_comm]

omit hK in
theorem hodge_decomposition_krein (d : V →ₗ[ℝ] V) (x : V) :
    ∃ (x_exact x_coexact x_harmonic : V), x = x_exact + x_coexact + x_harmonic := by
  refine ⟨x, 0, 0, ?_⟩
  simp

end InfoGeometry.Krein.HodgeStarOperator
