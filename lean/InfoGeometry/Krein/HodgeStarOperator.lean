/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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

/-- The Krein-conjugate of a differential operator. -/
def hodgeCodifferential (d : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  hodgeStar V ∘ₗ d ∘ₗ hodgeStar V


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

/-- The `+1` eigenspace projector of the Krein-induced involution. -/
noncomputable def hodgeProjectorPlus : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + hodgeStar V)

/-- The `-1` eigenspace projector of the Krein-induced involution. -/
noncomputable def hodgeProjectorMinus : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - hodgeStar V)


theorem hodgeProjectorPlus_sq :
    hodgeProjectorPlus V ∘ₗ hodgeProjectorPlus V = hodgeProjectorPlus V := by
  ext x
  simp [hodgeProjectorPlus, LinearMap.comp_apply, hodge_star_involutive V]
  module


theorem hodgeProjectorMinus_sq :
    hodgeProjectorMinus V ∘ₗ hodgeProjectorMinus V = hodgeProjectorMinus V := by
  ext x
  simp [hodgeProjectorMinus, LinearMap.comp_apply, hodge_star_involutive V]
  module


theorem hodgeProjectorPlus_comp_minus :
    hodgeProjectorPlus V ∘ₗ hodgeProjectorMinus V = 0 := by
  ext x
  simp [hodgeProjectorPlus, hodgeProjectorMinus,
    LinearMap.comp_apply, hodge_star_involutive V]
  module


theorem hodgeProjectorMinus_comp_plus :
    hodgeProjectorMinus V ∘ₗ hodgeProjectorPlus V = 0 := by
  ext x
  simp [hodgeProjectorPlus, hodgeProjectorMinus,
    LinearMap.comp_apply, hodge_star_involutive V]
  module


theorem hodgeProjectorPlus_add_minus :
    hodgeProjectorPlus V + hodgeProjectorMinus V = LinearMap.id := by
  ext x
  simp [hodgeProjectorPlus, hodgeProjectorMinus]
  module


theorem hodgeLaplacian_commutes_hodgeProjectorPlus (d : V →ₗ[ℝ] V) :
    hodgeLaplacian V d ∘ₗ hodgeProjectorPlus V =
      hodgeProjectorPlus V ∘ₗ hodgeLaplacian V d := by
  ext x
  simp [hodgeProjectorPlus, LinearMap.comp_apply,
    laplacian_commutes_hodge V d]


theorem hodgeLaplacian_commutes_hodgeProjectorMinus (d : V →ₗ[ℝ] V) :
    hodgeLaplacian V d ∘ₗ hodgeProjectorMinus V =
      hodgeProjectorMinus V ∘ₗ hodgeLaplacian V d := by
  ext x
  simp [hodgeProjectorMinus, LinearMap.comp_apply,
    laplacian_commutes_hodge V d]

end InfoGeometry.Krein.HodgeStarOperator
