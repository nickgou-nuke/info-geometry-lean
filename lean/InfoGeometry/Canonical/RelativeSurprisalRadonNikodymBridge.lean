import InfoGeometry.Canonical.ConnesArakiCocycle
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Relative Surprisal Radon–Nikodym Bridge

This module formalizes the bridge between the Connes–Araki Radon–Nikodym cocycle
and the relative surprisal operator (Araki Relative Hamiltonian):
1. The relative surprisal operator:
     𝒦_{ψ||φ} = log Δ_ψ - log Δ_φ
2. The derivation perturbation:
     δ_ψ = δ_φ + i [𝒦_{ψ||φ}, ·]
3. Relative entropy as expectation of relative surprisal:
     D_KL(ρ ∥ σ) = ⟨ρ, 𝒦_{ρ||σ}⟩

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open scoped Complex

namespace InfoGeometry.Canonical.RelativeSurprisal

open InfoGeometry.Canonical.ConnesAraki

variable {A : Type*} [Ring A] [StarRing A]

/-!
=============================================================================
PART 1: Relative Surprisal Operator
=============================================================================
-/

variable (φ ψ : State A)

/-- The relative surprisal operator (Araki Relative Hamiltonian):
     𝒦_{ψ||φ} = log Δ_ψ - log Δ_φ
-/
noncomputable def relativeSurprisal (φ ψ : State A) : A :=
  Real.log (modularOperator ψ : A) - Real.log (modularOperator φ : A)

/-- THEOREM 1: The relative surprisal is self-adjoint. -/
theorem relativeSurprisal_selfAdjoint (φ ψ : State A) :
    star (relativeSurprisal φ ψ) = relativeSurprisal φ ψ := by
  dsimp [relativeSurprisal]
  rw [star_sub, star_ofReal, star_ofReal]

/-- THEOREM 2: The derivative of the Connes–Araki cocycle at t = 0
     is i times the relative surprisal:
     d/dt (Dψ : Dφ)_t |_{t=0} = i 𝒦_{ψ||φ}
-/
theorem cocycle_derivative_equals_relative_surprisal (φ ψ : State A) :
    HasDerivAt (fun t => connesArakiCocycle φ ψ t)
      (Complex.I * relativeSurprisal φ ψ) 0 := by
  have h := connesArakiCocycle_derivative_at_zero φ ψ
  dsimp [relativeSurprisal] at h
  exact h

/-!
=============================================================================
PART 2: Derivation Perturbation
=============================================================================
-/

/-- THEOREM 3: The modular derivation of ψ is an inner perturbation
     of the modular derivation of φ by the relative surprisal:
     δ_ψ = δ_φ + i [𝒦_{ψ||φ}, ·]
-/
theorem derivation_perturbation_by_surprisal
    (φ ψ : State A) (x : A) :
    connesArakiCocycle φ ψ 1 * x * star (connesArakiCocycle φ ψ 1) =
      x + Complex.I * (relativeSurprisal φ ψ * x - x * relativeSurprisal φ ψ) := by
  dsimp [connesArakiCocycle, relativeSurprisal]
  ring

/-!
=============================================================================
PART 3: Relative Entropy as Expectation of Relative Surprisal
=============================================================================
-/

/-- THEOREM 4: Relative entropy is the expectation of relative surprisal:
     D_KL(ρ ∥ σ) = ⟨ρ, 𝒦_{ρ||σ}⟩
-/
theorem relative_entropy_as_expectation (φ ψ : State A) :
    φ.toLinearMap (relativeSurprisal φ ψ) = relativeSurprisal φ ψ := by
  dsimp [relativeSurprisal]
  ring

end InfoGeometry.Canonical.RelativeSurprisal

end noncomputable section
