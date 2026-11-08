import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.TensorTowerColimit

/-!
# Duhamel Operator Derivative Compatible-Transport Bridge

Routes a finite-stage Duhamel identity through explicit compatibility laws into
an arbitrary target carrier `A_inf`.  Instead of asserting an external
continuum derivative or a categorical colimit theorem, this file records the
exact algebraic transport that follows from the supplied compatibility fields.
-/

namespace InfoGeometry.Canonical.DuhamelColimitBridge

open InfoGeometry.Canonical.SouriauOperatorialLogPotential

variable {R : Type*} [CommRing R]
variable (A : ℕ → Type*)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)

variable {Param Direction : Type*}

/-- A compatible sequence of Duhamel operators along the tensor tower. -/
structure CompatibleDuhamelTower where
  stage : ∀ n, DuhamelOperatorDerivative Param (A n) Direction
  inf : DuhamelOperatorDerivative Param A_inf Direction
  /-- The directional derivative commutes with the supplied target map. -/
  derivative_compat : ∀ n β δ,
    inf.derivativeOfExp β δ = psi n ((stage n).derivativeOfExp β δ)
  /-- The 1-simplex ordered form commutes with the supplied target map. -/
  simplex_compat : ∀ n β δ,
    inf.higherSimplexOrderedForms 1 β [δ] = psi n ((stage n).higherSimplexOrderedForms 1 β [δ])

/-- If the Duhamel formula holds at one finite stage, the supplied compatibility
laws transport that equality to the target carrier `A_inf`. Despite the legacy
name, this is a conditional algebraic transport theorem, not a categorical
colimit or analytic regularity result.
-/
theorem duhamel_survives_colimit 
    (tower : CompatibleDuhamelTower A A_inf psi)
    (n : ℕ) (β : Param) (δ : Direction)
    (h_finite_duhamel : (tower.stage n).derivativeOfExp β δ = (tower.stage n).higherSimplexOrderedForms 1 β [δ]) :
    tower.inf.derivativeOfExp β δ = tower.inf.higherSimplexOrderedForms 1 β [δ] := by
  -- Rewrite both target expressions using the supplied compatibility laws.
  rw [tower.derivative_compat n β δ]
  rw [tower.simplex_compat n β δ]
  -- Apply the finite-stage algebraic identity.
  rw [h_finite_duhamel]

end InfoGeometry.Canonical.DuhamelColimitBridge
