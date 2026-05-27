import Mathlib

/-!
# InfoGeometry.Canonical.ModularFluxVacuumFunctional

Finite seed:
`ω_{Δ-1}(A) = ⟪Ω, A ((Δ - 1) Ω)⟫`, and if `Δ Ω = Ω` then this vanishes.
-/

namespace InfoGeometry.Canonical.ModularFluxVacuumFunctional

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Centered modular flux operator `Δ - 1`. -/
def modularFlux (Δ : Module.End ℂ E) : Module.End ℂ E :=
  Δ - LinearMap.id

/-- Flux action seen at vector level. -/
def vacuumFluxAction (Ω : E) (A X : Module.End ℂ E) : E :=
  A (X Ω)

/-- If `Δ Ω = Ω`, then `A ((Δ - 1) Ω) = 0` for all test operators `A`. -/
theorem vacuumFluxAction_eq_zero_of_fixed
    (Δ : Module.End ℂ E) (Ω : E)
    (hfix : Δ Ω = Ω) :
    ∀ A : Module.End ℂ E, vacuumFluxAction Ω A (modularFlux Δ) = 0 := by
  intro A
  have hflux : modularFlux Δ Ω = 0 := by
    simp [modularFlux, hfix]
  simp [vacuumFluxAction, hflux]

end Algebraic

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Vector-functional pairing for the centered modular flux. -/
def vacuumFluxFunctional (Ω : E) (A X : Module.End ℂ E) : ℂ :=
  inner ℂ Ω (vacuumFluxAction Ω A X)

/-- Finite vacuum-functional annihilation for fixed vector `Ω`. -/
theorem vacuumFluxFunctional_eq_zero_of_fixed
    (Δ : Module.End ℂ E) (Ω : E)
    (hfix : Δ Ω = Ω) :
    ∀ A : Module.End ℂ E, vacuumFluxFunctional Ω A (modularFlux Δ) = 0 := by
  intro A
  have hact : vacuumFluxAction Ω A (modularFlux Δ) = 0 :=
    vacuumFluxAction_eq_zero_of_fixed (Δ := Δ) (Ω := Ω) hfix A
  simp [vacuumFluxFunctional, hact]

end InnerProduct

end InfoGeometry.Canonical.ModularFluxVacuumFunctional
