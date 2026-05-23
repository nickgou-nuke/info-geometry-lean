import InfoGeometry.Thermodynamics.FiniteConnesCocycle

/-!
# Finite Connes transport for network edges

This file connects the finite Connes--Radon--Nikodym cocycle theorem to the
operator-network vocabulary without introducing a field-bearing edge or diamond
structure.

The theorem surface is just the group identity:

`Uψ (s+t) * (Uφ (s+t))⁻¹`
`= (Uψ s * (Uφ s)⁻¹) * (Uφ s * (Uψ t * (Uφ t)⁻¹) * (Uφ s)⁻¹)`.

No analytic Tomita--Takesaki theorem, support projection theory, fluctuation
theorem, or packaged bridge structure is asserted here.
-/

namespace InfoGeometry.Network

open InfoGeometry.Thermodynamics.FiniteConnesCocycle

variable {G : Type*} [Group G]

/--
Canonical finite Connes transport law for network edges.

The source and target modular transports are plain functions `ℝ → G`; their
additive-time laws are explicit hypotheses. The conclusion is the Connes
cocycle law for the concrete relative transport `u_t = Uψ t * (Uφ t)⁻¹`.
-/
theorem connesTransportEdge_cocycle_law
    (Uφ Uψ : ℝ → G)
    (hφ_add : ∀ s t : ℝ, Uφ (s + t) = Uφ s * Uφ t)
    (hψ_add : ∀ s t : ℝ, Uψ (s + t) = Uψ s * Uψ t)
    (s t : ℝ) :
    Uψ (s + t) * (Uφ (s + t))⁻¹ =
      (Uψ s * (Uφ s)⁻¹) *
        (Uφ s * (Uψ t * (Uφ t)⁻¹) * (Uφ s)⁻¹) :=
  finiteConnesFlux_cocycle Uψ Uφ hψ_add hφ_add s t

/-- Canonical finite Connes transport is unit-valued at zero. -/
@[simp]
theorem connesTransportEdge_zero
    (Uφ Uψ : ℝ → G) (hφ_zero : Uφ 0 = 1) (hψ_zero : Uψ 0 = 1) :
    Uψ 0 * (Uφ 0)⁻¹ = 1 :=
  finiteConnesFlux_zero Uψ Uφ hψ_zero hφ_zero

/-- If source and target modular transports agree, the relative transport is trivial. -/
@[simp]
theorem connesTransportEdge_eq_one_of_same
    (Uφ : ℝ → G) (t : ℝ) :
    Uφ t * (Uφ t)⁻¹ = 1 :=
  finiteConnesFlux_eq_one_of_same Uφ t

end InfoGeometry.Network
