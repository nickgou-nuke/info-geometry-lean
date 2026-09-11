import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.EinsteinHilbertPalatiniActionBridge

/-!
# Palatini Boundary Stokes Bridge

This module formalizes the canonical boundary pairing for Palatini gravity via the Stokes theorem
on differential complexes. It establishes:
1. `StokesBoundaryComplex`: differential complex `(Ω², Ω³, Ω⁴, Ω³(∂M))` with `d₃ ∘ d₂ = 0`,
   boundary pullback `i* : Ω³(M) → Ω³(∂M)`, and Stokes boundary pairing `∫_{∂M} i* θ = ∫_M d₃ θ`.
2. `PalatiniActionData`: bulk 4-form Lagrangian density `L` and symplectic potential 3-form `θ`
   satisfying `d₃ θ = L`.
3. `palatini_stokes_pairing`: boundary flux `∫_{∂M} i* θ` equals bulk action `∫_M L`.
4. `boundary_gauge_shift_invariant`: gauge shifts `θ ↦ θ + d₂ α` leave boundary and bulk integrals invariant.
5. `CauchyBoundarySplitting`: boundary decomposition `∂M = Σ₊ ∪ (-Σ₋)`.
6. `on_shell_flux_conservation`: for on-shell vacuum `L = 0`, future and past Cauchy fluxes are identical:
   `∫_{Σ₊} i* θ = ∫_{Σ₋} i* θ`.
7. `flux_transfer_with_bulk_source`: Cauchy flux net difference equals bulk Palatini action.
8. `certified_palatini_stokes_synthesis`: unified certified synthesis packet.
-/

namespace InfoGeometry.Canonical.PalatiniBoundaryStokesBridge

open InfoGeometry.Canonical.EinsteinHilbertPalatiniActionBridge

variable {R : Type*} [CommRing R]
variable {Ω2 Ω3 Ω4 Ω3_bd : Type*}
variable [AddCommGroup Ω2] [Module R Ω2]
variable [AddCommGroup Ω3] [Module R Ω3]
variable [AddCommGroup Ω4] [Module R Ω4]
variable [AddCommGroup Ω3_bd] [Module R Ω3_bd]

/-- **Definition**: Stokes Boundary Differential Complex.
    Encapsulates exterior derivative stages d₂ : Ω² → Ω³, d₃ : Ω³ → Ω⁴ with d₃ ∘ d₂ = 0,
    a boundary pullback map i* : Ω³(M) → Ω³(∂M), and Stokes boundary pairing. -/
structure StokesBoundaryComplex (R : Type*) [CommRing R]
    (Ω2 Ω3 Ω4 Ω3_bd : Type*)
    [AddCommGroup Ω2] [Module R Ω2]
    [AddCommGroup Ω3] [Module R Ω3]
    [AddCommGroup Ω4] [Module R Ω4]
    [AddCommGroup Ω3_bd] [Module R Ω3_bd] where
  d2 : Ω2 →ₗ[R] Ω3
  d3 : Ω3 →ₗ[R] Ω4
  d_squared : ∀ α : Ω2, d3 (d2 α) = 0
  pullback : Ω3 →ₗ[R] Ω3_bd
  integrateBulk : Ω4 →ₗ[R] R
  integrateBoundary : Ω3_bd →ₗ[R] R
  boundary_pairing_eq : ∀ θ : Ω3, integrateBoundary (pullback θ) = integrateBulk (d3 θ)

/-- **Theorem**: Boundary Pairing of Exact Forms Vanishes (Stokes on Closed Boundaries). -/
theorem boundary_pairing_exact_vanishes
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) (α : Ω2) :
    C.integrateBoundary (C.pullback (C.d2 α)) = 0 := by
  rw [C.boundary_pairing_eq, C.d_squared, map_zero]

/-- **Theorem**: Bulk Gauge Shift Invariance under exact 2-form differentials. -/
theorem bulk_gauge_shift_invariant
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) (θ : Ω3) (α : Ω2) :
    C.integrateBulk (C.d3 (θ + C.d2 α)) = C.integrateBulk (C.d3 θ) := by
  rw [map_add, C.d_squared, add_zero]

/-- **Theorem**: Boundary Gauge Shift Invariance. -/
theorem boundary_gauge_shift_invariant
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) (θ : Ω3) (α : Ω2) :
    C.integrateBoundary (C.pullback (θ + C.d2 α)) = C.integrateBoundary (C.pullback θ) := by
  rw [C.boundary_pairing_eq, C.boundary_pairing_eq, bulk_gauge_shift_invariant]

/-- **Theorem**: Linearity of Stokes boundary integration under form addition. -/
theorem boundary_pairing_add
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) (θ₁ θ₂ : Ω3) :
    C.integrateBoundary (C.pullback (θ₁ + θ₂)) =
      C.integrateBoundary (C.pullback θ₁) + C.integrateBoundary (C.pullback θ₂) := by
  rw [map_add, map_add]

/-- **Theorem**: Linearity of Stokes boundary integration under scalar multiplication. -/
theorem boundary_pairing_smul
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) (c : R) (θ : Ω3) :
    C.integrateBoundary (C.pullback (c • θ)) = c • C.integrateBoundary (C.pullback θ) := by
  rw [map_smul, map_smul]

/-- **Definition**: Palatini Action Data on a Stokes boundary complex.
    Associates a bulk 4-form Lagrangian density L (e.g. Tr(e ∧ e ∧ R)) with a
    boundary symplectic potential 3-form θ satisfying d₃ θ = L. -/
structure PalatiniActionData
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd) where
  lagrangian : Ω4
  potential : Ω3
  field_equation : C.d3 potential = lagrangian

/-- **Definition**: Construction of PalatiniActionData from ExteriorAlgebra Palatini Lagrangian. -/
def palatiniActionDataOfExteriorAlgebra
    {V : Type*} [AddCommGroup V] [Module R V]
    (C : StokesBoundaryComplex R Ω2 Ω3 (ExteriorAlgebra R V) Ω3_bd)
    (diff : Module.End R (ExteriorAlgebra R V))
    (e : Fin 4 → ExteriorAlgebra R V)
    (omega : Fin 4 → Fin 4 → ExteriorAlgebra R V)
    (theta : Ω3)
    (h_diff : C.d3 theta = palatiniLagrangianFourForm diff e omega) :
    PalatiniActionData C := {
  lagrangian := palatiniLagrangianFourForm diff e omega
  potential := theta
  field_equation := h_diff
}

/-- **Definition**: Palatini Bulk Action Functional. -/
def palatiniBulkAction
    {C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd}
    (P : PalatiniActionData C) : R :=
  C.integrateBulk P.lagrangian

/-- **Definition**: Palatini Boundary Flux Functional. -/
def palatiniBoundaryFlux
    {C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd}
    (P : PalatiniActionData C) : R :=
  C.integrateBoundary (C.pullback P.potential)

/-- **Theorem**: Palatini-Stokes Boundary Pairing Theorem.
    The boundary flux of the symplectic potential 3-form equals the total bulk action. -/
theorem palatini_stokes_pairing
    {C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd}
    (P : PalatiniActionData C) :
    palatiniBoundaryFlux P = palatiniBulkAction P := by
  dsimp [palatiniBoundaryFlux, palatiniBulkAction]
  rw [C.boundary_pairing_eq, P.field_equation]

/-- **Definition**: Cauchy Boundary Splitting ∂M = Σ₊ ∪ (-Σ₋).
    Decomposes the total boundary integral into future and past Cauchy surface integrals. -/
structure CauchyBoundarySplitting
    (R : Type*) [CommRing R]
    (Ω3_bd : Type*) [AddCommGroup Ω3_bd] [Module R Ω3_bd]
    (integrateBoundary : Ω3_bd →ₗ[R] R) where
  integrateFuture : Ω3_bd →ₗ[R] R
  integratePast : Ω3_bd →ₗ[R] R
  boundary_split_eq : ∀ ω : Ω3_bd, integrateBoundary ω = integrateFuture ω - integratePast ω

/-- **Theorem**: On-Shell Boundary Flux Conservation.
    When the bulk Palatini Lagrangian vanishes on-shell (vacuum, L = 0), the boundary flux
    through the future Cauchy surface equals that through the past Cauchy surface. -/
theorem on_shell_flux_conservation
    {C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd}
    (P : PalatiniActionData C)
    (S : CauchyBoundarySplitting R Ω3_bd C.integrateBoundary)
    (h_on_shell : P.lagrangian = 0) :
    S.integrateFuture (C.pullback P.potential) = S.integratePast (C.pullback P.potential) := by
  have h_flux : palatiniBoundaryFlux P = 0 := by
    rw [palatini_stokes_pairing P]
    dsimp [palatiniBulkAction]
    rw [h_on_shell, map_zero]
  have h_split := S.boundary_split_eq (C.pullback P.potential)
  have h_pot : palatiniBoundaryFlux P = C.integrateBoundary (C.pullback P.potential) := rfl
  rw [← h_pot, h_flux] at h_split
  exact sub_eq_zero.mp h_split.symm

/-- **Theorem**: Cauchy Flux Transfer with Bulk Palatini Source.
    The net flux difference between future and past Cauchy surfaces equals the bulk action. -/
theorem flux_transfer_with_bulk_source
    {C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd}
    (P : PalatiniActionData C)
    (S : CauchyBoundarySplitting R Ω3_bd C.integrateBoundary) :
    S.integrateFuture (C.pullback P.potential) - S.integratePast (C.pullback P.potential) =
      palatiniBulkAction P := by
  rw [← S.boundary_split_eq]
  exact palatini_stokes_pairing P

/-- **Definition**: Certified Synthesis Package for Palatini Boundary Stokes Architecture. -/
structure CertifiedPalatiniStokesSynthesis
    (R : Type*) [CommRing R]
    (Ω2 Ω3 Ω4 Ω3_bd : Type*)
    [AddCommGroup Ω2] [Module R Ω2]
    [AddCommGroup Ω3] [Module R Ω3]
    [AddCommGroup Ω4] [Module R Ω4]
    [AddCommGroup Ω3_bd] [Module R Ω3_bd] where
  complex : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd
  palatini : PalatiniActionData complex
  splitting : CauchyBoundarySplitting R Ω3_bd complex.integrateBoundary
  stokes_pairing_identity : palatiniBoundaryFlux palatini = palatiniBulkAction palatini
  gauge_invariance_identity : ∀ α : Ω2,
    complex.integrateBoundary (complex.pullback (palatini.potential + complex.d2 α)) =
      palatiniBoundaryFlux palatini
  flux_transfer_identity :
    splitting.integrateFuture (complex.pullback palatini.potential) -
      splitting.integratePast (complex.pullback palatini.potential) =
      palatiniBulkAction palatini

/-- **Theorem**: Master Constructor for Certified Palatini-Stokes Boundary Synthesis. -/
def makeCertifiedPalatiniStokesSynthesis
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd)
    (P : PalatiniActionData C)
    (S : CauchyBoundarySplitting R Ω3_bd C.integrateBoundary) :
    CertifiedPalatiniStokesSynthesis R Ω2 Ω3 Ω4 Ω3_bd := {
  complex := C
  palatini := P
  splitting := S
  stokes_pairing_identity := palatini_stokes_pairing P
  gauge_invariance_identity := by
    intro α
    exact boundary_gauge_shift_invariant C P.potential α
  flux_transfer_identity := flux_transfer_with_bulk_source P S
}

/-- **Theorem**: Master Palatini Boundary Stokes Infrastructure Synthesis.
    Unifies:
    1. Stokes Boundary Pairing: ∫_{∂M} i* θ = ∫_M d₃ θ.
    2. Gauge Shift Invariance: ∫_{∂M} i*(θ + d₂ α) = ∫_{∂M} i* θ.
    3. Exact Boundary Vanishing: ∫_{∂M} i*(d₂ α) = 0.
    4. Palatini Action Pairing: Flux_{∂M}(θ) = Action_M(L_{Palatini}).
    5. On-Shell Cauchy Flux Conservation: ∫_{Σ₊} θ = ∫_{Σ₋} θ when L = 0.
    6. Cauchy Flux Transfer: ∫_{Σ₊} θ - ∫_{Σ₋} θ = Action_M(L). -/
theorem certified_palatini_stokes_synthesis
    (C : StokesBoundaryComplex R Ω2 Ω3 Ω4 Ω3_bd)
    (P : PalatiniActionData C)
    (S : CauchyBoundarySplitting R Ω3_bd C.integrateBoundary)
    (θ : Ω3) (α : Ω2) :
    (C.integrateBoundary (C.pullback θ) = C.integrateBulk (C.d3 θ)) ∧
    (C.integrateBoundary (C.pullback (θ + C.d2 α)) = C.integrateBoundary (C.pullback θ)) ∧
    (C.integrateBoundary (C.pullback (C.d2 α)) = 0) ∧
    (palatiniBoundaryFlux P = palatiniBulkAction P) ∧
    (P.lagrangian = 0 →
      S.integrateFuture (C.pullback P.potential) = S.integratePast (C.pullback P.potential)) ∧
    (S.integrateFuture (C.pullback P.potential) - S.integratePast (C.pullback P.potential) =
      palatiniBulkAction P) := ⟨
  C.boundary_pairing_eq θ,
  boundary_gauge_shift_invariant C θ α,
  boundary_pairing_exact_vanishes C α,
  palatini_stokes_pairing P,
  on_shell_flux_conservation P S,
  flux_transfer_with_bulk_source P S
⟩

end InfoGeometry.Canonical.PalatiniBoundaryStokesBridge
