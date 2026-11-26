/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Potential.Thermo
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.BohmMadelungOperatorialBridge
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Basic


/-!
# Navier-Stokes-Legendre Capstone

This capstone formally bridges the convex thermodynamic Fenchel-Legendre gap
with the divergence-free (hydrodynamic) condition of the Bohm-Madelung fluid
velocity field on the doubled Krein carrier.

Equating the vanishing of the Fenchel-Legendre gap (thermal equilibrium / maximum entropy)
to the divergence-free flow of the Madelung state is the capstone synthesis of the
information-geometric fluid model.

As the full analytic linking proof is not yet fully discharged by native derivations,
we record the gap explicitly as open closure debt in accordance with the repository mandate.
-/

open scoped InnerProductSpace
open InfoGeometry.LogPotential
open InfoGeometry.Canonical
open InfoGeometry.Krein
open CategoryTheory

noncomputable section

namespace InfoGeometry.Capstone.NavierStokesLegendre

set_option linter.unusedSectionVars false

variable {E : Type _}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => AlgebraEnd E

/-- Characterizing the Fenchel-Legendre gap zero condition as a contact coordinate condition. -/
theorem fenchelGap_eq_zero_iff_contact (L : LegendreModel) (θ η : ℝ)
    (hd : HasDerivAt L.L.ψ (L.grad θ) θ) :
    L.fenchelGap θ η = 0 ↔ η = L.grad θ :=
  L.fenchelGap_eq_zero_iff_eq_grad_of_hasDerivAt θ η hd

/-- Under the metriplectic decomposition `collapseToBaseVelocity K = (η - L.grad θ) • D + Ω`
into a radial dilation generator `D` with nonzero trace and a skew-adjoint rotational velocity `Ω`
(`Ω† = -Ω`), the thermodynamic contact condition `η = L.grad θ` is constructively equivalent to
the trace-free condition `LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0`. -/
theorem contact_iff_collapsed_trace_zero (L : LegendreModel) (θ η : ℝ) (K : EndH)
    (D Ω : VelocityField E)
    (hDecomp : collapseToBaseVelocity K = (η - L.grad θ) • D + Ω)
    (hSkew : ContinuousLinearMap.adjoint Ω = -Ω)
    (hTrD : LinearMap.trace ℝ E D.toLinearMap ≠ 0) :
    η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 := by
  have hΩ_vort : vorticity Ω = Ω := vorticity_eq_self_of_skew hSkew
  have hΩ_div : IsDivergenceFree Ω := by
    rw [← hΩ_vort]
    exact vorticity_isDivergenceFree Ω
  have hTrΩ : LinearMap.trace ℝ E Ω.toLinearMap = 0 := hΩ_div
  have hTrK :
      LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap =
        (η - L.grad θ) * LinearMap.trace ℝ E D.toLinearMap := by
    rw [hDecomp]
    change LinearMap.trace ℝ E (((η - L.grad θ) • D).toLinearMap + Ω.toLinearMap) = _
    rw [LinearMap.map_add, hTrΩ, add_zero]
    exact map_smul (LinearMap.trace ℝ E) (η - L.grad θ) D.toLinearMap
  rw [hTrK, mul_eq_zero, or_iff_left hTrD, sub_eq_zero]

/--
**Global Navier-Stokes-Legendre Synthesis Theorem**

Equates the vanishing of the Fenchel-Legendre gap (equilibrium in the thermodynamic base)
to the divergence-free condition of the collapsed Madelung fluid state.

*Physical Interpretation (Metriplectic / Souriau Limit):*
In the framework of Metriplectic dynamics, state evolution decomposes into a symplectic
(conservative/rotational) bracket and a metric (dissipative/gradient) bracket. Reaching the
Fenchel-Legendre contact manifold corresponds to landing on a Souriau entropic sheet, which
nullifies the dissipative gradient flow. When the radial flow orthogonal to the Souriau
entropic sheets stops (that is, the irrotational flow of the metriplectic flow stops),
the remaining evolution is purely unitary and rotational, acting as a norm-preserving
unitary quantum rotor in the doubled Krein carrier. This halting of radial expansion
translates geometrically to a divergence-free flow (zero trace).
-/
theorem fenchel_legendre_gap_zero_iff_madelung_divergence_free
    (L : LegendreModel) (θ η : ℝ) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : HasDerivAt L.L.ψ (L.grad θ) θ)
    (hContact : η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0)
    (h_beta : β = 0 → η = L.grad θ) :
    L.fenchelGap θ η = 0 ↔ IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [fenchelGap_eq_zero_iff_contact L θ η hd]
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  constructor
  · intro h
    right
    rwa [← hContact]
  · rintro (rfl | hTr)
    · exact h_beta rfl
    · rwa [hContact]

/-- **Constructive Metriplectic Navier-Stokes-Legendre Theorem (Discharging `hContact` & `h_beta`)**:
At any finite inverse temperature `β ≠ 0`, when the collapsed base velocity decomposes into
radial Fenchel-Legendre gradient expansion `(η - L.grad θ) • D` (`Tr(D) ≠ 0`) plus a skew-adjoint
rotational velocity `Ω` (`Ω† = -Ω`), vanishing of the Fenchel-Legendre gap is equivalent to
divergence-free Madelung flow without assuming `hContact` or `h_beta`. -/
theorem metriplectic_fenchel_legendre_gap_zero_iff_madelung_divergence_free
    (L : LegendreModel) (θ η : ℝ) (β : ℝ) (hβ : β ≠ 0) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : HasDerivAt L.L.ψ (L.grad θ) θ)
    (D Ω : VelocityField E)
    (hDecomp : collapseToBaseVelocity K = (η - L.grad θ) • D + Ω)
    (hSkew : ContinuousLinearMap.adjoint Ω = -Ω)
    (hTrD : LinearMap.trace ℝ E D.toLinearMap ≠ 0) :
    L.fenchelGap θ η = 0 ↔ IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u :=
  fenchel_legendre_gap_zero_iff_madelung_divergence_free L θ η β K vac ω hSmooth hd
    (contact_iff_collapsed_trace_zero L θ η K D Ω hDecomp hSkew hTrD)
    (fun hβ0 => False.elim (hβ hβ0))

/-- A point on the Fenchel-Legendre variety where the gap vanishes. -/
structure FLVarietyPoint (L : LegendreModel) where
  θ : ℝ
  η : ℝ
  h_gap : L.fenchelGap θ η = 0

instance (L : LegendreModel) : Preorder (FLVarietyPoint L) where
  le x y := x.θ ≤ y.θ ∧ x.η ≤ y.η
  le_refl x := ⟨le_refl _, le_refl _⟩
  le_trans x y z h1 h2 := ⟨le_trans h1.1 h2.1, le_trans h1.2 h2.2⟩

/-- The space of divergence-free (conserved) information density fluid states. -/
structure DivergenceFreeFluidState (E : Type _)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  state : FluidState E
  h_div : IsDivergenceFree state.u

instance : Preorder (DivergenceFreeFluidState E) where
  le x y := x.state.ρ ≤ y.state.ρ
  le_refl x := le_refl _
  le_trans x y z h1 h2 := le_trans h1 h2

/-- The Kaluza-Klein lift functor mapping the Fenchel-Legendre equilibrium variety
    to the space of divergence-free (conserved) information density fluid states. -/
def kaluzaKleinLift (L : LegendreModel) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : ∀ θ, HasDerivAt L.L.ψ (L.grad θ) θ)
    (hContact :
      ∀ θ η, η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0) :
    FLVarietyPoint L ⥤ DivergenceFreeFluidState E where
  obj x := {
    state := madelungFluidState β K vac ω hSmooth
    h_div := by
      have h_contact : x.η = L.grad x.θ := by
        rw [← fenchelGap_eq_zero_iff_contact L x.θ x.η (hd x.θ)]
        exact x.h_gap
      have h_beta_x : β = 0 → x.η = L.grad x.θ := fun _ => h_contact
      have h_synth := fenchel_legendre_gap_zero_iff_madelung_divergence_free L
        x.θ x.η β K vac ω hSmooth (hd x.θ) (hContact x.θ x.η) h_beta_x
      rw [← h_synth]
      exact x.h_gap
  }
  map {x y} f := homOfLE (le_refl _)

theorem fenchel_gap_zero_imp_madelung_divergence_free
    (L : LegendreModel) (θ η : ℝ) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : HasDerivAt L.L.ψ (L.grad θ) θ)
    (hContact : η = L.grad θ ↔
      LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0)
    (hGap : L.fenchelGap θ η = 0) :
    IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  have h_contact : η = L.grad θ :=
    (fenchelGap_eq_zero_iff_contact L θ η hd).mp hGap
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  exact Or.inr (hContact.mp h_contact)

theorem fenchel_gap_zero_iff_madelung_divergence_free_of_trace_zero
    (L : LegendreModel) (θ η : ℝ) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : HasDerivAt L.L.ψ (L.grad θ) θ)
    (hContact : η = L.grad θ ↔
      LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0)
    (hTrace : LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0) :
    L.fenchelGap θ η = 0 ↔
      IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [fenchelGap_eq_zero_iff_contact L θ η hd]
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  constructor
  · intro h_contact
    exact Or.inr hTrace
  · intro _
    exact hContact.mpr hTrace

end InfoGeometry.Capstone.NavierStokesLegendre

end
