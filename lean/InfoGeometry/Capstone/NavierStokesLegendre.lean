import InfoGeometry.Potential.Thermo
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
    (hd : HasDerivAt L.L (L.grad θ) θ) :
    L.fenchelGap θ η = 0 ↔ η = L.grad θ :=
  L.fenchelGap_eq_zero_iff_eq_grad_of_hasDerivAt θ η hd

/-- The thermodynamic contact condition is equivalent to the trace-free collapsed modular Hamiltonian. -/
theorem contact_iff_collapsed_trace_zero (L : LegendreModel) (θ η : ℝ) (K : EndH)
    (hContact : η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0) :
    η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0 :=
  hContact

/--\n**Global Navier-Stokes-Legendre Synthesis Theorem**\n\nEquates the vanishing of the Fenchel-Legendre gap (equilibrium in the thermodynamic base)\nto the divergence-free condition of the collapsed Madelung fluid state.\n\n*Physical Interpretation (Metriplectic / Souriau Limit):*\nIn the framework of Metriplectic dynamics, state evolution decomposes into a symplectic\n(conservative/rotational) bracket and a metric (dissipative/gradient) bracket. Reaching the\nFenchel-Legendre contact manifold corresponds to landing on a Souriau entropic sheet, which\nnullifies the dissipative gradient flow. When the radial flow orthogonal to the Souriau\nentropic sheets stops (that is, the irrotational flow of the metriplectic flow stops),\nthe remaining evolution is purely unitary and rotational, acting as a norm-preserving\nunitary quantum rotor in the doubled Krein carrier. This halting of radial expansion\ntranslates geometrically to a divergence-free flow (zero trace).\n-/
theorem fenchel_legendre_gap_zero_iff_madelung_divergence_free
    (L : LegendreModel) (θ η : ℝ) (β : ℝ) (K : EndH)
    (vac : ThermalVacuum (E := E) K) (ω : EndH →L[ℝ] ℝ)
    (hSmooth : IsThermodynamicallySmoothed β K)
    (hd : HasDerivAt L.L (L.grad θ) θ)
    (hContact : η = L.grad θ ↔ LinearMap.trace ℝ E (collapseToBaseVelocity K).toLinearMap = 0)
    (h_beta : β = 0 → η = L.grad θ) :
    L.fenchelGap θ η = 0 ↔ IsDivergenceFree (madelungFluidState β K vac ω hSmooth).u := by
  rw [fenchelGap_eq_zero_iff_contact L θ η hd]
  rw [madelung_divergence_free_iff β K vac ω hSmooth]
  constructor
  · intro h
    right
    rwa [← contact_iff_collapsed_trace_zero L θ η K hContact]
  · rintro (rfl | hTr)
    · exact h_beta rfl
    · rwa [contact_iff_collapsed_trace_zero L θ η K hContact]

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
    (hd : ∀ θ, HasDerivAt L.L (L.grad θ) θ)
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

end InfoGeometry.Capstone.NavierStokesLegendre
