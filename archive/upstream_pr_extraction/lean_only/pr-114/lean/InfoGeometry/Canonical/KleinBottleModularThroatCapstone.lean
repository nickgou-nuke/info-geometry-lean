import InfoGeometry.Quantum.KleinBottleModularThroat

namespace InfoGeometry.Canonical.KleinBottleModularThroatCapstone

open InfoGeometry.Quantum.KleinBottleModularThroat

theorem capstone_klein_bottle_throat_synthesis
    {R : Type*} [CommRing R]
    (z : ℂ) (N_L N_R : ℝ)
    (h_standing : N_L = N_R) (σ : ℝ) (h_throat : σ - 1 / 2 = 0)
    (Q Qbar H : R) (h_susy : anticommutator Q Qbar = 2 * H) :
    (modularInvolution (modularInvolution z) = z) ∧
    (‖z‖ = 1 ↔ ‖modularInvolution z‖ = 1) ∧
    (throatRapidity N_L N_R = 0) ∧
    (σ = 1 / 2) ∧
    (anticommutator Q Qbar = 2 * H) :=
  grand_klein_bottle_throat_synthesis z N_L N_R h_standing σ h_throat Q Qbar H h_susy

end InfoGeometry.Canonical.KleinBottleModularThroatCapstone
