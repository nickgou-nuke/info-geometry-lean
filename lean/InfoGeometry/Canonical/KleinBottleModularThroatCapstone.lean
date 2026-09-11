import InfoGeometry.Canonical.KleinBottleModularThroatBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.KleinBottleModularThroatCapstone

open InfoGeometry.Quantum.KleinBottleModularThroat

/-!
  Compatibility surface for the upstream capstone.  The proofs are delegated
  to the current quantum owner; this file contains no second modular model.
-/

theorem capstone_klein_bottle_throat_synthesis
    {R : Type*} [CommRing R]
    (z : ℂ) (N_L N_R : ℝ)
    (h_standing : N_L = N_R) (σ : ℝ) (h_throat : σ - 1 / 2 = 0)
    (Q Qbar H : R) (h_susy : anticommutator Q Qbar = 2 * H) :
    (modularInvolution (modularInvolution z) = z) ∧
    (‖z‖ = 1 ↔ ‖modularInvolution z‖ = 1) ∧
    (throatRapidity N_L N_R = 0) ∧
    (σ = 1 / 2) ∧
    (anticommutator Q Qbar = 2 * H) := by
  refine ⟨modular_involution_involution z, throat_equator_invariance z, ?_, ?_, h_susy⟩
  · simp [throatRapidity, h_standing]
  · linarith

end InfoGeometry.Canonical.KleinBottleModularThroatCapstone
