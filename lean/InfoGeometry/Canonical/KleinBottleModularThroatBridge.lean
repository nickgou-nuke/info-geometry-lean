import InfoGeometry.Quantum.KleinBottleModularThroat

namespace InfoGeometry.Canonical.KleinBottleModularThroatBridge

open InfoGeometry.Quantum.KleinBottleModularThroat

theorem modular_throat_packet (z : ℂ) :
    modularInvolution (modularInvolution z) = z ∧
      (‖z‖ = 1 ↔ ‖modularInvolution z‖ = 1) :=
  ⟨modular_involution_involution z, throat_equator_invariance z⟩

theorem cayley_critical_line_packet (t : ℝ) :
    ‖cayleyTransform (1 / 2 + t * Complex.I)‖ = 1 :=
  cayley_critical_line_param t

theorem bps_center_packet (σ : ℝ) (h : BPSState 0 (σ - 1 / 2)) :
    σ = 1 / 2 :=
  bps_zero_rapidity_center σ h

end InfoGeometry.Canonical.KleinBottleModularThroatBridge
